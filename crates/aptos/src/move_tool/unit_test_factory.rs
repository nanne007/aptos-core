use aptos_framework::natives::aggregator_natives::NativeAggregatorContext;
use aptos_framework::natives::code::NativeCodeContext;
use aptos_framework::natives::cryptography::algebra::AlgebraContext;
use aptos_framework::natives::cryptography::ristretto255_point::NativeRistrettoPointContext;
use aptos_framework::natives::event::NativeEventContext;
use aptos_framework::natives::randomness::RandomnessContext;
use aptos_framework::natives::transaction_context::NativeTransactionContext;

use aptos_framework::extended_checks::run_extended_checks;
use aptos_rest_client::AptosBaseUrl;
use aptos_table_natives::{NativeTableContext, TableChangeSet};
use aptos_transaction_simulation::{DeltaStateStore, EitherStateView, EmptyStateView, SimulationStateStore, GENESIS_CHANGE_SET_HEAD};
use aptos_types::chain_id::ChainId;
use aptos_types::state_store::state_key::StateKey;
use aptos_types::vm::module_metadata::{RuntimeModuleMetadataV1, APTOS_METADATA_KEY, APTOS_METADATA_KEY_V1, METADATA_V1_MIN_FILE_FORMAT_VERSION};
use aptos_validator_interface::{DebuggerStateView, RestDebuggerInterface};
use aptos_vm::data_cache::AsMoveResolver;
use aptos_vm_environment::environment::AptosEnvironment;
use aptos_vm_types::module_and_script_storage::AsAptosCodeStorage;
use aptos_vm_types::resolver::TResourceView;
use bytes::Bytes;
use itertools::Itertools;
use legacy_move_compiler::unit_test::{ModuleTestPlan, NamedOrBytecodeModule, TestCase, TestPlan};
use move_binary_format::errors::PartialVMError;
use move_binary_format::CompiledModule;
use move_bytecode_utils::compiled_module_viewer::CompiledModuleView;
use move_core_types::effects::Op;
use move_core_types::language_storage::ModuleId;
use move_core_types::metadata::Metadata;
use move_core_types::value::MoveTypeLayout;
use move_core_types::{effects::ChangeSet, value::MoveValue};
use move_package::{BuildConfig, ModelConfig};
use move_table_extension::{TableHandle, TableResolver};
use move_unit_test::test_reporter::{AsModuleStorage, AsResourceResolver, TestRunInfo, UnitTestFactory};
use move_vm_runtime::{native_extensions::NativeContextExtensions, AsFunctionValueExtension, ModuleStorage};
use move_vm_types::{gas::UnmeteredGasMeter, resolver::ResourceResolver};
use std::collections::BTreeMap;
use std::{fmt, path::PathBuf, str::FromStr, sync::Arc};
use tokio::runtime::Handle;
use url::Url;

type FakeExecutorStateStore = DeltaStateStore<EitherStateView<EmptyStateView, DebuggerStateView>>;
const APTOS_REST_API_KEY: &str = "APTOS_REST_API_KEY";

pub(crate) struct AptosUnitTestFactory {
    package_path: PathBuf,
    module_metadatas: BTreeMap<ModuleId, RuntimeModuleMetadataV1>,
    rt_handle: Handle,
}


impl UnitTestFactory for AptosUnitTestFactory {
    type GasMeter = UnmeteredGasMeter;
    type Resolver = StateStore;
    fn new_gas_meter(&self) -> Self::GasMeter {
        UnmeteredGasMeter
    }

    fn finalize_test_run_info(
        &self,
        resolver: &Self::Resolver,
        change_set: &ChangeSet,
        extensions: &mut NativeContextExtensions,
        _gas_meter: Self::GasMeter,
        mut test_run_info: TestRunInfo,
    ) -> TestRunInfo {
        let table_cs = extensions.remove::<NativeTableContext>().into_change_set(&resolver.as_module_storage().as_function_value_extension()).ok();

        test_run_info.storage_state = print_resources_and_extensions(
            change_set,
            &table_cs,
            resolver,
        ).ok();
        test_run_info
    }
    fn resolver(
        &self,
        test_plan: &TestPlan,
        module_test_plan: &ModuleTestPlan,
        test: &TestCase,
    ) -> StateStore {
        self.setup_store(test_plan, module_test_plan, test)
    }

    fn extensions<'a>(&'a self, resolver: &'a Self::Resolver) -> NativeContextExtensions<'a> {
        let mut exts = NativeContextExtensions::default();
        use aptos_framework::natives::object::NativeObjectContext;
        exts.add(NativeTableContext::new([0u8; 32], resolver));
        exts.add(NativeCodeContext::new());
        exts.add(NativeTransactionContext::new(
            vec![1],
            vec![1],
            ChainId::test().id(),
            None,
        ));
        exts.add(NativeAggregatorContext::new(
            [0; 32], &resolver.inner,
            false,
            &resolver.inner,
        ));
        exts.add(NativeRistrettoPointContext::new());
        exts.add(AlgebraContext::new());
        exts.add(NativeEventContext::default());
        exts.add(NativeObjectContext::default());

        let mut randomness_ctx = RandomnessContext::new();
        randomness_ctx.mark_unbiasable();
        exts.add(randomness_ctx);
        exts
    }
}


impl AptosUnitTestFactory {
    pub fn new(
        package_path: PathBuf,
        build_config: BuildConfig,
    ) -> anyhow::Result<Self> {
        let model_config = ModelConfig {
            all_files_as_targets: true,
            target_filter: None,
            compiler_version: build_config.compiler_config
                .compiler_version
                .unwrap_or_default(),
            language_version: build_config.compiler_config.language_version.unwrap_or_default(),
        };
        let global_env = build_config.move_model_for_package(&package_path, model_config)?;
        let module_metadatas = run_extended_checks(&global_env);

        Ok(Self {
            package_path,
            module_metadatas,
            rt_handle: Handle::current(),
        })
    }

    fn setup_store(
        &self,
        test_plan: &TestPlan,
        module_test_plan: &ModuleTestPlan,
        test: &TestCase,
    ) -> StateStore {
        // remote client need to spawn an async task to run the setup
        let store = self.rt_handle.block_on(async {
            setup_store(test_plan, module_test_plan, test)
        });

        let modules = test_plan.module_info.values().map(|info| match info {
            NamedOrBytecodeModule::Named(named_compiled_module) => {
                &named_compiled_module.module
            },
            NamedOrBytecodeModule::Bytecode(compiled_module) => compiled_module,
        });

        for m in modules {
            let mut m = m.clone();
            inject_runtime_metadata(&mut m, &self.module_metadatas, None);
            store.inner
                .add_module(&m)
                .expect("Failed to add module to state store during unit test setup");
        }

        store
    }
}
fn setup_store(
    test_plan: &TestPlan,
    module_test_plan: &ModuleTestPlan,
    test: &TestCase,
) -> StateStore {
    let e2e_test = test.test_name.as_str().starts_with("e2e");

    let store = if e2e_test { create_store(test_plan, module_test_plan, test) } else {
        let state_store = DeltaStateStore::new_with_base(EitherStateView::Left(EmptyStateView));
        state_store.set_chain_id(ChainId::test()).unwrap();

        state_store.apply_write_set(GENESIS_CHANGE_SET_HEAD.write_set()).unwrap();
        state_store
    };

    StateStore {
        runtime_env: AptosEnvironment::new(&store),
        inner: store,
    }
}
fn create_store(
    test_plan: &TestPlan,
    module_test_plan: &ModuleTestPlan,
    test: &TestCase,
) -> FakeExecutorStateStore {
    let txn_id = test.arguments.last().unwrap(); // TODO: handle this more gracefully
    let txn_id = if let MoveValue::U64(tx_id) = txn_id {
        *tx_id
    } else {
        panic!("Expected the last argument of the test case to be a transaction ID of type MoveValue::U64");
    };
    let network_url = test.arguments.iter().rev().nth(1).unwrap(); // TODO: handle this more gracefully
    let network_url = if let MoveValue::Vector(url) = network_url {
        let url = MoveValue::vec_to_vec_u8(url.clone()).expect("Expected the second to last argument of the test case to be a network URL of type vector<u8>");
        String::from_utf8(url).expect("Invalid UTF-8 in network URL")
    } else {
        panic!("Expected the second to last argument of the test case to be a network URL of type MoveValue::String");
    };
    let aptos_base_url = if network_url == "mainnet" {
        AptosBaseUrl::Mainnet
    } else if network_url == "testnet" {
        AptosBaseUrl::Testnet
    } else if network_url == "devnet" {
        AptosBaseUrl::Devnet
    } else {
        AptosBaseUrl::Custom(
            Url::from_str(&network_url).expect("Invalid URL in network URL argument"),
        )
    };

    let mut builder = aptos_rest_client::Client::builder(aptos_base_url);
    let api_key = std::env::var(APTOS_REST_API_KEY)
        .ok()
        .map(|api_key| api_key.trim().to_string())
        .and_then(|api_key| {
            if api_key.is_empty() {
                None
            } else {
                Some(api_key)
            }
        });


    if let Some(api_key) = api_key {
        builder = builder
            .api_key(&api_key)
            .expect("failed to configure API key")
    }
    let rest_client = builder.build();

    let debugger = Arc::new(RestDebuggerInterface::new(rest_client));
    let debugger_state_view = DebuggerStateView::new(debugger, txn_id);
    let state_store = DeltaStateStore::new_with_base(EitherStateView::<EmptyStateView, _>::Right(
        debugger_state_view,
    ));
    state_store
}

pub struct StateStore {
    inner: FakeExecutorStateStore,
    runtime_env: AptosEnvironment,
}
//
// impl ModuleBytesStorage for StateStore {
//     fn fetch_module_bytes(
//         &self,
//         address: &AccountAddress,
//         module_name: &IdentStr,
//     ) -> VMResult<Option<bytes::Bytes>> {
//         let state_key = StateKey::module(address, module_name);
//         self.inner
//             .get_state_value_bytes(&state_key)
//             .map_err(|e| module_storage_error!(address, module_name, e))
//     }
// }
//
// impl WithRuntimeEnvironment for StateStore {
//     fn runtime_environment(&self) -> &RuntimeEnvironment {
//         &self.runtime_env.runtime_environment()
//     }
// }

impl AsModuleStorage for StateStore {
    fn as_module_storage(&self) -> impl ModuleStorage {
        self.inner.as_aptos_code_storage(&self.runtime_env)
    }
}

impl AsResourceResolver for StateStore {
    fn as_resource_resolver(&self) -> impl ResourceResolver {
        self.inner.as_move_resolver()
    }
}

impl TableResolver for StateStore {
    fn resolve_table_entry_bytes_with_layout(&self, handle: &TableHandle, key: &[u8], maybe_layout: Option<&MoveTypeLayout>) -> Result<Option<Bytes>, PartialVMError> {
        let state_key = StateKey::table_item(&(*handle).into(), key);
        self.inner
            .get_resource_bytes(&state_key, maybe_layout)
    }
}

impl CompiledModuleView for &StateStore {
    type Item = CompiledModule;

    fn view_compiled_module(&self, id: &ModuleId) -> anyhow::Result<Option<Self::Item>> {
        self.inner.get_module(id)
    }
}

/// Print the updates to storage represented by `cs` in the context of the starting storage state
/// `storage`.
fn print_resources_and_extensions(
    cs: &ChangeSet,
    table_change_set: &Option<TableChangeSet>,
    storage: &StateStore,
) -> anyhow::Result<String> {
    let mut buf = String::new();

    print_cs(&mut buf, cs, storage)?;
    if let Some(cs) = table_change_set {
        print_table_cs(&mut buf, cs);
    }
    Ok(buf)
}

fn print_cs<W: fmt::Write>(
    buf: &mut W,
    cs: &ChangeSet,
    module_view: impl CompiledModuleView,
) -> anyhow::Result<()> {
    let annotator = move_resource_viewer::MoveValueAnnotator::new(module_view);
    for (account_addr, account_state) in cs.accounts() {
        writeln!(buf, "0x{}:", account_addr.short_str_lossless())?;

        for (tag, resource_op) in account_state.resources() {
            if let Op::New(resource) | Op::Modify(resource) = resource_op {
                writeln!(
                    buf,
                    "\t{}",
                    format!("=> {}", annotator.view_resource(tag, resource)?).replace('\n', "\n\t")
                )?;
            }
        }
    }
    Ok(())
}

fn print_table_cs<W: fmt::Write>(
    w: &mut W,
    cs: &TableChangeSet,
) {
    if !cs.new_tables.is_empty() {
        writeln!(
            w,
            "new tables {}",
            cs.new_tables
                .iter()
                .map(|(k, v)| format!("{}<{},{}>", k, v.key_type, v.value_type))
                .join(", ")
        )
            .unwrap();
    }
    if !cs.removed_tables.is_empty() {
        writeln!(
            w,
            "removed tables {}",
            cs.removed_tables.iter().map(|h| h.to_string()).join(", ")
        )
            .unwrap();
    }
    for (h, c) in &cs.changes {
        writeln!(w, "for {}", h).unwrap();
        for (k, v) in &c.entries {
            writeln!(w, "  {:X?} := {:X?}", k, v).unwrap();
        }
    }
}


fn inject_runtime_metadata(
    module: &mut CompiledModule,
    metadata: &BTreeMap<ModuleId, RuntimeModuleMetadataV1>,
    bytecode_version: Option<u32>,
) {
    if let Some(module_metadata) = metadata.get(&module.self_id()) {
        if !module_metadata.is_empty() {
            if bytecode_version.unwrap_or(METADATA_V1_MIN_FILE_FORMAT_VERSION)
                >= METADATA_V1_MIN_FILE_FORMAT_VERSION
            {
                let serialized_metadata = bcs::to_bytes(&module_metadata)
                    .expect("BCS for RuntimeModuleMetadata");
                module.metadata.push(Metadata {
                    key: APTOS_METADATA_KEY_V1.to_vec(),
                    value: serialized_metadata,
                });
            } else {
                let serialized_metadata =
                    bcs::to_bytes(&module_metadata.clone().downgrade())
                        .expect("BCS for RuntimeModuleMetadata");
                module.metadata.push(Metadata {
                    key: APTOS_METADATA_KEY.to_vec(),
                    value: serialized_metadata,
                });
            }
        }
    }
}


