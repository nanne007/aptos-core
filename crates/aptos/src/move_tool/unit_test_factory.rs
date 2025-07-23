use crate::common::utils::chain_id;
use crate::move_tool::unit_test_factory::fork_attributes::{
    construct_fork_plan, ForkInfo, ModuleTestForkPlan,
};
use aptos_framework::{
    extended_checks::run_extended_checks,
    natives::{
        aggregator_natives::NativeAggregatorContext,
        code::NativeCodeContext,
        cryptography::{algebra::AlgebraContext, ristretto255_point::NativeRistrettoPointContext},
        event::NativeEventContext,
        randomness::RandomnessContext,
        transaction_context::NativeTransactionContext,
    },
};
use aptos_rest_client::AptosBaseUrl;
use aptos_table_natives::{NativeTableContext, TableChangeSet};
use aptos_transaction_simulation::{
    DeltaStateStore, EitherStateView, EmptyStateView, SimulationStateStore, GENESIS_CHANGE_SET_HEAD,
};
use aptos_types::state_store::errors::StateViewError;
use aptos_types::state_store::state_storage_usage::StateStorageUsage;
use aptos_types::state_store::state_value::StateValue;
use aptos_types::state_store::{StateViewResult, TStateView};
use aptos_types::transaction::user_transaction_context::UserTransactionContext;
use aptos_types::{
    chain_id::ChainId,
    state_store::state_key::StateKey,
    vm::module_metadata::{
        RuntimeModuleMetadataV1, APTOS_METADATA_KEY, APTOS_METADATA_KEY_V1,
        METADATA_V1_MIN_FILE_FORMAT_VERSION,
    },
};
use aptos_validator_interface::{AptosValidatorInterface, DebuggerStateView, RestDebuggerInterface};
use aptos_vm::data_cache::AsMoveResolver;
use aptos_vm_environment::environment::AptosEnvironment;
use aptos_vm_types::{module_and_script_storage::AsAptosCodeStorage, resolver::TResourceView};
use bytes::Bytes;
use itertools::Itertools;
use legacy_move_compiler::unit_test::{ModuleTestPlan, NamedOrBytecodeModule, TestCase, TestPlan};
use move_binary_format::access::ModuleAccess;
use move_binary_format::file_format::StructFieldInformation;
use move_binary_format::{errors::PartialVMError, CompiledModule};
use move_bytecode_utils::compiled_module_viewer::CompiledModuleView;
use move_core_types::account_address::AccountAddress;
use move_core_types::language_storage::CORE_CODE_ADDRESS;
use move_core_types::{
    effects::{ChangeSet, Op},
    language_storage::ModuleId,
    metadata::Metadata,
    value::MoveTypeLayout,
};
use move_package::{BuildConfig, ModelConfig};
use move_table_extension::{TableHandle, TableResolver};
use move_unit_test::test_reporter::{
    AsModuleStorage, AsResourceResolver, TestRunInfo, UnitTestFactory,
};
use move_vm_runtime::{
    native_extensions::NativeContextExtensions, AsFunctionValueExtension, ModuleStorage,
};
use move_vm_types::{gas::UnmeteredGasMeter, resolver::ResourceResolver};
use serde::Serialize;
use std::{collections::BTreeMap, fmt, path::PathBuf, str::FromStr, sync::Arc};
use tokio::runtime::Handle;
use url::Url;

type FakeExecutorStateStore = DeltaStateStore<EitherStateView<EmptyStateView, CachedRemoteStateView<DebuggerStateView>>>;
const APTOS_REST_API_KEY: &str = "APTOS_REST_API_KEY";

const CACHE_DIR: &str = "cache";
pub(crate) struct AptosUnitTestFactory {
    package_path: PathBuf,
    module_metadatas: BTreeMap<ModuleId, RuntimeModuleMetadataV1>,
    fork_tests: BTreeMap<ModuleId, ModuleTestForkPlan>,
    rt_handle: Handle,
}
impl AptosUnitTestFactory {
    pub fn new(package_path: PathBuf, build_config: BuildConfig) -> anyhow::Result<Self> {
        let model_config = ModelConfig {
            all_files_as_targets: true,
            target_filter: None,
            compiler_version: build_config
                .compiler_config
                .compiler_version
                .unwrap_or_default(),
            language_version: build_config
                .compiler_config
                .language_version
                .unwrap_or_default(),
        };
        let global_env = build_config.move_model_for_package(&package_path, model_config)?;
        let module_metadatas = run_extended_checks(&global_env);
        let fork_plans = construct_fork_plan(&global_env, None);
        Ok(Self {
            package_path,
            module_metadatas,
            fork_tests: fork_plans,
            rt_handle: Handle::current(),
        })
    }

    fn setup_store(
        &self,
        test_plan: &TestPlan,
        module_test_plan: &ModuleTestPlan,
        test: &TestCase,
    ) -> StateStore {
        let test_fork_info = self
            .fork_tests
            .get(&module_test_plan.module_id)
            .and_then(|m| m.infos.get(&test.test_name))
            .cloned();

        // remote client need to spawn an async task to run the setup
        let store = self
            .rt_handle
            .block_on(setup_store(self.package_path.clone(), test_plan, module_test_plan, test, test_fork_info));

        let modules = test_plan.module_info.values().map(|info| match info {
            NamedOrBytecodeModule::Named(named_compiled_module) => &named_compiled_module.module,
            NamedOrBytecodeModule::Bytecode(compiled_module) => compiled_module,
        });

        for m in modules {
            let mut m = m.clone();

            let contain_native_func = m.function_defs().iter().any(|f| f.is_native());
            let contain_native_struct = m.struct_defs().iter().any(|s| matches!(s.field_information, StructFieldInformation::Native));
            let is_core_module = m.self_id().address() == &CORE_CODE_ADDRESS;

            // skip override modules that have native functions or structs
            if !is_core_module && (contain_native_func || contain_native_struct) {
                continue;
            }
            inject_runtime_metadata(&mut m, &self.module_metadatas, None);
            store
                .inner
                .add_module(&m)
                .expect("Failed to add module to state store during unit test setup");
        }

        store
    }
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
        let table_cs = extensions
            .remove::<NativeTableContext>()
            .into_change_set(&resolver.as_module_storage().as_function_value_extension())
            .ok();

        test_run_info.storage_state =
            print_resources_and_extensions(change_set, &table_cs, resolver).ok();
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
            vec![0],
            vec![1],
            resolver.inner.get_chain_id().unwrap().id(),
            Some(UserTransactionContext::new(
                AccountAddress::ZERO,
                vec![],
                AccountAddress::ZERO,
                0,
                0,
                resolver.inner.get_chain_id().unwrap().id(),
                None,
                None,
            )),
        ));
        exts.add(NativeAggregatorContext::new(
            [0; 32],
            &resolver.inner,
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

async fn setup_store(
    package_path: PathBuf,
    test_plan: &TestPlan,
    module_test_plan: &ModuleTestPlan,
    test: &TestCase,
    fork_info: Option<ForkInfo>,
) -> StateStore {
    let store = if let Some(info) = fork_info {
        create_store(package_path, test_plan, module_test_plan, test, info).await
    } else {
        let state_store = DeltaStateStore::new_with_base(EitherStateView::Left(EmptyStateView));
        state_store.set_chain_id(ChainId::test()).unwrap();

        state_store
            .apply_write_set(GENESIS_CHANGE_SET_HEAD.write_set())
            .unwrap();
        state_store
    };

    StateStore {
        runtime_env: AptosEnvironment::new(&store),
        inner: store,
    }
}
async fn create_store(
    package_path: PathBuf,
    _test_plan: &TestPlan,
    _module_test_plan: &ModuleTestPlan,
    _test: &TestCase,
    fork_info: ForkInfo,
) -> FakeExecutorStateStore {
    let network_url = fork_info.network.unwrap_or("testnet".to_string());

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

    let chain_id = chain_id(&rest_client).await.unwrap();
    let debugger = Arc::new(RestDebuggerInterface::new(rest_client));
    let version = match fork_info.version {
        Some(v) => v,
        None => debugger.get_latest_ledger_info_version().await.unwrap()
    };
    let debugger_state_view = DebuggerStateView::new(debugger, version);
    let cache_dir = package_path.join(CACHE_DIR).join(chain_id.id().to_string()).join(version.to_string());
    let state_view = CachedRemoteStateView {
        cache: LocalFileCache::new(cache_dir),
        state_view: debugger_state_view,
    };

    let state_store = DeltaStateStore::new_with_base(EitherStateView::<EmptyStateView, _>::Right(
        state_view,
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
    fn resolve_table_entry_bytes_with_layout(
        &self,
        handle: &TableHandle,
        key: &[u8],
        maybe_layout: Option<&MoveTypeLayout>,
    ) -> Result<Option<Bytes>, PartialVMError> {
        let state_key = StateKey::table_item(&(*handle).into(), key);
        self.inner.get_resource_bytes(&state_key, maybe_layout)
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

fn print_table_cs<W: fmt::Write>(w: &mut W, cs: &TableChangeSet) {
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
                let serialized_metadata =
                    bcs::to_bytes(&module_metadata).expect("BCS for RuntimeModuleMetadata");
                module.metadata.push(Metadata {
                    key: APTOS_METADATA_KEY_V1.to_vec(),
                    value: serialized_metadata,
                });
            } else {
                let serialized_metadata = bcs::to_bytes(&module_metadata.clone().downgrade())
                    .expect("BCS for RuntimeModuleMetadata");
                module.metadata.push(Metadata {
                    key: APTOS_METADATA_KEY.to_vec(),
                    value: serialized_metadata,
                });
            }
        }
    }
}

pub(crate) mod fork_attributes {
    use legacy_move_compiler::shared::known_attributes::TestingAttribute;
    use move_command_line_common::{address::NumericalAddress, parser::NumberFormat};
    use move_compiler_v2::plan_builder::convert_constant_value_u64_constant_or_value;
    use move_core_types::{
        account_address::AccountAddress, identifier::Identifier, language_storage::ModuleId
        ,
    };
    use move_model::ast::ModuleName;
    use move_model::{
        ast::{Address, Attribute, AttributeValue, Value},
        model::{FunctionEnv, GlobalEnv, ModuleEnv},
        symbol::Symbol,
    };
    use std::collections::BTreeMap;

    pub const FORK: &str = "fork";
    pub const FORK_NETWORK: &str = "network";
    pub const FORK_VERSION: &str = "version";

    #[derive(Default, Debug, Clone)]
    pub(super) struct ForkInfo {
        pub(super) network: Option<String>,
        pub(super) version: Option<u64>,
    }
    #[derive(Debug)]
    pub(super) struct ModuleTestForkPlan {
        pub(super) module_id: ModuleId,
        pub(super) infos: BTreeMap<String, ForkInfo>,
    }
    impl ModuleTestForkPlan {
        pub fn new(
            addr: &NumericalAddress,
            module_name: &str,
            infos: BTreeMap<String, ForkInfo>,
        ) -> Self {
            let addr = AccountAddress::new((*addr).into_bytes());
            let name = Identifier::new(module_name.to_owned()).unwrap();
            let module_id = ModuleId::new(addr, name);
            ModuleTestForkPlan { module_id, infos }
        }
    }
    pub(super) fn construct_fork_plan(
        env: &GlobalEnv,
        _package_filter: Option<Symbol>,
    ) -> BTreeMap<ModuleId, ModuleTestForkPlan> {
        env.get_modules()
            .filter_map(|m| construct_module_test_fork_attributes(env, m))
            .map(|p| (p.module_id.clone(), p))
            .collect()
    }

    fn construct_module_test_fork_attributes(
        env: &GlobalEnv,
        module_env: ModuleEnv,
    ) -> Option<ModuleTestForkPlan> {
        let fork_infos: BTreeMap<_, _> = module_env
            .get_functions()
            .filter_map(|func| {
                let func_name = func.get_name_str();
                build_fork_info(env, &module_env, func).map(|info| (func_name, info))
            })
            .collect();
        let module_id = module_env.get_identifier();
        if fork_infos.is_empty() {
            None
        } else {
            let module_name = module_env.get_name();
            let addr = module_name.addr();
            let name_sym = module_name.name();
            let name_str = env.symbol_pool().string(name_sym).to_string();
            if let Some(module_identifier) = module_id {
                let name_id =
                    Identifier::new(name_str.clone()).expect("name is valid for identifier");
                assert!(name_id == module_identifier);
            }
            let optional_num_addr: Option<move_core_types::account_address::AccountAddress> =
                match addr {
                    Address::Numerical(num_addr) => Some(*num_addr),
                    Address::Symbolic(sym) => env.resolve_address_alias(*sym),
                };
            optional_num_addr.map(|addr_bytes| {
                ModuleTestForkPlan::new(
                    &NumericalAddress::new(*addr_bytes, NumberFormat::Hex),
                    &name_str,
                    fork_infos,
                )
            })
        }
    }
    fn build_fork_info(
        env: &GlobalEnv,
        module_env: &ModuleEnv,
        function: FunctionEnv,
    ) -> Option<ForkInfo> {
        let current_module = module_env.get_name();
        let attrs = function.get_attributes();
        let fork_symbol = env.symbol_pool().make(FORK);
        let test_name = env.symbol_pool().make(TestingAttribute::TEST);
        let fork_attribute_opt = attrs.iter().find(|a| a.name() == fork_symbol);
        // TODO: check test exists
        let _test_attribute_opt = attrs.iter().find(|a| a.name() == test_name);

        if let Some(fork_attribute) = fork_attribute_opt {
            let mut fork_info = ForkInfo::default();
            parse_fork_attribute(env, current_module, fork_attribute, &mut fork_info, 0);
            Some(fork_info)
        } else {
            None
        }
    }

    fn parse_fork_attribute(
        env: &GlobalEnv,
        current_module: &ModuleName,
        fork_attribute: &Attribute,
        fork_info: &mut ForkInfo,
        depth: usize,
    ) {
        match fork_attribute {
            Attribute::Apply(id, _, _) if depth > 0 => {
                let aloc = env.get_node_loc(*id);
                env.error(&aloc, "Unexpected nested attribute in fork declaration");
            },
            Attribute::Apply(_id, sym, vec) => {
                assert!(
                    *FORK == env.symbol_pool().string(*sym).to_string(),
                    "ICE: We should only be parsing a raw fork attribute"
                );
                vec.iter()
                    .for_each(|attr| parse_fork_attribute(env, current_module, attr, fork_info, depth + 1));
            },
            Attribute::Assign(id, sym, val) => {
                if depth != 1 {
                    let aloc = env.get_node_loc(*id);
                    env.error(&aloc, "Unexpected fork attribute in test declaration");
                }
                let key = env.symbol_pool().string(*sym).to_string();
                match key.as_str() {
                    FORK_NETWORK => match val {
                        AttributeValue::Value(_id, Value::ByteArray(bytes)) => {
                            if let Ok(network) = String::from_utf8(bytes.clone()) {
                                fork_info.network = Some(network)
                            } else {
                                let aloc = env.get_node_loc(*id);
                                let assign_loc = env.get_node_loc(*id);
                                env.error_with_labels(
                                    &assign_loc,
                                    "Unsupported attribute value",
                                    vec![(aloc, "Assigned in this attribute".to_string())],
                                );
                            }
                        },
                        _ => {
                            let aloc = env.get_node_loc(*id);
                            let assign_loc = env.get_node_loc(*id);
                            env.error_with_labels(
                                &assign_loc,
                                "Unsupported attribute value",
                                vec![(aloc, "Assigned in this attribute".to_string())],
                            );
                        },
                    },
                    FORK_VERSION => {
                        let version = convert_constant_value_u64_constant_or_value(
                            env,
                            current_module,
                            val,
                        ).map(|d| d.2);
                        match version {
                            None => {
                                let aloc = env.get_node_loc(*id);
                                let assign_loc = env.get_node_loc(*id);
                                env.error_with_labels(
                                    &assign_loc,
                                    "attribute value too big",
                                    vec![(aloc, "Assigned in this attribute".to_string())],
                                );
                            }
                            Some(v) => {
                                fork_info.version = Some(v);
                            }
                        }
                    },
                    _ => {
                        let aloc = env.get_node_loc(*id);
                        let assign_loc = env.get_node_loc(*id);
                        env.error_with_labels(&assign_loc, "Unsupported attribute key", vec![(
                            aloc,
                            "Assigned in this attribute".to_string(),
                        )]);
                    },
                }
            },
        }
    }
}

struct CachedRemoteStateView<R> {
    cache: LocalFileCache,
    state_view: R,
}
impl<R: TStateView<Key=StateKey>> TStateView for CachedRemoteStateView<R> {
    type Key = StateKey;

    fn get_state_value(&self, state_key: &Self::Key) -> StateViewResult<Option<StateValue>> {
        match self.cache.get_state_value(state_key) {
            Ok(Some(value)) => Ok(value),
            Ok(None) => {
                // If not found in cache, fetch from remote state view and save to cache
                let value = self.state_view.get_state_value(state_key)?;
                self.cache.save(state_key, &value)?;
                Ok(value)
            },
            Err(e) => Err(e),
        }
    }

    fn get_usage(&self) -> StateViewResult<StateStorageUsage> {
        self.state_view.get_usage()
    }
}

struct LocalFileCache {
    base_dir: PathBuf,
}

impl LocalFileCache {
    pub fn new(base_dir: PathBuf) -> Self {
        std::fs::create_dir_all(&base_dir).expect("Failed to create base directory for file cache");
        Self { base_dir }
    }

    pub fn save(&self, state_key: &StateKey, state_value: &Option<StateValue>) -> StateViewResult<()> {
        let hash = state_key.crypto_hash_ref();
        let file_path = self.base_dir.join(format!("{:x}.bcs", hash));
        let bytes = bcs::to_bytes(state_value).map_err(|e| StateViewError::BcsError(e))?;
        std::fs::write(&file_path, bytes)
            .map_err(|e| StateViewError::Other(e.to_string()))?;
        Ok(())
    }

    fn get_state_value(&self, state_key: &StateKey) -> StateViewResult<Option<Option<StateValue>>> {
        let hash = state_key.crypto_hash_ref();
        let file_path = self.base_dir.join(format!("{:x}.bcs", hash));
        if file_path.exists() {
            let bytes = std::fs::read(&file_path)
                .map_err(|e| StateViewError::Other(e.to_string()))?;
            let state = bcs::from_bytes(bytes.as_slice()).map_err(|e| StateViewError::BcsError(e))?;
            Ok(Some(state))
        } else {
            Ok(None)
        }
    }
}