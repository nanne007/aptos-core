script {
    fun test_script(_s: &signer) {
        let n = 1 + 1;
        assert!(n < 128, 0);
    }
}