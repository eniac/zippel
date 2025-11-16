#[cfg(test)]
mod runtime_tests {
    use crate::graph::RuntimeInformation;
    use backend::config::ArkBls12_381;

    type TestConfig = ArkBls12_381;

    #[test]
    fn test_runtime_information_creation() {
        // Just test that we can create RuntimeInformation
        let _rt_info = RuntimeInformation::<TestConfig>::new(4);
        let _rt_info2 = RuntimeInformation::<TestConfig>::new(1);
        let _rt_info3 = RuntimeInformation::<TestConfig>::new(16);
    }
}
