use crate::config::{ArkBls12_381, ArkCurve25519, ArkField17, ArkField65537};
use lang::typ::backend::BackendConfig;

#[test]
fn test_arkfield17_fft_domain_limits() {
    assert!(<ArkField17 as BackendConfig>::supports_fft_domain(0));
    assert!(<ArkField17 as BackendConfig>::supports_fft_domain(4));
    assert!(<ArkField17 as BackendConfig>::supports_fft_domain(8));
    assert!(<ArkField17 as BackendConfig>::supports_fft_domain(16));
    assert!(!<ArkField17 as BackendConfig>::supports_fft_domain(32));
    assert!(!<ArkField17 as BackendConfig>::supports_fft_domain(64));
}

#[test]
fn test_arkfield65537_fft_domain_limits() {
    assert!(<ArkField65537 as BackendConfig>::supports_fft_domain(0));
    assert!(<ArkField65537 as BackendConfig>::supports_fft_domain(256));
    assert!(<ArkField65537 as BackendConfig>::supports_fft_domain(65536));
    assert!(!<ArkField65537 as BackendConfig>::supports_fft_domain(
        131072
    ));
}

#[test]
fn test_pairing_support() {
    assert!(<ArkBls12_381 as BackendConfig>::supports_pairing());
    assert!(!<ArkCurve25519 as BackendConfig>::supports_pairing());
    assert!(!<ArkField17 as BackendConfig>::supports_pairing());
    assert!(!<ArkField65537 as BackendConfig>::supports_pairing());
}
