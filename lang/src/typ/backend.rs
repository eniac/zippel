pub trait BackendConfig {
    fn supports_fft_domain(deg: usize) -> bool;
    fn supports_pairing() -> bool;
}
