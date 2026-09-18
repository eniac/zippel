/// Uninhabited-in-practice curve group used to fill `ArkConfig::G1`/`G2` for
/// field-only configurations.
pub mod nocurve;
/// Placeholder scalar field for configurations that carry no usable field type.
pub mod nofield;
/// Pairing stub selected as `ArkConfig::P` by every pairing-free curve config.
pub mod nopairing;
pub use nocurve::NoCurve;
pub use nofield::NoField;
pub use nopairing::NoPairing;
