module Model.Flags

/// A generic flag that enables cryptographic modeling. Allows defining a switch
/// between calling the specification / calling the implementation.
inline_for_extraction
val model : bool

type ideal_flag = b:bool{b ==> model}

/// Specific flags for each one of our cryptographic security assumptions.

/// Ideal keying for transport secret (?)
inline_for_extraction val ideal_TS: ideal_flag

/// Ideal encrypted authenticated functionality
inline_for_extraction val ideal_AEAD : f:ideal_flag{b2t f ==> b2t ideal_TS}

/// Ideal PRF used with an auxiliary key.
///
/// TODO: figure out whether sequentialization is needed (e.g. because PRF needs
/// a perfect random input from AEAD) or if it's just a stylistic thing
inline_for_extraction val ideal_PRF : f:ideal_flag{b2t f ==> b2t ideal_AEAD}
