module QUIC.UInt62
module U64 = FStar.UInt64
include FStar.UInt64

inline_for_extraction
let bound : (bound: U64.t { U64.v bound == pow2 62 }) =
  [@inline_let] let v = 4611686018427387904uL in
  [@inline_let] let _ = assert_norm (U64.v v == pow2 62) in
  v

inline_for_extraction
let t = (x: U64.t { U64.v x < U64.v bound })

module Secret = QUIC.Secret.Int

inline_for_extraction
let secret = (x: Secret.uint64 { Secret.v x < U64.v bound })
