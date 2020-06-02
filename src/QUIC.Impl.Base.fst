module QUIC.Impl.Base

module U32 = FStar.UInt32
module U62 = QUIC.UInt62

(* Length computations need to be transparent because the precondition
to QUIC.Impl.encrypt requires the user to provide a destination buffer
large enough to contain the byte representation of the header *)

let varint_len
  (x: U62.t)
: Tot (y: U32.t {U32.v y <= 8})
= if x `U62.lt` 64uL
  then 1ul
  else if x `U62.lt` 16384uL
  then 2ul
  else if x `U62.lt` 1073741824uL
  then 4ul
  else 8ul
