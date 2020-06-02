module QUIC.Secret.Int.Base
include Lib.IntTypes

module U8 = FStar.UInt8
module U16 = FStar.UInt16
module U32 = FStar.UInt32
module U64 = FStar.UInt64

unfold
let v #t #l (u: int_t t l) : GTot (range_t t) =
  v u

noextract
let supported_type = function
  | U8 | U16 | U32 | U64 -> true
  | _ -> false
