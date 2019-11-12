module QUIC.Impl.VarInt
include QUIC.Spec.VarInt
open QUIC.Impl.Base

module Cast = FStar.Int.Cast
module U64 = FStar.UInt64
module LP = LowParse.Spec.BoundedInt // for bounded_int32
module LL = LowParse.Low.Base

val validate_varint: LL.validator parse_varint

val read_varint: LL.leaf_reader parse_varint

val jump_varint: LL.jumper parse_varint

val serialize_varint: LL.serializer32 serialize_varint

module U32 = FStar.UInt32

val validate_bounded_varint
  (min: U32.t)
  (max: U32.t { U32.v min <= U32.v max })
: Tot (LL.validator (parse_bounded_varint (U32.v min) (U32.v max)))

inline_for_extraction
noextract
val read_bounded_varint
  (min: nat)
  (max: nat { min <= max /\ max < 4294967296 })
: Tot (LL.leaf_reader (parse_bounded_varint min max))

inline_for_extraction
noextract
val jump_bounded_varint
  (min: nat)
  (max: nat { min <= max /\ max < 4294967296 })
: Tot (LL.jumper (parse_bounded_varint min max))

inline_for_extraction
noextract
val serialize_bounded_varint
  (min: nat)
  (max: nat { min <= max /\ max < 4294967296 })
: Tot (LL.serializer32 (serialize_bounded_varint min max))

val varint_len_correct
  (x: uint62_t)
: Lemma
  (U32.v (varint_len x) == FStar.Seq.length (LP.serialize QUIC.Spec.VarInt.serialize_varint x))

val bounded_varint_len_correct
  (min: nat)
  (max: nat { min <= max /\ max < 4294967296 })
  (x: LP.bounded_int32 min max)
: Lemma
  (U32.v (varint_len (Cast.uint32_to_uint64 x)) == FStar.Seq.length (LP.serialize (QUIC.Spec.VarInt.serialize_bounded_varint min max) x))
