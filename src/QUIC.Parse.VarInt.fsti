module QUIC.Parse.VarInt
include QUIC.Spec.Base

module U64 = FStar.UInt64
module LP = LowParse.Spec.BoundedInt // for bounded_int32
module LL = LowParse.Low.Base

inline_for_extraction
let parse_varint_kind = {
  LP.parser_kind_low = 1;
  LP.parser_kind_high = Some 8;
  LP.parser_kind_subkind = Some LP.ParserStrong;
  LP.parser_kind_metadata = None;
}

val parse_varint : LP.parser parse_varint_kind uint62_t

val serialize_varint : LP.serializer parse_varint

val parse_bounded_varint
  (min: nat)
  (max: nat { min <= max /\ max < 4294967296 })
: Tot (LP.parser parse_varint_kind (LP.bounded_int32 min max))

val serialize_bounded_varint
  (min: nat)
  (max: nat { min <= max /\ max < 4294967296 })
: Tot (LP.serializer (parse_bounded_varint min max))

val validate_varint: LL.validator parse_varint

val read_varint: LL.leaf_reader parse_varint

val jump_varint: LL.jumper parse_varint

val serialize_varint_impl: LL.serializer32 serialize_varint

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
val serialize_bounded_varint_impl
  (min: nat)
  (max: nat { min <= max /\ max < 4294967296 })
: Tot (LL.serializer32 (serialize_bounded_varint min max))

