module QUIC.Spec.VarInt

module U62 = QUIC.UInt62
module U64 = FStar.UInt64
module LP = LowParse.Spec.BoundedInt // for bounded_int32

inline_for_extraction
let parse_varint_kind = {
  LP.parser_kind_low = 1;
  LP.parser_kind_high = Some 8;
  LP.parser_kind_subkind = Some LP.ParserStrong;
  LP.parser_kind_metadata = None;
}

val parse_varint : LP.parser parse_varint_kind U62.t

val serialize_varint : LP.serializer parse_varint

val parse_bounded_varint
  (min: nat)
  (max: nat { min <= max /\ max < 4294967296 })
: Tot (LP.parser parse_varint_kind (LP.bounded_int32 min max))

val serialize_bounded_varint
  (min: nat)
  (max: nat { min <= max /\ max < 4294967296 })
: Tot (LP.serializer (parse_bounded_varint min max))
