module QUIC.Spec.PacketNumber
open QUIC.Spec.Base
open LowParse.Spec.Base

module U64 = FStar.UInt64
module U32 = FStar.UInt32

inline_for_extraction
let parse_packet_number_kind
  (sz: packet_number_length_t)
: Tot parser_kind
= total_constant_size_parser_kind (U32.v sz)

inline_for_extraction
let packet_number_t
  (last: last_packet_number_t)
  (pn_len: packet_number_length_t)
: Tot eqtype
= (pn: uint62_t { in_window (U32.v pn_len - 1) (U64.v last) (U64.v pn) })

val parse_packet_number
  (last: last_packet_number_t)
  (pn_len: packet_number_length_t)
: Tot (parser (parse_packet_number_kind pn_len) (packet_number_t last pn_len))

val serialize_packet_number
  (last: last_packet_number_t)
  (pn_len: packet_number_length_t)
: Tot (serializer (parse_packet_number last pn_len))

val serialize_packet_number_ext
  (last1 last2: last_packet_number_t)
  (pn_len: packet_number_length_t)
  (pn: uint62_t)
: Lemma
  (requires (
    in_window (U32.v pn_len - 1) (U64.v last1) (U64.v pn) /\
    in_window (U32.v pn_len - 1) (U64.v last2) (U64.v pn)
  ))
  (ensures (
    serialize (serialize_packet_number last1 pn_len) pn == serialize (serialize_packet_number last2 pn_len) pn
  ))
