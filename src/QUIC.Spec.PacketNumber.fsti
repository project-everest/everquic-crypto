module QUIC.Spec.PacketNumber
include QUIC.Spec.PacketNumber.Base
open LowParse.Spec.Base

module U62 = QUIC.UInt62
module U64 = FStar.UInt64
module U32 = FStar.UInt32
module Secret = QUIC.Secret.Int

inline_for_extraction
let parse_packet_number_kind = strong_parser_kind 1 4 None

val parse_packet_number
  (last: last_packet_number_t)
  (pn_len: packet_number_length_t)
: Tot (parser parse_packet_number_kind (packet_number_t' last pn_len))

inline_for_extraction
let parse_packet_number_kind'
  (sz: packet_number_length_t)
: GTot parser_kind
= total_constant_size_parser_kind (Secret.v sz)

(* we cannot use this as the actual parser kind, because it is ghost,
   relying on the actual value of pn_len. So we work around:  *)

val parse_packet_number_kind'_correct
  (last: last_packet_number_t)
  (pn_len: packet_number_length_t)
: Lemma
  (parser_kind_prop (parse_packet_number_kind' pn_len) (parse_packet_number last pn_len))

val serialize_packet_number
  (last: last_packet_number_t)
  (pn_len: packet_number_length_t)
: Tot (serializer (parse_packet_number last pn_len))

val serialize_packet_number_ext
  (last1 last2: last_packet_number_t)
  (pn_len: packet_number_length_t)
  (pn: packet_number_t)
: Lemma
  (requires (
    in_window (Secret.v pn_len - 1) (Secret.v last1) (Secret.v pn) /\
    in_window (Secret.v pn_len - 1) (Secret.v last2) (Secret.v pn)
  ))
  (ensures (
    serialize (serialize_packet_number last1 pn_len) pn == serialize (serialize_packet_number last2 pn_len) pn
  ))
