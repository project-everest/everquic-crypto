module QUIC.Spec.PacketNumber
open LowParse.Spec.Base

module U62 = QUIC.UInt62
module U64 = FStar.UInt64
module U32 = FStar.UInt32
module Secret = QUIC.Secret.Int

inline_for_extraction
noextract
type packet_number_length_t = (x: Secret.uint32 { 1 <= Secret.v x /\ Secret.v x <= 4 })

inline_for_extraction
let parse_packet_number_kind = strong_parser_kind 1 4 None

(* Packet number *)

inline_for_extraction
let last_packet_number_t = (last: U62.secret { Secret.v last + 1 < U62.v U62.bound})

let bound_npn' (pn_len:nat { pn_len < 4 }) : Tot (y: nat {y == pow2 (8 `op_Multiply` (pn_len + 1)) }) =
  assert_norm (pow2 8 == 256);
  assert_norm (pow2 16 == 65536);
  assert_norm (pow2 24 == 16777216);
  assert_norm (pow2 32 == 4294967296);
  match pn_len with
  | 0 -> 256
  | 1 -> 65536
  | 2 -> 16777216
  | 3 -> 4294967296

let in_window (pn_len: nat { pn_len < 4 }) (last pn:nat) : Tot bool =
  let h = bound_npn' pn_len in
  (last+1 < h/2 && pn < h) ||
  (last+1 >= U62.v U62.bound - h/2 && pn >= U62.v U62.bound - h) ||
  (last+1 - h/2 < pn && pn <= last+1 + h/2)

inline_for_extraction
let packet_number_t = U62.secret

inline_for_extraction
let packet_number_t'
  (last: last_packet_number_t)
  (pn_len: packet_number_length_t)
: Tot Type0
= (pn: packet_number_t { in_window (Secret.v pn_len - 1) (Secret.v last) (Secret.v pn) })

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
