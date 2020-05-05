module QUIC.Spec.PacketNumber.Base

module U62 = QUIC.UInt62
module U64 = FStar.UInt64
module U32 = FStar.UInt32
module Secret = QUIC.Secret.Int

inline_for_extraction
noextract
type packet_number_length_t = (x: Secret.uint32 { 1 <= Secret.v x /\ Secret.v x <= 4 })

inline_for_extraction
let last_packet_number_t = (last: U62.secret { Secret.v last + 1 < U62.v U62.bound})


(* Packet number *)

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
