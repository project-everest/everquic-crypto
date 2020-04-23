module QUIC.Impl.PacketNumber
include QUIC.Spec.PacketNumber

module U64 = FStar.UInt64
module U32 = FStar.UInt32
module HST = FStar.HyperStack.ST
module B = LowStar.Buffer
module HS = FStar.HyperStack
module Secret = QUIC.Secret
module SecretBuffer = QUIC.SecretBuffer
module LP = LowParse.Spec.Base

val read_packet_number
  (last: last_packet_number_t)
  (pn_len: packet_number_length_t)
  (b: B.buffer Secret.uint8)
: HST.Stack (packet_number_t' last pn_len)
  (requires (fun h ->
    B.live h b /\
    4 <= B.length b
  ))
  (ensures (fun h res h' ->
    B.modifies B.loc_none h h' /\
    begin match LP.parse (parse_packet_number last pn_len) (SecretBuffer.seq_reveal (B.as_seq h b)) with
    | Some (v, _) -> res == v
    | None -> False
    end
  ))

val write_packet_number
  (last: last_packet_number_t)
  (pn_len: packet_number_length_t)
  (pn: packet_number_t' last pn_len)
  (b: B.buffer Secret.uint8)
: HST.Stack unit
  (requires (fun h ->
    B.live h b /\
    4 <= B.length b
  ))
  (ensures (fun h _ h' ->
    let b' = B.gsub b 0ul (U32.uint_to_t (Secret.v pn_len)) in
    B.modifies (B.loc_buffer b') h h' /\
    SecretBuffer.seq_reveal (B.as_seq h' b') == LP.serialize (serialize_packet_number last pn_len) pn
  ))
