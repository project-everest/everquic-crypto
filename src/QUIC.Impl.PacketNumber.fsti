module QUIC.Impl.PacketNumber
include QUIC.Spec.PacketNumber
open QUIC.Spec.Base
open LowParse.Low.Writers

module U64 = FStar.UInt64
module U32 = FStar.UInt32
module HST = FStar.HyperStack.ST
module B = LowStar.Buffer
module HS = FStar.HyperStack

inline_for_extraction
val validate_packet_number
  (last: last_packet_number_t)
  (pn_len: packet_number_length_t)
: Tot (validator (parse_packet_number last pn_len))

inline_for_extraction
val jump_packet_number
  (last: last_packet_number_t)
  (pn_len: packet_number_length_t)
: Tot (jumper (parse_packet_number last pn_len))

inline_for_extraction
val read_packet_number
  (last: last_packet_number_t)
  (pn_len: packet_number_length_t)
  (#rrel: _)
  (#rel: _)
  (sl: slice rrel rel)
  (pos: U32.t)
: HST.Stack (packet_number_t last pn_len)
  (requires (fun h ->
    live_slice h sl /\
    U32.v pos + 4 <= U32.v sl.len
  ))
  (ensures (fun h res h' ->
    B.modifies B.loc_none h h' /\
    valid_content (parse_packet_number last pn_len) h sl pos res
  ))

inline_for_extraction
noextract
val swrite_packet_number
  (last: last_packet_number_t)
  (pn_len: packet_number_length_t)
  (pn: packet_number_t last pn_len)
  (h0: HS.mem)
  (sout: slice (srel_of_buffer_srel (B.trivial_preorder _)) (srel_of_buffer_srel (B.trivial_preorder _)))
  (pout_from0: U32.t)
: Tot (y: swriter (serialize_packet_number last pn_len) h0 (4 - U32.v pn_len) sout pout_from0 { swvalue y == pn })
