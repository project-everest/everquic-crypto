module QUIC.Impl.Header.Parse
open QUIC.Spec.Header.Parse
include QUIC.Impl.Header.Base

module HS = FStar.HyperStack
module U32 = FStar.UInt32
module Seq = FStar.Seq
module PN = QUIC.Spec.PacketNumber.Base
module Secret = QUIC.Secret.Int
module Spec = QUIC.Spec.Header.Parse
module U8 = FStar.UInt8
module B = LowStar.Buffer
module HST = FStar.HyperStack.ST

val public_header_len_is_pn_offset
  (h: header { ~ (is_retry h) })
  (m: HS.mem)
  (pn: PN.packet_number_t)
: Lemma
  (U32.v (public_header_len h) == pn_offset (g_header h m pn))

val header_len_correct
  (h: header)
  (m: HS.mem)
  (pn: PN.packet_number_t)
: Lemma
  (Secret.v (header_len h) == Spec.header_len (g_header h m pn))

val write_header
  (h: header)
  (pn: PN.packet_number_t)
  (out: B.buffer U8.t)
  (out_len: U32.t { U32.v out_len <= B.length out })
: HST.Stack unit
  (requires (fun h0 ->
    header_live h h0 /\
    B.live h0 out /\
    B.loc_disjoint (header_footprint h) (B.loc_buffer out) /\
    U32.v (public_header_len h) + 4 <= U32.v out_len // needs more space than just pn_length to write pn in constant time
  ))
  (ensures (fun h0 _ h1 ->
    let gh = g_header h h0 pn in
    let s = format_header gh in
    let len = header_len h in
    B.modifies (B.loc_buffer out) h0 h1 /\
    Secret.v len <= U32.v out_len /\
    Seq.slice (B.as_seq h1 out) 0 (Secret.v len) `Seq.equal` s 
  ))

val putative_pn_offset
  (cid_len: short_dcid_len_t)
  (b: B.buffer U8.t)
  (b_len: U32.t { U32.v b_len == B.length b })
: HST.Stack (option U32.t)
  (requires (fun h ->
    B.live h b
  ))
  (ensures (fun h res h' ->
    B.modifies B.loc_none h h' /\
    begin match Spec.putative_pn_offset (U32.v cid_len) (B.as_seq h b), res with
    | None, None -> True
    | Some off, Some off' -> U32.v off' == off
    | _ -> False
    end
  ))

val read_header
  (packet: B.buffer U8.t)
  (packet_len: U32.t { let v = U32.v packet_len in v == B.length packet })
  (cid_len: U32.t { U32.v cid_len <= 20 } )
  (last: PN.last_packet_number_t)
: HST.Stack (header & PN.packet_number_t)
  (requires (fun h ->
    B.live h packet /\
    begin match Spec.putative_pn_offset (U32.v cid_len) (B.as_seq h packet) with
    | None -> False
    | Some off -> (~ (packet_is_retry (B.as_seq h packet))) ==> off + 4 <= B.length packet
    end
  ))
  (ensures (fun h (x, pn) h' ->
    B.modifies B.loc_none h h' /\
    begin match parse_header (U32.v cid_len) (Secret.v last) (B.as_seq h packet) with
    | H_Success hd _ ->
      let len = public_header_len x in
      U32.v len <= B.length packet /\
      header_live x h' /\
      B.loc_buffer (B.gsub packet 0ul len) `B.loc_includes` header_footprint x /\
      g_header x h' pn == hd
    | _ -> False
    end
  ))
