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
