module QUIC.Impl.Header

(*
include QUIC.Spec.Header
include QUIC.Impl.Base

module B = LowStar.Buffer
module U8 = FStar.UInt8
module U32 = FStar.UInt32
module HST = FStar.HyperStack.ST
module S = FStar.Seq
module U64 = FStar.UInt64

module Spec = QUIC.Spec.Header
module Impl = QUIC.Impl.Base

val read_header
  (packet: B.buffer U8.t)
  (packet_len: U32.t { let v = U32.v packet_len in v == B.length packet })
  (cid_len: U32.t { U32.v cid_len <= 20 } )
  (last: uint62_t { U64.v last + 1 < pow2 62 })
: HST.Stack (option (Impl.header & uint62_t & U32.t))
  (requires (fun h ->
    B.live h packet
  ))
  (ensures (fun h res h' ->
    B.modifies B.loc_none h h' /\
    begin
      let spec = parse_header (U32.v cid_len) (U64.v last) (B.as_seq h packet) in
      match res with
      | None ->
        begin match spec with
        | H_Failure -> True
        | H_Success hd _ ->
          ((~ (Spec.is_retry hd)) /\ Spec.header_len hd + 4 > B.length packet)
        end
      | Some (x, pn, len) ->
        H_Success? spec /\
        begin
          let H_Success hd _ = spec in
          Impl.header_live x h' /\
          U32.v len <= B.length packet /\
          B.loc_buffer (B.gsub packet 0ul len) `B.loc_includes` Impl.header_footprint x /\
          Impl.g_header x h' pn == hd /\
          U32.v len = Spec.header_len hd
        end
    end
  ))

module HS = FStar.HyperStack

val header_len_correct
  (h: Impl.header)
  (m: HS.mem)
  (pn: uint62_t)
: Lemma
  (U32.v (Impl.header_len h) == Spec.header_len (Impl.g_header h m pn))

val write_header
  (dst: B.buffer U8.t)
  (x: Impl.header)
  (pn: uint62_t)
: HST.Stack unit
  (requires (fun h ->
    B.live h dst /\
    Impl.header_live x h /\
    B.length dst >= Spec.header_len (Impl.g_header x h pn) + (if Impl.is_retry x then 0 else 4) /\
    Impl.header_footprint x `B.loc_disjoint` B.loc_buffer dst
  ))
  (ensures (fun h _ h' ->
    let len = Spec.header_len (Impl.g_header x h pn) in
    B.modifies (B.loc_buffer dst) h h' /\
    S.slice (B.as_seq h' dst) 0 len == format_header (Impl.g_header x h pn)
  ))

val putative_pn_offset
  (cid_len: U32.t)
  (b: B.buffer U8.t)
  (len: U32.t { U32.v len == B.length b })
: HST.Stack U32.t
  (requires (fun h ->
    B.live h b
  ))
  (ensures (fun h res h' ->
    B.modifies B.loc_none h h' /\ (
    let x = putative_pn_offset (U32.v cid_len) (B.as_seq h b) in
    if res = 0ul
    then
      None? x
    else
      Some? x /\ (
      let Some v = x in
      U32.v res == v
  ))))

val pn_offset
  (h: Impl.header)
  (pn: Ghost.erased uint62_t)
: HST.Stack U32.t
  (requires (fun m ->
    Impl.header_live h m /\
    (~ (Spec.is_retry (Impl.g_header h m (Ghost.reveal pn))))
  ))
  (ensures (fun m res m' ->
    B.modifies B.loc_none m m' /\
    U32.v res == pn_offset (Impl.g_header h m (Ghost.reveal pn))
  ))
