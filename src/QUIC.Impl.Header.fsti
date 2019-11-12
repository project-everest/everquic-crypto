module QUIC.Impl.Header
include QUIC.Spec.Header

module B = LowStar.Buffer
module U8 = FStar.UInt8
module U32 = FStar.UInt32
module HST = FStar.HyperStack.ST
module S = FStar.Seq
module U64 = FStar.UInt64

module Impl = QUIC.Impl.Base

val read_header
  (packet: B.buffer U8.t)
  (packet_len: U32.t { let v = U32.v packet_len in v == B.length packet /\ v < 4294967280 })
  (cid_len: U32.t { U32.v cid_len < 20 } )
  (last: uint62_t { U64.v last + 1 < pow2 62 })
: HST.Stack (option (Impl.header & U32.t))
  (requires (fun h ->
    B.live h packet
  ))
  (ensures (fun h res h' ->
    B.modifies B.loc_none h h' /\
    begin
      let spec = parse_header (U32.v cid_len) (U64.v last) (B.as_seq h packet) in
      match res with
      | None -> H_Failure? spec
      | Some (x, len) ->
        H_Success? spec /\
        begin
          let H_Success hd _ = spec in
          Impl.header_live x h' /\
          U32.v len <= B.length packet /\
          B.loc_buffer (B.gsub packet 0ul len) `B.loc_includes` Impl.header_footprint x /\
          Impl.g_header x h' == hd /\
          U32.v len = header_len hd
        end
    end
  ))

val header_length
  (x: Impl.header)
: HST.Stack U32.t
  (requires (fun h -> Impl.header_live x h))
  (ensures (fun h res h' ->
    B.modifies B.loc_none h h' /\
    U32.v res == header_len (Impl.g_header x h)
  ))

val write_header
  (dst: B.buffer U8.t)
  (x: Impl.header)
: HST.Stack unit
  (requires (fun h ->
    B.live h dst /\
    Impl.header_live x h /\
    B.length dst == header_len (Impl.g_header x h) /\
    Impl.header_footprint x `B.loc_disjoint` B.loc_buffer dst
  ))
  (ensures (fun h _ h' ->
    B.modifies (B.loc_buffer dst) h h' /\
    B.as_seq h' dst == format_header (Impl.g_header x h)
  ))

val putative_pn_offset
  (cid_len: U32.t)
  (b: B.buffer U8.t)
  (len: U32.t { U32.v len == B.length b /\ U32.v len < 4294967280 })
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
: HST.Stack U32.t
  (requires (fun m ->
    Impl.header_live h m /\
    (~ (is_retry (Impl.g_header h m)))
  ))
  (ensures (fun m res m' ->
    B.modifies B.loc_none m m' /\
    U32.v res == pn_offset (Impl.g_header h m)
  ))

val header_len
  (h: Impl.header)
: HST.Stack U32.t
  (requires (fun m ->
    Impl.header_live h m
  ))
  (ensures (fun m res m' ->
    B.modifies B.loc_none m m' /\
    U32.v res == header_len (Impl.g_header h m)
  ))
