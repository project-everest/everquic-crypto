module QUIC.Impl.Header
include QUIC.Impl.Header.Base

open QUIC.Spec.Crypto

module G = FStar.Ghost
module U8 = FStar.UInt8
module B = LowStar.Buffer
module U32 = FStar.UInt32
module Secret = QUIC.Secret.Int
module PN = QUIC.Spec.PacketNumber.Base
module HST = FStar.HyperStack.ST
module Seq = FStar.Seq
module HS = FStar.HyperStack

module Spec = QUIC.Spec.Header
module Parse = QUIC.Spec.Header.Parse
module AEAD = Spec.Agile.AEAD

module CTR = EverCrypt.CTR // because we do not want to friend the full state definition here

unfold
let header_encrypt_pre
  (a: ea)
  (s: CTR.state (AEAD.cipher_alg_of_supported_alg a))
  (k: B.buffer Secret.uint8)
  (dst:B.buffer U8.t)
  (h: G.erased Spec.header)
  (is_short: bool)
  (is_retry: bool)
  (public_len: U32.t)
  (pn_len: PN.packet_number_length_t)
  (m: HS.mem)
: GTot Type0
=
  let a' = AEAD.cipher_alg_of_supported_alg a in
  let fmt = Parse.format_header h in
  let header_len = Seq.length fmt in

  B.all_disjoint [
    CTR.footprint m s;
    B.loc_buffer k;
    B.loc_buffer dst;
  ] /\

  CTR.invariant m s /\
  B.live m k /\ B.length k == Spec.Agile.Cipher.key_length a' /\
  B.live m dst /\

  is_short == Spec.MShort? h /\
  is_retry == Spec.is_retry h /\
  begin if is_retry
  then
    U32.v public_len == header_len /\
    B.length dst == header_len
  else
    let cipher_len = B.length dst - header_len in
    U32.v public_len == Parse.pn_offset h /\
    pn_len == Spec.pn_length h /\
    19 <= cipher_len /\ cipher_len < max_cipher_length
  end /\
  Seq.slice (B.as_seq m dst) 0 header_len `Seq.equal` fmt

unfold
let header_encrypt_post
  (a: ea)
  (s: CTR.state (AEAD.cipher_alg_of_supported_alg a))
  (k: B.buffer Secret.uint8)
  (dst:B.buffer U8.t)
  (h: G.erased Spec.header)
  (is_short: bool)
  (is_retry: bool)
  (public_len: U32.t)
  (pn_len: PN.packet_number_length_t)
  (m: HS.mem)
  (m' : HS.mem)
: GTot Type0
= 
  header_encrypt_pre a s k dst h is_short is_retry public_len pn_len m /\
  begin
    let a' = AEAD.cipher_alg_of_supported_alg a in
    let fmt = Parse.format_header h in
    let header_len = Seq.length fmt in
    let cipher = Seq.slice (B.as_seq m dst) header_len (B.length dst) in
    B.modifies (B.loc_buffer dst `B.loc_union` CTR.footprint m s) m m' /\
    B.as_seq m' dst `Seq.equal`
      Spec.header_encrypt a (B.as_seq m k) h cipher /\
    CTR.invariant m' s /\
    CTR.footprint m s == CTR.footprint m' s
  end

val header_encrypt: a: ea ->
  (s: CTR.state (Spec.Agile.AEAD.cipher_alg_of_supported_alg a)) ->
  (k: B.buffer Secret.uint8) ->
  dst:B.buffer U8.t ->
  h: G.erased Spec.header ->
  is_short: bool ->
  is_retry: bool ->
  public_len: U32.t ->
  pn_len: PN.packet_number_length_t ->
  HST.Stack unit
    (requires (fun h0 ->
      header_encrypt_pre a s k dst h is_short is_retry public_len pn_len h0
    ))
    (ensures fun h0 _ h1 ->
      header_encrypt_post a s k dst h is_short is_retry public_len pn_len h0 h1
    )

(*
      let fmt = Parse.format_header h in
      let header_len = Seq.length fmt in
    )
  )

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
