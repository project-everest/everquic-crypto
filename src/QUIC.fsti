module QUIC

module QSpec = QUIC.Spec
module QImpl = QUIC.Impl
module QImplBase = QUIC.Impl.Header.Base
module QModel = Model.QUIC
module PN = QUIC.Spec.PacketNumber.Base

module Secret = QUIC.Secret.Int

module I = Model.Indexing
module G = FStar.Ghost
module B = LowStar.Buffer
module S = FStar.Seq
module HS = FStar.HyperStack
module ST = FStar.HyperStack.ST

module U64 = FStar.UInt64
module U32 = FStar.UInt32
module U8 = FStar.UInt8

open FStar.HyperStack
open FStar.HyperStack.ST

open EverCrypt.Helpers
open EverCrypt.Error

#set-options "--fuel 0 --ifuel 0"

type nat62 = n:nat{n < pow2 62}

let cipher_keysize (a:QSpec.ea) =
  Spec.Agile.Cipher.key_length (Spec.Agile.AEAD.cipher_alg_of_supported_alg a)

/// Low-level types used in this API
/// --------------------------------

let u2 = QImpl.u2
let u4 = QImpl.u4
let u62 = QImpl.u62

val index:eqtype

val alg: index -> GTot QSpec.ea
val halg: index -> GTot QSpec.ha

let traffic_secret i =
  Spec.Hash.Definitions.bytes_hash (halg i)

// Switch state: either QModel or QImpl
val state: index -> Type0

val footprint: #i:index -> HS.mem -> state i -> GTot B.loc
val invariant: #i:index -> HS.mem -> state i -> Type0

val g_traffic_secret: #i:index -> state i -> HS.mem -> GTot (traffic_secret i)
val g_initial_packet_number: #i:index -> (s: state i) -> GTot PN.packet_number_t
val g_last_packet_number: #i:index -> (s:state i) -> (h: HS.mem { invariant h s }) ->
  GTot (pn: PN.packet_number_t {
    let open Lib.IntTypes in
    Secret.v pn >= Secret.v #U64 #SEC (g_initial_packet_number s)
  })

let incrementable (#i: index) (s: state i) (h: HS.mem { invariant h s }) =
  Secret.v (g_last_packet_number s h) + 1 < pow2 62

val encrypt: #i:(*G.erased *)index -> (
  //let i = G.reveal i in
  s: state i ->
  dst: B.buffer U8.t ->
  dst_pn: B.pointer PN.packet_number_t ->
  h: QImplBase.header ->
  plain: B.buffer U8.t ->
  plain_len: U32.t ->
  Stack error_code
    (requires fun h0 ->
      not (QImpl.is_retry h) /\ // until it's supported in Model.QUIC
      // Memory & preservation
      B.live h0 plain /\ B.live h0 dst /\ B.live h0 dst_pn /\
      QImplBase.header_live h h0 /\
      B.(all_disjoint [ footprint h0 s; loc_buffer dst; loc_buffer dst_pn; QImpl.header_footprint h; loc_buffer plain ]) /\
      invariant h0 s /\
      incrementable s h0 /\
      B.length plain == U32.v plain_len /\ (
      let clen =
        if QImplBase.is_retry h then
          0
        else
          U32.v plain_len + Spec.Agile.AEAD.tag_length (alg i)
      in
      (if QImplBase.is_retry h then U32.v plain_len == 0 else 3 <= U32.v plain_len /\ U32.v plain_len < QSpec.max_plain_length) /\
      (QImplBase.has_payload_length h ==> Secret.v (QImplBase.payload_length h) == clen) /\
      B.length dst == Secret.v (QImplBase.header_len h) + clen
    ))
    (ensures fun h0 r h1 ->
      match r with
      | Success ->
          // Memory & preservation
          B.(modifies (footprint h0 s `loc_union` loc_buffer dst `loc_union` loc_buffer dst_pn)) h0 h1 /\
          invariant h1 s /\
          footprint h1 s == footprint h0 s /\ (
          // Functional correctness
          let ts = g_traffic_secret s h0 in
          let open QUIC.Spec in
          let k = derive_secret (halg i) ts label_key (Spec.Agile.AEAD.key_length (alg i)) in
          let iv = derive_secret (halg i) ts label_iv 12 in
          let pne = derive_secret (halg i) ts label_hp (cipher_keysize (alg i)) in
          let plain = B.as_seq h0 plain in
          let packet: packet = B.as_seq h1 dst in
          let pn = g_last_packet_number s h0 `Secret.add` Secret.to_u64 1uL in
          B.deref h1 dst_pn == pn /\
          packet == encrypt (alg i) k iv pne (QImpl.g_header h h0 pn) plain /\
          g_last_packet_number s h1 == pn)
      | _ ->
          False))

unfold
let decrypt_post (i: index)
  (s:state i)
  (dst: B.pointer QImpl.result)
  (packet: B.buffer U8.t)
  (len: U32.t)
  (cid_len: U8.t)
  (h0: HS.mem)
  (res: error_code)
  (h1: HS.mem): Pure Type0
  (requires
    U8.v cid_len <= 20 /\
    U32.v len == B.length packet /\
    invariant h0 s /\
    incrementable s h0)
  (ensures fun _ -> True)
=
  let s0 = g_traffic_secret s h0 in
  let k = QSpec.(derive_secret (halg i) s0 label_key (Spec.Agile.AEAD.key_length (alg i))) in
  let iv = QSpec.(derive_secret (halg i) s0 label_iv 12) in
  let pne = QSpec.(derive_secret (halg i) s0 label_hp (cipher_keysize (alg i))) in
  let prev = g_last_packet_number s h0 in
  invariant h1 s /\
  footprint h1 s == footprint h0 s /\
  begin
    let r = B.deref h1 dst in
    let x = g_last_packet_number in
    let y = packet in
    let open QImpl in
    let packet = y in
    let g_last_packet_number = x in
    match res with
    | Success ->
      // prev is known to be >= g_initial_packet_number (see lemma invariant_packet_number)
      Secret.v (g_last_packet_number s h1) == FStar.Math.Lib.max (Secret.v prev) (Secret.v r.QImplBase.pn) /\ (

      // Lengths
      r.header_len == header_len r.header /\
      Secret.v r.header_len + Secret.v r.plain_len <= Secret.v r.total_len /\
      Secret.v r.total_len <= B.length packet /\
      B.(loc_includes (loc_buffer (B.gsub packet 0ul (Secret.reveal r.header_len))) (header_footprint r.header)) /\
      header_live r.header h1 /\
      Secret.v r.total_len <= B.length packet /\

      // Contents
      (
      let fmt = B.as_seq h1 (B.gsub packet 0ul (Secret.reveal r.header_len)) in
      let plain =
        B.as_seq h1 (B.gsub packet (Secret.reveal r.header_len) (Secret.reveal r.plain_len)) in
      let rem = B.as_seq h0 (B.gsub packet (Secret.reveal r.total_len) (B.len packet `U32.sub `Secret.reveal r.total_len)) in
      match QSpec.decrypt (alg i) k iv pne (Secret.v prev) (U8.v cid_len) (B.as_seq h0 packet) with
      | QSpec.Success h' plain' rem' ->
        h' == g_header r.header h1 r.pn /\
        fmt == QUIC.Spec.Header.Parse.format_header h' /\
        plain' == plain /\
        rem' == rem
      | _ -> False
    ))
    | DecodeError ->
      QSpec.Failure? (QSpec.decrypt (alg i) k iv pne (Secret.v prev) (U8.v cid_len) (B.as_seq h0 packet))
    | AuthenticationFailure ->
      QSpec.Failure? (QSpec.decrypt (alg i) k iv pne (Secret.v prev) (U8.v cid_len) (B.as_seq h0 packet)) /\
      Secret.v r.total_len <= B.length packet
    | _ ->
      False
  end

val decrypt: #i:G.erased index -> (
  let i = G.reveal i in
  s:state i ->
  dst: B.pointer QImpl.result ->
  packet: B.buffer U8.t ->
  len: U32.t{
    B.length packet == U32.v len
  } ->
  cid_len: U8.t { U8.v cid_len <= 20 } ->
  Stack error_code
    (requires fun h0 ->
      // We require clients to allocate space for a result, e.g.
      //   result r = { 0 };
      //   decrypt(s, &r, ...);
      // This means that we don't require that the pointers inside ``r`` be live
      // (i.e. NO ``header_live header`` precondition).
      // After a successful call to decrypt, ``packet`` contains the decrypted
      // data; ``header`` is modified to point within the header area of
      // ``packet``; and the plaintext is within ``packet`` in range
      // ``[header_len, header_len + plain_len)``.
      B.live h0 packet /\ B.live h0 dst /\
      B.(all_disjoint [ loc_buffer dst; loc_buffer packet; footprint h0 s ]) /\
      invariant h0 s /\
      incrementable s h0)
    (ensures fun h0 res h1 ->
      let r = B.deref h1 dst in
      decrypt_post i s dst packet len cid_len h0 res h1 /\
      begin match res with
      | Success ->
        B.(modifies (footprint h0 s `loc_union`
          loc_buffer (gsub packet 0ul (Secret.reveal r.QImpl.total_len)) `loc_union` loc_buffer dst) h0 h1)
      | DecodeError ->
        B.modifies (footprint h0 s `B.loc_union` B.loc_buffer packet) h0 h1
      | AuthenticationFailure ->
        B.(modifies (footprint h0 s `loc_union`
          loc_buffer (gsub packet 0ul (Secret.reveal r.QImpl.total_len)) `loc_union` loc_buffer dst) h0 h1)
      | _ -> False
      end
    )
  )
