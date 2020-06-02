module QUIC

module QSpec = QUIC.Spec
module QImpl = QUIC.Impl
module QImplBase = QUIC.Impl.Base
module QModel = Model.QUIC

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


/// Low-level types used in this API
/// --------------------------------

let u2 = QImpl.u2
let u4 = QImpl.u4
let u62 = QImpl.u62

let index =
  if I.model then QModel.id else QImpl.index

let mid (i:index{I.model}) = i <: QModel.id
let iid (i:index{not I.model}) = i <: QImpl.index

let alg (i:index) =
  if I.model then I.ae_id_ginfo (fst (mid i))
  else (iid i).QImpl.aead_alg

let halg (i:index) =
  if I.model then I.ae_id_ghash (fst (mid i))
  else (iid i).QImpl.hash_alg

let traffic_secret i =
  Spec.Hash.Definitions.bytes_hash (halg i)

let itraffic_secret (i:QModel.id) =
  Spec.Hash.Definitions.bytes_hash (I.ae_id_ghash (fst i))

module MH = Model.Helpers

let derived (#i:QModel.id) (#w:QModel.stream_writer i) (r:QModel.stream_reader w) (ts:itraffic_secret i) =
  if I.model && QModel.unsafe i then
    let ha = I.ae_id_hash (fst i) in
    let ea = I.ae_id_info (fst i) in
    let (k1, k2) = QModel.reader_leak r in
    QModel.writer_static_iv w ==
      QSpec.derive_secret ha ts QSpec.label_iv 12 /\
    k1 == QSpec.derive_secret ha ts
        QSpec.label_key (QSpec.ae_keysize ea) /\
    k2 == QUIC.Spec.derive_secret ha ts
        QUIC.Spec.label_key (QSpec.cipher_keysize ea)
  else True

noeq type mstate_t i =
| Ideal:
  writer: QModel.stream_writer i ->
  reader: QModel.stream_reader writer ->
  ts: itraffic_secret i{derived reader ts} -> // FIXME erased
  mstate_t i
  
let istate_t i = QImpl.state i

let state (i:index) =
  if I.model then mstate_t (mid i)
  else istate_t (iid i)

let mstate (#i:index{I.model}) (s:state i) = s <: mstate_t (mid i)
let istate (#i:index{not I.model}) (s:state i) = s <: istate_t (iid i)

let footprint (#i:index) (h:HS.mem) (s:state i) : GTot B.loc =
  if I.model then
    QModel.rfootprint (mstate s).reader
  else QImpl.footprint h (istate s)

let invariant #i (h:HS.mem) (s:state i) =
  if I.model then
    QModel.rinvariant (mstate s).reader h
  else QImpl.invariant h (istate s)

val g_initial_packet_number: #i:index -> (s: state i) -> GTot QSpec.nat62

val g_last_packet_number: #i:index -> (s:state i) -> (h: HS.mem { invariant h s }) ->
  GTot (pn: QSpec.uint62_t{
    U64.v pn >= g_initial_packet_number s
  })

let incrementable (#i: index) (s: state i) (h: HS.mem { invariant h s }) =
  U64.v (g_last_packet_number s h) + 1 < pow2 62

let g_traffic_secret (#i:index) (s:state i) (h:HS.mem)
  : GTot (traffic_secret i) =
  if I.model then
    (mstate s).ts <: traffic_secret i
  else 
    QImpl.g_traffic_secret (B.deref h (istate s))

(*
let g_last_packet_number (#i:index) (s:state i) (h:HS.mem)
  =
  if I.model then QModel.expected_pnT (mstate s).reader h
  else
    QImpl.g_last_packet_number (B.deref h (istate s)) h
*)

val encrypt: #i:G.erased index -> (
  let i = G.reveal i in
  s: state i ->
  dst: B.buffer U8.t ->
  dst_pn: B.pointer u62 ->
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
      (QImplBase.has_payload_length h ==> U64.v (QImplBase.payload_length h) == clen) /\
      B.length dst == U32.v (QImplBase.header_len h) + clen
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
          let pn = g_last_packet_number s h0 `U64.add` 1uL in
          B.deref h1 dst_pn == pn /\
          packet == encrypt (alg i) k iv pne (QImpl.g_header h h0 pn) plain /\
          g_last_packet_number s h1 == pn)
      | _ ->
          False))

val decrypt: #i:G.erased index -> (
  let i = G.reveal i in
  s:state i ->
  dst: B.pointer result ->
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
      B.(modifies (footprint_s h0 (deref h0 s) `loc_union`
        loc_buffer (gsub packet 0ul r.total_len) `loc_union` loc_buffer dst) h0 h1)
      | DecodeError ->
        B.modifies (footprint_s h0 (B.deref h0 s) `B.loc_union` B.loc_buffer packet) h0 h1
      | AuthenticationFailure ->
        B.(modifies (footprint_s h0 (deref h0 s) `loc_union`
        loc_buffer (gsub packet 0ul r.total_len) `loc_union` loc_buffer dst) h0 h1)
      | _ -> False
      end
    )
  )
