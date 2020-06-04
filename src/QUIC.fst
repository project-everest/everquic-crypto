module QUIC

module QSpec = QUIC.Spec
module QImpl = QUIC.State
module QImplBase = QUIC.Impl.Header.Base
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

// The switch only makes sense in the non-ideal case. (Unsurprisingly: if we
// replace data by random values, functional correctness no longer holds!)
let index =
  if I.model then i:QModel.id { QModel.unsafe i } else QImpl.index

let mid (i:index{I.model}) = i <: QModel.id
let iid (i:index{not I.model}) = i <: QImpl.index

let alg (i:index) =
  if I.model then I.ae_id_ginfo (fst (mid i))
  else (iid i).QImpl.aead_alg

let halg (i:index) =
  if I.model then I.ae_id_ghash (fst (mid i))
  else (iid i).QImpl.hash_alg

let itraffic_secret (i:QModel.id) =
  Spec.Hash.Definitions.bytes_hash (I.ae_id_ghash (fst i))

module MH = Model.Helpers

let derived (#i:QModel.id) (#w:QModel.stream_writer i) (r:QModel.stream_reader w) (ts:itraffic_secret i) =
  if I.model && QModel.unsafe i then
    let ha = I.ae_id_hash (fst i) in
    let ea = I.ae_id_info (fst i) in
    let (k1, k2) = QModel.reader_leak r in
    MH.hide (QModel.writer_static_iv w) ==
      QSpec.derive_secret ha ts QSpec.label_iv 12 /\
    MH.hide k1 == QSpec.derive_secret ha ts
        QSpec.label_key (QSpec.cipher_keysize ea) /\
    MH.hide k2 == QUIC.Spec.derive_secret ha ts
        QUIC.Spec.label_key (QSpec.cipher_keysize ea)
  else True

noeq type mstate_t i =
| Ideal:
  writer: QModel.stream_writer i ->
  reader: QModel.stream_reader writer ->
  ts: itraffic_secret i{derived reader ts} -> // FIXME erased
  mstate_t i

let istate_t i = QImpl.state i

let state i =
  if I.model then mstate_t (mid i)
  else istate_t (iid i)

let mstate (#i:index{I.model}) (s:state i) = s <: mstate_t (mid i)
let istate (#i:index{not I.model}) (s:state i) = s <: istate_t (iid i)

let footprint #i h s =
  if I.model then
    QModel.rfootprint (mstate s).reader `B.loc_union` QModel.footprint (mstate s).writer
  else QImpl.footprint h (istate s)

let invariant #i h s =
  if I.model then
    let Ideal writer reader _ = mstate s in
    QModel.invariant writer h /\ QModel.rinvariant reader h /\
    B.loc_disjoint (QModel.rfootprint (mstate s).reader) (QModel.footprint (mstate s).writer)
  else QImpl.invariant h (istate s)

let g_traffic_secret #i s h =
  if I.model then (mstate s).ts
  else
    QImpl.g_traffic_secret (B.deref h (istate s))

let g_initial_packet_number #i s h =
  assert_norm (pow2 62 - 1 < pow2 64);
  if I.model then
    Lib.IntTypes.u64 (QModel.writer_offset #(mid i) (mstate s).writer)
  else
    QImpl.g_initial_packet_number (B.deref h (istate s))

let g_last_packet_number #i s h =
  assert_norm (pow2 62 - 1 < pow2 64);
  if I.model then
    Lib.IntTypes.u64 (UInt64.v (QModel.expected_pnT #(mid i) (mstate s).reader h)) // - 1 ?
  else
    QImpl.g_last_packet_number (B.deref h (istate s)) h

// TODO: reveal in the interface (just for good measure)
let frame_invariant #i l s h0 h1 =
  if I.model then
    let Ideal w r _ = mstate #(mid i) s in
    QModel.frame_invariant w h0 l h1;
    QModel.rframe_invariant r h0 l h1
  else
    QImpl.frame_invariant #(iid i) l s h0 h1

/// Ingredients we need for the mythical switch

/// First, a stateful equivalent of as_seq. Implementation doesn't need to be
/// efficient.

let rec as_seq #a (b: B.buffer a) (l: UInt32.t { l == B.len b }): Stack (S.seq a)
  (requires fun h0 ->
    B.live h0 b)
  (ensures fun h0 r h1 ->
    h0 == h1 /\
    B.as_seq h0 b `S.equal` r)
=
  let h0 = ST.get () in
  if l = 0ul then
    S.empty
  else
    let hd = B.index b 0ul in
    let l = l `U32.sub` 1ul in
    let b = B.sub b 1ul l in
    S.cons hd (as_seq b l)

let rec from_seq #a (dst: B.buffer a) (s: S.seq a): Stack unit
  (requires fun h0 ->
    B.live h0 dst /\
    B.length dst == S.length s)
  (ensures fun h0 _ h1 ->
    B.modifies (B.loc_buffer dst) h0 h1 /\
    B.as_seq h1 dst `S.equal` s)
=
  if S.length s = 0 then
    ()
  else begin
    let hd = B.sub dst 0ul 1ul in
    let tl = B.sub dst 1ul (UInt32.uint_to_t (S.length s - 1)) in
    B.upd hd 0ul (S.index s 0);
    from_seq tl (S.slice s 1 (S.length s));
    let h1 = ST.get () in
    calc (S.equal) {
      B.as_seq h1 dst;
    (S.equal) { }
      S.append (S.slice (B.as_seq h1 hd) 0 1) (S.slice (B.as_seq h1 dst) 1 (S.length s));
    (S.equal) { }
      S.append (S.create 1 (S.index s 0)) (S.slice (B.as_seq h1 dst) 1 (S.length s));
    (S.equal) { }
      S.append (S.create 1 (S.index s 0)) (S.slice s 1 (S.length s));
    (S.equal) { }
      s;
    }
  end

#set-options "--fuel 0 --ifuel 0 --z3rlimit 200 --using_facts_from '*,-LowStar.Monotonic.Buffer.unused_in_not_unused_in_disjoint_2'"

let nat_of_u8 (x: Lib.IntTypes.uint8) =
  UInt8.v (Lib.RawIntTypes.u8_to_UInt8 x)

let reveal_bitfield #n (x: QUIC.Spec.secret_bitfield n): QUIC.Spec.bitfield n =
  Lib.RawIntTypes.u8_to_UInt8 x

let fstar_bytes_of_seq (s: S.seq UInt8.t):
  Pure FStar.Bytes.bytes
    (requires S.length s < pow2 32)
    (ensures fun b -> FStar.Bytes.reveal b `S.equal` s)
=
  assert_norm (pow2 32 = 4294967296);
  LowParse.SLow.Base.bytes_of_seq s

let as_header (h: QUIC.Impl.header) (packet_number: PN.packet_number_t) : Stack QUIC.Spec.header
  (requires fun h0 ->
    QUIC.Impl.header_live h h0)
  (ensures fun h0 r h1 ->
    h0 == h1 /\
    r == QUIC.Impl.g_header h h0 packet_number)
=
  let _ = allow_inversion QImplBase.header in
  let _ = allow_inversion QImplBase.long_header_specifics in

  let x = packet_number in
  let open QUIC.Impl in
  let open QUIC.Spec.Header.Base in
  let packet_number = x in
  match h with
  | BShort rb spin phase cid cid_len packet_number_length ->
    // Insane type errors if I don't put everything in A-normal form.
    let bar: S.seq UInt8.t = as_seq cid cid_len in
    let foo: vlbytes 0 20 = fstar_bytes_of_seq bar in
    MShort
      (reveal_bitfield rb)
      spin
      (nat_of_u8 phase = 1)
      foo
      packet_number_length packet_number
  | _ -> admit ()


(*let x = 
  | BLong version dcid dcil scid scil spec ->
    MLong version (FB.hide (B.as_seq m dcid)) (FB.hide (B.as_seq m scid))
      begin match spec with
      | BInitial rb payload_length packet_number_length token token_length ->
        MInitial (Secret.reveal rb) (FB.hide (B.as_seq m token)) payload_length packet_number_length packet_number
      | BZeroRTT rb payload_length packet_number_length ->
        MZeroRTT (Secret.reveal rb) payload_length packet_number_length packet_number
      | BHandshake rb payload_length packet_number_length ->
        MHandshake (Secret.reveal rb) payload_length packet_number_length packet_number
      | BRetry unused odcid odcil ->
        MRetry (Secret.reveal unused) (FB.hide (B.as_seq m odcid))
      end*)

let encrypt #i s dst dst_pn h plain plain_len =
  let h0 = ST.get () in
  if I.model then
    let i = i <: QModel.id in
    // A pure version of plain suitable for calling specs with. From here on,
    // this is a "magical" value that has no observable side-effects since it
    // belongs to spec-land.
    let plain_s = as_seq plain plain_len in

    let _ = allow_inversion QImplBase.header in
    let _ = allow_inversion QImplBase.long_header_specifics in

    (**) let h1 = ST.get () in

    // Yet do a "fake" call that generates the same side-effects.
    push_frame ();
    (**) let h2 = ST.get () in
    let hash_alg: QSpec.ha = I.ae_id_hash (fst i) in
    let aead_alg = I.ae_id_info (fst i) in
    let dummy_traffic_secret = B.alloca (Lib.IntTypes.u8 0) (Hacl.Hash.Definitions.hash_len hash_alg) in
    (**) let h3 = ST.get () in
    (**) B.loc_unused_in_not_unused_in_disjoint h3;
    (**) B.(modifies_only_not_unused_in loc_none h2 h3);
    // This is a dummy plaintext that only contains zeroes.
    let dummy_plain = B.alloca (Lib.IntTypes.u8 0) plain_len in
    (**) let h30 = ST.get () in
    (**) B.loc_unused_in_not_unused_in_disjoint h30;
    (**) B.(modifies_only_not_unused_in loc_none h3 h30);
    let dummy_index: QImpl.index = { QImpl.hash_alg = hash_alg; QImpl.aead_alg = aead_alg } in
    let dummy_dst = B.alloca B.null 1ul in
    (**) let h4 = ST.get () in
    (**) B.loc_unused_in_not_unused_in_disjoint h4;
    (**) B.(modifies_only_not_unused_in loc_none h30 h4);
    // This changes the side-effects between the two branches, which is
    // precisely what we're trying to avoid. We could allocate this on the stack
    // with QImpl.alloca (hence eliminating the heap allocation effect), but for
    // that we need EverCrypt.AEAD.alloca which was merged to master only two
    // days ago. So this will have to be fixed for the final version.
    let r = QImpl.create_in dummy_index HS.root dummy_dst (Lib.IntTypes.u64 0) dummy_traffic_secret in
    (**) let h5 = ST.get () in
    (**) B.loc_unused_in_not_unused_in_disjoint h5;
    (**) B.(modifies_only_not_unused_in (loc_buffer dummy_dst) h4 h5);
    (**) B.(modifies_trans loc_none h2 h4 (loc_buffer dummy_dst) h5);
    (**) assert B.(modifies (loc_buffer dummy_dst) h2 h5);
    // This is just annoying because EverCrypt still doesn't have a C fallback
    // implementation for AES-GCM so UnsupportedAlgorithm errors may be thrown
    // for one of our chosen algorithms.
    // Assuming here a C implementation of AES-GCM will eventually happen and
    // EverCrypt will allow eliminating in the post-condition the
    // UnsupportedAlgorithm case provided the user passes in an aead_alg that is
    // one of the supported ones (i.e. not one of the CCM variants, which we do
    // not use here).
    assume (r <> UnsupportedAlgorithm);
    let dummy_s = LowStar.BufferOps.(!* dummy_dst) in
    let r = QImpl.encrypt #(G.hide dummy_index) dummy_s dst dst_pn h dummy_plain plain_len in
    (**) let h6 = ST.get () in
    (**) B.loc_unused_in_not_unused_in_disjoint h6;
    (**) B.(modifies_only_not_unused_in (loc_buffer dummy_dst `loc_union` loc_buffer dst_pn `loc_union` loc_buffer dst)
      h2 h6);
    (**) assert B.(modifies (loc_buffer dummy_dst `loc_union` loc_buffer dst_pn `loc_union` loc_buffer dst) h2 h6);
    pop_frame ();

    (**) let h7 = ST.get () in
    B.(modifies_fresh_frame_popped h1 h2 (loc_buffer dst_pn `loc_union` loc_buffer dst) h6 h7);
    assert B.(modifies (loc_buffer dst_pn `loc_union` loc_buffer dst) h0 h7);

    // Now call the spec. This is pure-land, so no observable side-effects since
    // the code is not stateful.
    let Ideal writer reader traffic_secret = s <: mstate_t i in
    let last_pn = QModel.expected_pn #i reader in
    let spec_h = as_header h (Lib.RawIntTypes.u64_from_UInt64 last_pn) in
    let cipher = Model.QUIC.encrypt writer spec_h
      (UInt32.v (Lib.RawIntTypes.u32_to_UInt32 (QUIC.Spec.Header.Base.pn_length spec_h)))
      Model.QUIC.((writer_info writer).plain_pkg.mk i (S.length plain_s) (Model.Helpers.reveal plain_s)) in
    assume (S.length cipher == B.length dst);
    from_seq dst cipher;
    admit ();
    Success
  else
    let s = s <: QImpl.state i in
    QImpl.encrypt #(G.hide (i <: QImpl.index)) s dst dst_pn h plain plain_len
