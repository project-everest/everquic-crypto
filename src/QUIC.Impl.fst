module QUIC.Impl

// This MUST be kept in sync with QUIC.Impl.fsti...
module G = FStar.Ghost
module B = LowStar.Buffer
module IB = LowStar.ImmutableBuffer
module Seq = QUIC.Secret.Seq
module HS = FStar.HyperStack
module ST = FStar.HyperStack.ST


module U64 = FStar.UInt64
module U32 = FStar.UInt32
module U8 = FStar.UInt8

open FStar.HyperStack
open FStar.HyperStack.ST

open EverCrypt.Helpers
open EverCrypt.Error

module Cipher = EverCrypt.Cipher
module AEAD = EverCrypt.AEAD
module HKDF = EverCrypt.HKDF
module CTR = EverCrypt.CTR

friend QUIC.Spec

open LowStar.BufferOps

inline_for_extraction noextract
let as_cipher_alg (a: QUIC.Spec.ea): a:Spec.Agile.Cipher.cipher_alg {
  Spec.Agile.Cipher.(a == AES128 \/ a == AES256 \/ a == CHACHA20)
} =
  Spec.Agile.AEAD.cipher_alg_of_supported_alg a

/// https://tools.ietf.org/html/draft-ietf-quic-tls-23#section-5
///
/// We perform the three key derivations (AEAD key; AEAD iv; header protection
/// key) when ``create`` is called. We thus store the original traffic secret
/// only ghostly.
///
/// We retain the AEAD state, in order to perform the packet payload encryption.
///
/// We retain the Cipher state, in order to compute the mask for header protection.
noeq
type state_s (i: index) =
  | State:
      the_hash_alg:hash_alg { the_hash_alg == i.hash_alg } ->
      the_aead_alg:aead_alg { the_aead_alg == i.aead_alg } ->
      traffic_secret:G.erased (Spec.Hash.Definitions.bytes_hash the_hash_alg) ->
      initial_pn:G.erased QUIC.Spec.nat62 ->
      aead_state:EverCrypt.AEAD.state the_aead_alg ->
      iv:EverCrypt.AEAD.iv_p the_aead_alg ->
      hp_key:B.buffer U8.t { B.length hp_key = QUIC.Spec.ae_keysize the_aead_alg } ->
      pn:B.pointer PN.packet_number_t ->
      ctr_state:CTR.state (as_cipher_alg the_aead_alg) ->
      state_s i

let footprint_s #i h s =
  let open LowStar.Buffer in
  AEAD.footprint h (State?.aead_state s) `loc_union`
  CTR.footprint h (State?.ctr_state s) `loc_union`
  loc_buffer (State?.iv s) `loc_union`
  loc_buffer (State?.hp_key s) `loc_union`
  loc_buffer (State?.pn s)

let g_traffic_secret #i s =
  // Automatic reveal insertion doesn't work here
  G.reveal (State?.traffic_secret s)

let g_initial_packet_number #i s =
  // New style: automatic insertion of reveal
  State?.initial_pn s

let invariant_s #i h s =
  let open QUIC.Spec in
  let State hash_alg aead_alg traffic_secret initial_pn aead_state iv hp_key pn ctr_state =
    s in
  hash_is_keysized s; (
  AEAD.invariant h aead_state /\
  not (B.g_is_null aead_state) /\
  CTR.invariant h ctr_state /\
  not (B.g_is_null ctr_state) /\
  B.(all_live h [ buf iv; buf hp_key; buf pn ])  /\
  B.(all_disjoint [ CTR.footprint h ctr_state;
    AEAD.footprint h aead_state; loc_buffer iv; loc_buffer hp_key; loc_buffer pn ]) /\
  // JP: automatic insertion of reveal does not work here
  G.reveal initial_pn <= Secret.v (B.deref h pn) /\
  Seq.seq_reveal (AEAD.as_kv (B.deref h aead_state)) ==
    derive_secret i.hash_alg (G.reveal traffic_secret) label_key (Spec.Agile.AEAD.key_length aead_alg) /\
  Seq.seq_reveal (B.as_seq h iv) ==
    derive_secret i.hash_alg (G.reveal traffic_secret) label_iv 12 /\
  B.as_seq h hp_key ==
    derive_secret i.hash_alg (G.reveal traffic_secret) label_hp (QUIC.Spec.ae_keysize aead_alg)
  )

let invariant_loc_in_footprint #_ _ _ = ()

let g_last_packet_number #i s h =
  B.deref h (State?.pn s)

let frame_invariant #i l s h0 h1 =
  AEAD.frame_invariant l (State?.aead_state (B.deref h0 s)) h0 h1;
  CTR.frame_invariant l (State?.ctr_state (B.deref h0 s)) h0 h1

let aead_alg_of_state #i s =
  let State _ the_aead_alg _ _ _ _ _ _ _ = !*s in
  the_aead_alg

let hash_alg_of_state #i s =
  let State the_hash_alg _ _ _ _ _ _ _ _ = !*s in
  the_hash_alg

let last_packet_number_of_state #i s =
  let State _ _ _ _ _ _ _ pn _ = !*s in
  !*pn

/// Helpers & globals
/// -----------------

friend QUIC.Impl.Lemmas
open QUIC.Impl.Lemmas

inline_for_extraction noextract
let u32_of_u8 = FStar.Int.Cast.uint8_to_uint32
inline_for_extraction noextract
let u64_of_u8 = FStar.Int.Cast.uint8_to_uint64
inline_for_extraction noextract
let u64_of_u32 = FStar.Int.Cast.uint32_to_uint64

let key_len (a: QUIC.Spec.ea): x:U8.t { U8.v x = Spec.Agile.AEAD.key_length a } =
  let open Spec.Agile.AEAD in
  match a with
  | AES128_GCM -> 16uy
  | AES256_GCM -> 32uy
  | CHACHA20_POLY1305 -> 32uy

let key_len32 a = FStar.Int.Cast.uint8_to_uint32 (key_len a)

#push-options "--warn_error -272"
let label_key = LowStar.ImmutableBuffer.igcmalloc_of_list HS.root QUIC.Spec.label_key_l
let label_iv = LowStar.ImmutableBuffer.igcmalloc_of_list HS.root QUIC.Spec.label_iv_l
let label_hp = LowStar.ImmutableBuffer.igcmalloc_of_list HS.root QUIC.Spec.label_hp_l
let prefix = LowStar.ImmutableBuffer.igcmalloc_of_list HS.root QUIC.Spec.prefix_l
#pop-options

/// Actual code
/// -----------

#push-options "--z3rlimit 200"
inline_for_extraction noextract
let op_inplace (dst: B.buffer U8.t)
  (dst_len: U32.t)
  (src: B.buffer U8.t)
  (src_len: U32.t)
  (ofs: U32.t)
  (op: U8.t -> U8.t -> U8.t)
:
  Stack unit
    (requires fun h0 ->
      B.(all_live h0 [ buf dst; buf src ]) /\
      B.disjoint dst src /\
      B.length src = U32.v src_len /\
      B.length dst = U32.v dst_len /\
      B.length dst >= U32.v ofs + B.length src)
    (ensures fun h0 _ h1 ->
      B.(modifies (loc_buffer dst) h0 h1) /\
      B.as_seq h1 dst `Seq.equal`
        QUIC.Spec.Lemmas.pointwise_op op (B.as_seq h0 dst) (B.as_seq h0 src) (U32.v ofs) /\
      Seq.slice (B.as_seq h0 dst) 0 (U32.v ofs) `Seq.equal`
        Seq.slice (B.as_seq h1 dst) 0 (U32.v ofs) /\
      Seq.slice (B.as_seq h0 dst) (U32.v (ofs `U32.add` src_len)) (U32.v dst_len) `Seq.equal`
      Seq.slice (B.as_seq h1 dst) (U32.v (ofs `U32.add` src_len)) (U32.v dst_len))
=
  let h0 = ST.get () in
  let dst0 = B.sub dst 0ul ofs in
  let dst1 = B.sub dst ofs src_len in
  let dst2 = B.sub dst (ofs `U32.add` src_len) (dst_len `U32.sub` (ofs `U32.add` src_len)) in
  C.Loops.in_place_map2 dst1 src src_len op;
  let h1 = ST.get () in
  calc (Seq.equal) {
    B.as_seq h1 dst;
  (Seq.equal) { lemma_slice3 (B.as_seq h1 dst) (U32.v ofs) (U32.v (ofs `U32.add` src_len)) }
    Seq.slice (B.as_seq h1 dst) 0 (U32.v ofs) `Seq.append`
    (Seq.slice (B.as_seq h1 dst) (U32.v ofs) (U32.v (ofs `U32.add` src_len))) `Seq.append`
    (Seq.slice (B.as_seq h1 dst) (U32.v (ofs `U32.add` src_len)) (B.length dst));
  (Seq.equal) {}
    Seq.slice (B.as_seq h0 dst) 0 (U32.v ofs) `Seq.append`
    (Seq.slice (B.as_seq h1 dst) (U32.v ofs) (U32.v (ofs `U32.add` src_len))) `Seq.append`
    (Seq.slice (B.as_seq h0 dst) (U32.v (ofs `U32.add` src_len)) (B.length dst));
  (Seq.equal) { pointwise_seq_map2 op (B.as_seq h0 dst1) (B.as_seq h0 src) 0 }
    Seq.slice (B.as_seq h0 dst) 0 (U32.v ofs) `Seq.append`
    (QUIC.Spec.Lemmas.pointwise_op op
      (Seq.slice (B.as_seq h0 dst) (U32.v ofs) (U32.v (ofs `U32.add` src_len)))
      (B.as_seq h0 src)
      0) `Seq.append`
    (Seq.slice (B.as_seq h0 dst) (U32.v (ofs `U32.add` src_len)) (B.length dst));
  (Seq.equal) { QUIC.Spec.Lemmas.pointwise_op_suff op (Seq.slice (B.as_seq h0 dst) 0 (U32.v ofs))
    (Seq.slice (B.as_seq h0 dst) (U32.v ofs) (U32.v (ofs `U32.add` src_len)))
    (B.as_seq h0 src)
    (U32.v ofs) }
    QUIC.Spec.Lemmas.pointwise_op op
      (Seq.append (Seq.slice (B.as_seq h0 dst) 0 (U32.v ofs))
        (Seq.slice (B.as_seq h0 dst) (U32.v ofs) (U32.v (ofs `U32.add` src_len))))
      (B.as_seq h0 src)
      (U32.v ofs) `Seq.append`
    (Seq.slice (B.as_seq h0 dst) (U32.v (ofs `U32.add` src_len)) (B.length dst));
  (Seq.equal) { lemma_slice1 (B.as_seq h0 dst) (U32.v ofs) (U32.v (ofs `U32.add` src_len)) }
    QUIC.Spec.Lemmas.pointwise_op op
      (Seq.slice (B.as_seq h0 dst) 0 (U32.v (ofs `U32.add` src_len)))
      (B.as_seq h0 src)
      (U32.v ofs) `Seq.append`
    (Seq.slice (B.as_seq h0 dst) (U32.v (ofs `U32.add` src_len)) (B.length dst));
  (Seq.equal) { QUIC.Spec.Lemmas.pointwise_op_pref op
    (Seq.slice (B.as_seq h0 dst) 0 (U32.v (ofs `U32.add` src_len)))
    (Seq.slice (B.as_seq h0 dst) (U32.v (ofs `U32.add` src_len)) (B.length dst))
    (B.as_seq h0 src)
    (U32.v ofs)
  }
    QUIC.Spec.Lemmas.pointwise_op op
      (Seq.slice (B.as_seq h0 dst) 0 (U32.v (ofs `U32.add` src_len)) `Seq.append`
      (Seq.slice (B.as_seq h0 dst) (U32.v (ofs `U32.add` src_len)) (B.length dst)))
      (B.as_seq h0 src)
      (U32.v ofs);
  (Seq.equal) { lemma_slice (B.as_seq h0 dst) (U32.v (ofs `U32.add` src_len)) }
    QUIC.Spec.Lemmas.pointwise_op op
      (B.as_seq h0 dst)
      (B.as_seq h0 src)
      (U32.v ofs);
  }

#push-options "--max_ifuel 1 --initial_ifuel 1"
/// One ifuel for inverting on the hash algorithm for computing bounds (the
/// various calls to assert_norm should help ensure this proof goes through
/// reliably). Note that I'm breaking from the usual convention where lengths
/// are UInt32's, mostly to avoid trouble reasoning with modulo when casting
/// from UInt32 to UInt8 to write the label for the key derivation. This could
/// be fixed later.
val derive_secret: a: QUIC.Spec.ha ->
  dst:B.buffer U8.t ->
  dst_len: U8.t { B.length dst = U8.v dst_len /\ U8.v dst_len <= 255 } ->
  secret:B.buffer U8.t { B.length secret = Spec.Hash.Definitions.hash_length a } ->
  label:IB.ibuffer U8.t ->
  label_len:U8.t { IB.length label = U8.v label_len /\ U8.v label_len <= 244 } ->
  Stack unit
    (requires fun h0 ->
      B.(all_live h0 [ buf secret; buf label; buf dst ]) /\
      B.disjoint dst secret)
    (ensures fun h0 _ h1 ->
      assert_norm (255 < pow2 61);
      assert_norm (pow2 61 < pow2 125);
      B.(modifies (loc_buffer dst) h0 h1) /\
      B.as_seq h1 dst == QUIC.Spec.derive_secret a (Seq.seq_hide (B.as_seq h0 secret))
        (IB.as_seq h0 label) (U8.v dst_len))
#pop-options

#push-options "--z3rlimit 100"
let derive_secret a dst dst_len secret label label_len =
  LowStar.ImmutableBuffer.recall prefix;
  LowStar.ImmutableBuffer.recall_contents prefix QUIC.Spec.prefix;
  (**) let h0 = ST.get () in

  push_frame ();
  (**) let h1 = ST.get () in

  let label_len32 = FStar.Int.Cast.uint8_to_uint32 label_len in
  let dst_len32 = FStar.Int.Cast.uint8_to_uint32 dst_len in
  let info_len = U32.(1ul +^ 1ul +^ 1ul +^ 11ul +^ label_len32 +^ 1ul) in
  let info = B.alloca 0uy info_len in

  // JP: best way to reason about this sort of code is to slice the buffer very thinly
  let info_z = B.sub info 0ul 1ul in
  let info_lb = B.sub info 1ul 1ul in
  let info_llen = B.sub info 2ul 1ul in
  let info_prefix = B.sub info 3ul 11ul in
  let info_label = B.sub info 14ul label_len32 in
  let info_z' = B.sub info (14ul `U32.add` label_len32) 1ul in
  (**) assert (14ul `U32.add` label_len32 `U32.add` 1ul = B.len info);
  (**) assert B.(all_disjoint [ loc_buffer info_z; loc_buffer info_lb; loc_buffer info_llen;
  (**)   loc_buffer info_prefix; loc_buffer info_label; loc_buffer info_z' ]);

  info_lb.(0ul) <- dst_len;
  info_llen.(0ul) <- U8.(label_len +^ 11uy);
  B.blit prefix 0ul info_prefix 0ul 11ul;
  B.blit label 0ul info_label 0ul label_len32;

  (**) let h2 = ST.get () in
  (**) assert (
  (**)   let z = Seq.create 1 0uy in
  (**)   let lb = Seq.create 1 dst_len in // len <= 255
  (**)   let llen = Seq.create 1 (U8.uint_to_t (11 + Seq.length (B.as_seq h0 label))) in
  (**)   let info = B.as_seq h2 info in
  (**)   B.as_seq h2 info_z `Seq.equal` z /\
  (**)   B.as_seq h2 info_lb `Seq.equal` lb /\
  (**)   B.as_seq h2 info_llen `Seq.equal` llen /\
  (**)   B.as_seq h2 info_prefix `Seq.equal` QUIC.Spec.prefix /\
  (**)   B.as_seq h2 info_label `Seq.equal` (B.as_seq h0 label) /\
  (**)   B.as_seq h2 info_z' `Seq.equal` z
  (**) );
  (**) (
  (**)   let z = Seq.create 1 0uy in
  (**)   let lb = Seq.create 1 dst_len in // len <= 255
  (**)   let llen = Seq.create 1 (U8.uint_to_t (11 + Seq.length (B.as_seq h0 label))) in
  (**)   let info = B.as_seq h2 info in
  (**)   lemma_five_cuts info 1 2 3 14 (14 + U8.v label_len)
  (**)     z lb llen QUIC.Spec.prefix (B.as_seq h0 label) z
  (**) );
  (**) hash_is_keysized_ a;
  assume False;
  HKDF.expand a dst secret (Hacl.Hash.Definitions.hash_len a) info info_len dst_len32;
  (**) let h3 = ST.get () in
  pop_frame ();
  (**) let h4 = ST.get () in
  (**) B.modifies_fresh_frame_popped h0 h1 (B.loc_buffer dst) h3 h4;
  (**) assert (ST.equal_domains h0 h4)
#pop-options

/// For functions that perform allocations, or even functions that need
/// temporary state, a style we adopt here is to write the core (i.e. what would
/// normally go in-between push and pop frame) as a separate function. If
/// needed, the core of the function takes its temporary allocations as
/// parameters, and reasons abstractly against a region where the temporary
/// allocations live. This gives significantly better proof performance.
///
/// Another bit of style: after every stateful operation, we restore manually:
/// the modifies clause (going directly for the one we want); the invariant; the
/// footprint preservation; then the functional correctness propertise we are
/// seeking.

val create_in_core:
  i:index ->
  r:HS.rid ->
  dst: B.pointer (B.pointer_or_null (state_s i)) ->
  initial_pn:u62 ->
  traffic_secret:B.buffer U8.t {
    B.length traffic_secret = Spec.Hash.Definitions.hash_length i.hash_alg
  } ->
  aead_state:AEAD.state i.aead_alg ->
  ctr_state:CTR.state (as_cipher_alg i.aead_alg) ->
  ST unit
    (requires fun h0 ->
      QUIC.Impl.Lemmas.hash_is_keysized_ i.hash_alg; (
      ST.is_eternal_region r /\
      B.live h0 dst /\ B.live h0 traffic_secret /\
      B.(all_disjoint [ AEAD.footprint h0 aead_state; CTR.footprint h0 ctr_state;
        loc_buffer dst; loc_buffer traffic_secret ]) /\
      B.(loc_includes (loc_region_only true r) (AEAD.footprint h0 aead_state)) /\
      B.(loc_includes (loc_region_only true r) (CTR.footprint h0 ctr_state)) /\

      // Whatever from the invariant ought to be established already.
      AEAD.invariant h0 aead_state /\
      not (B.g_is_null aead_state) /\
      CTR.invariant h0 ctr_state /\
      not (B.g_is_null ctr_state) /\
      Seq.seq_reveal (AEAD.as_kv (B.deref h0 aead_state)) ==
        QUIC.Spec.(derive_secret i.hash_alg (Seq.seq_hide (B.as_seq h0 traffic_secret)) label_key
          (Spec.Agile.AEAD.key_length i.aead_alg))))
    (ensures (fun h0 _ h1 ->
      let s = B.deref h1 dst in
      not (B.g_is_null s) /\
      invariant h1 s /\

      B.(modifies (loc_buffer dst) h0 h1) /\ (
      let State _ _ _ initial_pn' aead_state' iv' hp_key' pn' ctr_state' = B.deref h1 s in
      aead_state' == aead_state /\
      ctr_state' == ctr_state /\
      B.(fresh_loc (loc_buffer iv') h0 h1) /\
      B.(fresh_loc (loc_buffer hp_key') h0 h1) /\
      B.(fresh_loc (loc_buffer pn') h0 h1) /\
      B.(fresh_loc (loc_addr_of_buffer s) h0 h1) /\

      G.reveal initial_pn' == U64.v initial_pn)))

#push-options "--z3rlimit 50"
let create_in_core i r dst initial_pn traffic_secret aead_state ctr_state =
  LowStar.ImmutableBuffer.recall label_key;
  LowStar.ImmutableBuffer.recall_contents label_key QUIC.Spec.label_key;
  LowStar.ImmutableBuffer.recall label_iv;
  LowStar.ImmutableBuffer.recall_contents label_iv QUIC.Spec.label_iv;
  LowStar.ImmutableBuffer.recall label_hp;
  LowStar.ImmutableBuffer.recall_contents label_hp QUIC.Spec.label_hp;

  (**) let h0 = ST.get () in
  (**) assert_norm FStar.Mul.(8 * 12 <= pow2 64 - 1);

  // The modifies clauses that we will transitively carry across this function body.
  let mloc = G.hide (B.(loc_buffer dst `loc_union` loc_unused_in h0)) in
  let e_traffic_secret: G.erased (Spec.Hash.Definitions.bytes_hash i.hash_alg) =
    G.hide (Seq.seq_hide #Secret.U8 (B.as_seq h0 traffic_secret)) in
  let e_initial_pn: G.erased QUIC.Spec.nat62 = G.hide (U64.v initial_pn) in

  assume False;
  let iv = B.malloc r 0uy 12ul in
  let hp_key = B.malloc r 0uy (key_len32 i.aead_alg) in
  let pn = B.malloc r initial_pn 1ul in
  (**) let h1 = ST.get () in
  (**) B.(modifies_loc_includes (G.reveal mloc) h0 h1 loc_none);
  (**) assert (B.length hp_key = QUIC.Spec.ae_keysize i.aead_alg);

  let s: state_s i = State #i
    i.hash_alg i.aead_alg e_traffic_secret e_initial_pn
    aead_state iv hp_key pn ctr_state
  in

  let s:B.pointer_or_null (state_s i) = B.malloc r s 1ul in
  (**) let h2 = ST.get () in
  (**) B.(modifies_loc_includes (G.reveal mloc) h1 h2 loc_none);
  (**) B.(modifies_trans (G.reveal mloc) h0 h1 (G.reveal mloc) h2);

  derive_secret i.hash_alg iv 12uy traffic_secret label_iv 2uy;
  (**) let h3 = ST.get () in
  (**) B.(modifies_loc_includes (G.reveal mloc) h2 h3 (loc_buffer iv));
  (**) B.(modifies_trans (G.reveal mloc) h0 h2 (G.reveal mloc) h3);

  derive_secret i.hash_alg hp_key (key_len i.aead_alg) traffic_secret label_hp 2uy;
  (**) let h4 = ST.get () in
  (**) B.(modifies_loc_includes (G.reveal mloc) h3 h4 (loc_buffer hp_key));
  (**) B.(modifies_trans (G.reveal mloc) h0 h3 (G.reveal mloc) h4);

  dst *= s;
  (**) let h5 = ST.get () in
  (**) B.(modifies_loc_includes (G.reveal mloc) h4 h5 (loc_buffer dst));
  (**) B.(modifies_trans (G.reveal mloc) h0 h4 (G.reveal mloc) h5);
  (**) B.(modifies_only_not_unused_in (loc_buffer dst) h0 h5)
#pop-options

#push-options "--z3rlimit 256"
let create_in i r dst initial_pn traffic_secret =
  LowStar.ImmutableBuffer.recall label_key;
  LowStar.ImmutableBuffer.recall_contents label_key QUIC.Spec.label_key;

  (**) let h0 = ST.get () in

  push_frame ();
  (**) let h1 = ST.get () in
  let mloc = G.hide (B.(loc_region_only true (HS.get_tip h1) `loc_union` loc_buffer dst
    `loc_union` loc_unused_in h0)) in

  let aead_key = B.alloca 0uy (key_len32 i.aead_alg) in
  let aead_state: B.pointer (B.pointer_or_null (AEAD.state_s i.aead_alg)) =
    B.alloca B.null 1ul in
  let ctr_state: B.pointer (B.pointer_or_null (CTR.state_s (as_cipher_alg i.aead_alg))) =
    B.alloca (B.null #(CTR.state_s (as_cipher_alg i.aead_alg))) 1ul in
  assume False;
  let dummy_iv = B.alloca 0uy 12ul in

  (**) let h2 = ST.get () in
  (**) B.(modifies_loc_includes (G.reveal mloc) h1 h2 (loc_none));

  derive_secret i.hash_alg aead_key (key_len i.aead_alg) traffic_secret label_key 3uy;
  (**) let h3 = ST.get () in
  (**) B.(modifies_loc_includes (G.reveal mloc) h2 h3 (loc_buffer aead_key));
  (**) B.(modifies_trans (G.reveal mloc) h1 h2 (G.reveal mloc) h3);

  let ret = AEAD.create_in #i.aead_alg r aead_state aead_key in
  (**) let h4 = ST.get () in
  (**) B.(modifies_loc_includes (G.reveal mloc) h3 h4 (loc_buffer aead_state));
  (**) B.(modifies_trans (G.reveal mloc) h1 h3 (G.reveal mloc) h4);

  let ret' = CTR.create_in (as_cipher_alg i.aead_alg) r ctr_state aead_key dummy_iv 12ul 0ul in
  (**) let h5 = ST.get () in
  (**) B.(modifies_loc_includes (G.reveal mloc) h4 h5 (loc_buffer ctr_state));
  (**) B.(modifies_trans (G.reveal mloc) h1 h4 (G.reveal mloc) h5);
  (**) B.(modifies_only_not_unused_in B.(loc_region_only true (HS.get_tip h1) `loc_union` loc_buffer dst) h1 h5);

  match ret with
  | UnsupportedAlgorithm ->
      pop_frame ();
      (**) let h6 = ST.get () in
      (**) B.(modifies_fresh_frame_popped h0 h1 (loc_buffer dst) h5 h6);
      UnsupportedAlgorithm

  | Success ->

  match ret' with
  | UnsupportedAlgorithm ->
      pop_frame ();
      (**) let h6 = ST.get () in
      (**) B.(modifies_fresh_frame_popped h0 h1 (loc_buffer dst) h5 h6);
      UnsupportedAlgorithm

  | Success ->

      let aead_state: AEAD.state i.aead_alg = !*aead_state in
      (**) assert (AEAD.invariant h5 aead_state);

      let ctr_state: CTR.state (as_cipher_alg i.aead_alg) = !*ctr_state in
      (**) assert (CTR.invariant h5 ctr_state);

      create_in_core i r dst initial_pn traffic_secret aead_state ctr_state;
      (**) let h6 = ST.get () in

      (**) B.(modifies_loc_includes
        (loc_region_only true (HS.get_tip h1) `loc_union` loc_buffer dst) h5 h6
        (loc_buffer dst));
      (**) B.(modifies_trans
        (loc_region_only true (HS.get_tip h1) `loc_union` loc_buffer dst)
        h1 h5
        (loc_region_only true (HS.get_tip h1) `loc_union` loc_buffer dst)
        h6);

      pop_frame ();
      (**) let h7 = ST.get () in
      (**) B.(modifies_fresh_frame_popped h0 h1 (loc_buffer dst) h6 h7);
      (**) frame_invariant (B.loc_region_only false (HS.get_tip h6)) (B.deref h7 dst) h6 h7;

      Success
#pop-options

//module HeaderS = QUIC.Spec.Header
//module HeaderI = QUIC.Impl.Header

let block_len (a: Spec.Agile.Cipher.cipher_alg):
  x:U32.t { U32.v x = Spec.Agile.Cipher.block_length a }
=
  let open Spec.Agile.Cipher in
  match a with | CHACHA20 -> 64ul | _ -> 16ul

let encrypt
  #i s dst dst_pn h plain plain_len
= assume False;
  UnsupportedAlgorithm

(*
#push-options "--z3rlimit 256"
inline_for_extraction
let block_of_sample (a: Spec.Agile.Cipher.cipher_alg)
  (dst: B.buffer U8.t)
  (s: CTR.state a)
  (k: B.buffer U8.t)
  (sample: B.buffer U8.t):
  Stack unit
    (requires fun h0 ->
      B.(all_live h0 [ buf dst; buf k; buf sample ]) /\
      CTR.invariant h0 s /\
      B.(all_disjoint
        [ CTR.footprint h0 s; loc_buffer dst; loc_buffer k; loc_buffer sample ]) /\
      Spec.Agile.Cipher.(a == AES128 \/ a == AES256 \/ a == CHACHA20) /\
      B.length k = Spec.Agile.Cipher.key_length a /\
      B.length dst = 16 /\
      B.length sample = 16)
    (ensures fun h0 _ h1 ->
      B.(modifies (loc_buffer dst `loc_union` CTR.footprint h0 s) h0 h1) /\
      B.as_seq h1 dst `Seq.equal`
        QUIC.Spec.block_of_sample a (B.as_seq h0 k) (B.as_seq h0 sample) /\
      CTR.footprint h0 s == CTR.footprint h1 s /\
      CTR.invariant h1 s)
=
  push_frame ();
  (**) let h0 = ST.get () in
  let zeroes = B.alloca 0uy (block_len a) in
  let dst_block = B.alloca 0uy (block_len a) in
  begin match a with
  | Spec.Agile.Cipher.CHACHA20 ->
      let ctr = LowStar.Endianness.load32_le (B.sub sample 0ul 4ul) in
      let iv = B.sub sample 4ul 12ul in
      (**) let h1 = ST.get () in
      CTR.init (G.hide a) s k iv 12ul ctr;
      CTR.update_block (G.hide a) s dst_block zeroes;
      (**) let h2 = ST.get () in
      (**) seq_map2_xor0 (B.as_seq h1 dst_block)
      (**)   (Spec.Agile.Cipher.ctr_block a (B.as_seq h0 k) (B.as_seq h1 iv) (U32.v ctr));
      (**) assert (B.as_seq h2 dst_block `Seq.equal`
      (**)   Spec.Agile.Cipher.ctr_block a (B.as_seq h0 k) (B.as_seq h1 iv) (U32.v ctr));
      let dst_slice = B.sub dst_block 0ul 16ul in
      (**) assert (B.as_seq h2 dst_slice `Seq.equal` Seq.slice (
      (**)   Spec.Agile.Cipher.ctr_block a (B.as_seq h0 k) (B.as_seq h1 iv) (U32.v ctr)
      (**) ) 0 16);
      B.blit dst_slice 0ul dst 0ul 16ul
  | _ ->
      let ctr = LowStar.Endianness.load32_be (B.sub sample 12ul 4ul) in
      let iv = B.sub sample 0ul 12ul in
      (**) let h1 = ST.get () in
      CTR.init (G.hide a) s k iv 12ul ctr;
      CTR.update_block (G.hide a) s dst_block zeroes;
      (**) let h2 = ST.get () in
      (**) seq_map2_xor0 (B.as_seq h1 dst_block)
      (**)   (Spec.Agile.Cipher.ctr_block a (B.as_seq h0 k) (B.as_seq h1 iv) (U32.v ctr));
      (**) assert (B.as_seq h2 dst_block `Seq.equal`
      (**)   Spec.Agile.Cipher.ctr_block a (B.as_seq h0 k) (B.as_seq h1 iv) (U32.v ctr));
      let dst_slice = B.sub dst_block 0ul 16ul in
      (**) assert (B.as_seq h2 dst_slice `Seq.equal` Seq.slice (
      (**)   Spec.Agile.Cipher.ctr_block a (B.as_seq h0 k) (B.as_seq h1 iv) (U32.v ctr)
      (**) ) 0 16);
      B.blit dst_slice 0ul dst 0ul 16ul

  end;
  pop_frame ()
#pop-options

inline_for_extraction
noextract
let pn_sizemask (dst: B.buffer U8.t) (pn_len: u2): Stack unit
  (requires fun h0 ->
    B.live h0 dst /\ B.length dst = 4)
  (ensures fun h0 _ h1 ->
    B.as_seq h1 dst `Seq.equal` QUIC.Spec.pn_sizemask_ct (U8.v pn_len) /\
    B.(modifies (loc_buffer dst) h0 h1))
= let open FStar.Mul in
  [@ inline_let ]
  let pn_len32 = FStar.Int.Cast.uint8_to_uint32 pn_len in
  assert (U32.v pn_len32 = U8.v pn_len);
  assert_norm (0xffffffff = pow2 32 - 1);
  assert (24 - 8 * U32.v pn_len32 < 32);
  assert (24 - 8 * U32.v pn_len32 >= 0);
  FStar.UInt.shift_left_value_lemma #32 1 (24 - 8 * U32.v pn_len32);
  FStar.Math.Lemmas.pow2_lt_compat 32 (24 - 8 * U32.v pn_len32);
  FStar.Math.Lemmas.modulo_lemma (pow2 (24 - 8 * U32.v pn_len32)) (pow2 32);
  assert (U32.(v (1ul <<^ (24ul -^ 8ul *^ pn_len32))) = pow2 (24 - 8 * U32.v pn_len32));
  LowStar.Endianness.store32_be dst
    U32.(0xfffffffful -^ (1ul <<^ (24ul -^ 8ul *^ pn_len32)) +^ 1ul)

let g_hp_key #i h (s: state i) =
  B.as_seq h (State?.hp_key (B.deref h s))

unfold
let header_encrypt_pre
  (i: index)
  (dst:B.buffer U8.t)
  (dst_len: U32.t)
  (s:state i)
  (h:header)
  (cipher:G.erased (QUIC.Spec.cbytes' (is_retry h)))
  (pn: u62)
  (h0: HS.mem)
=
  let h_len = HeaderS.header_len (g_header h h0 pn) in

  // Administrative: memory
  B.(all_live h0 [ buf dst; buf s ]) /\
  invariant h0 s /\
  B.(all_disjoint [ footprint h0 s; loc_buffer dst; header_footprint h ]) /\
  header_live h h0 /\

  // Administrative: lengths
  U32.v dst_len == B.length dst /\
  B.length dst == h_len + Seq.length (G.reveal cipher) /\ (

  // ``dst`` contains formatted header + ciphertext
  let h_seq = Seq.slice (B.as_seq h0 dst) 0 h_len in
  let c = Seq.slice (B.as_seq h0 dst) h_len (B.length dst) in
  h_seq `Seq.equal` HeaderS.format_header (g_header h h0 pn) /\
  c `Seq.equal` G.reveal cipher)

val header_encrypt: i:G.erased index -> (
  let i = G.reveal i in
  dst:B.buffer U8.t ->
  dst_len: U32.t ->
  s:state i ->
  h:header ->
  cipher:G.erased (QUIC.Spec.cbytes' (is_retry h)) ->
  pn: u62 ->
  Stack unit
    (requires header_encrypt_pre i dst dst_len s h cipher pn)
    (ensures fun h0 _ h1 ->
      B.(modifies (loc_buffer dst `loc_union` footprint_s #i h0 (B.deref h0 s)) h0 h1) /\
      B.as_seq h1 dst `Seq.equal`
        QUIC.Spec.header_encrypt_ct i.aead_alg (g_hp_key h0 s) (g_header h h0 pn)
          (G.reveal cipher) /\
      invariant h1 s /\
      footprint_s h0 (B.deref h0 s) == footprint_s h1 (B.deref h1 s)))

module BF = LowParse.BitFields

#push-options "--z3rlimit 2048 --using_facts_from '*,-LowStar.Monotonic.Buffer.unused_in_not_unused_in_disjoint_2' --max_ifuel 0 --initial_ifuel 0"
let header_encrypt i dst dst_len s h cipher pn =
  let State _ aead_alg _ _ aead_state _ k _ ctr_state = !*s in
  [@inline_let]
  let u32_of_u8 = FStar.Int.Cast.uint8_to_uint32 in
  (**) let h0  = ST.get () in

  if is_retry h
  then ()
  else begin
    (**) assert (B.length dst >= 4);
    let pn_offset = HeaderI.pn_offset h (Ghost.hide pn) in
    let pn_len = pn_length h `U32.sub` 1ul in
    let h_len = HeaderI.header_len h in
    HeaderI.header_len_correct h h0 pn;
    let c = B.sub dst h_len (dst_len `U32.sub` h_len) in
    let sample = B.sub c (3ul `U32.sub` pn_len) 16ul in
    (**) assert (U32.v h_len = HeaderS.header_len (g_header h h0 pn));
    (**) assert (U32.v dst_len = U32.v h_len + Seq.length (G.reveal cipher));
    (**) lemma_slice (B.as_seq h0 dst) (U32.v h_len);
    (**) assert (B.as_seq h0 c `Seq.equal` G.reveal cipher);
    (**) assert (B.as_seq h0 sample `Seq.equal`
    (**)   Seq.slice (G.reveal cipher) (3 - U32.v pn_len) (19 - U32.v pn_len));

    push_frame ();
    let h08 = ST.get () in
    frame_header h pn B.loc_none h0 h08;
    header_live_loc_not_unused_in_footprint h h08;
    B.loc_unused_in_not_unused_in_disjoint h08;
    let mask = B.alloca 0uy 16ul in
    assert (header_footprint h `B.loc_disjoint` B.loc_buffer mask);
    let h09 = ST.get () in
    frame_header h pn B.loc_none h08 h09;
    header_live_loc_not_unused_in_footprint h h09;
    B.loc_unused_in_not_unused_in_disjoint h09;
    let pn_mask = B.alloca 0uy 4ul in
    assert (header_footprint h `B.loc_disjoint` B.loc_buffer pn_mask);
    (**) let h1 = ST.get () in
    (**) assert (B.(loc_disjoint (loc_buffer pn_mask) (footprint h1 s)));
    (**) assert (B.(all_live h1 [ buf mask; buf k; buf sample ]));

    (**) assert (CTR.invariant h1 ctr_state);
    (**) assert (invariant h1 s);
    (**) assert (B.(all_disjoint
      [ CTR.footprint h1 ctr_state; loc_buffer k ]));

    block_of_sample (as_cipher_alg aead_alg) mask ctr_state k sample;
    (**) let h2 = ST.get () in
    (**) assert (CTR.footprint h1 ctr_state == CTR.footprint h2 ctr_state);
    (**) assert (AEAD.footprint h1 aead_state == AEAD.footprint h2 aead_state);

    pn_sizemask pn_mask (FStar.Int.Cast.uint32_to_uint8 pn_len);
    (**) let h3 = ST.get () in
    (**) frame_invariant B.(loc_buffer pn_mask) s h2 h3;

    let sub_mask = B.sub mask 1ul 4ul in
    (**) assert (B.as_seq h3 sub_mask `Seq.equal` Seq.slice (B.as_seq h3 mask) 1 5);
    op_inplace pn_mask 4ul sub_mask 4ul 0ul U8.logand;
    (**) pointwise_seq_map2 U8.logand (B.as_seq h3 pn_mask) (B.as_seq h3 sub_mask) 0;
    (**) and_inplace_commutative (B.as_seq h3 pn_mask) (B.as_seq h3 sub_mask);
    (**) pointwise_seq_map2 U8.logand (B.as_seq h3 sub_mask) (B.as_seq h3 pn_mask) 0;
    (**) let h4 = ST.get () in
    (**) frame_invariant B.(loc_buffer pn_mask) s h3 h4;
    (**) assert (invariant h4 s);
    (**) assert (B.(loc_disjoint (footprint h4 s) (loc_buffer dst)));
    let f = dst.(0ul) in
    let fmask = mask.(0ul) in
    let f' =
      if BShort? h
      then BF.(uint8.set_bitfield) f 0 5 (BF.(uint8.get_bitfield) (f `U8.logxor` fmask) 0 5)
      else BF.(uint8.set_bitfield) f 0 4 (BF.(uint8.get_bitfield) (f `U8.logxor` fmask) 0 4)
    in
    op_inplace dst dst_len pn_mask 4ul pn_offset U8.logxor;
    (**) let h5 = ST.get () in
    (**) frame_invariant B.(loc_buffer dst) s h4 h5;
    (**) assert (invariant h5 s);

    dst.(0ul) <- f' ;
    (**) let h6 = ST.get () in
    (**) frame_invariant B.(loc_buffer dst) s h5 h6;
    (**) assert (invariant h6 s);
    (**) upd_op_inplace U8.logxor (B.as_seq h5 dst) fmask;

//    assert (
//      B.as_seq h6 dst `Seq.equal`
//        QUIC.Spec.header_encrypt_ct i.aead_alg (g_hp_key h0 s) (g_header h h0 pn)
//          (G.reveal cipher)
//    );

(*    
    assert (
      let the_npn = npn in
      let open QUIC.Spec in
      let a = aead_alg in
      let k = B.as_seq h0 k in
      let h = g_header h h0 pn in
      let npn = B.as_seq h0 the_npn in
      let c = G.reveal cipher in
      B.as_seq h6 dst `Seq.equal` QUIC.Spec.header_encrypt aead_alg k h c);
*)
    pop_frame ();
    (**) let h7 = ST.get () in
    ()
  end

#pop-options

let tag_len (a: QUIC.Spec.ea): x:U32.t { U32.v x = Spec.Agile.AEAD.tag_length a /\ U32.v x = 16} =
  let open Spec.Agile.AEAD in
  match a with
  | CHACHA20_POLY1305 -> 16ul
  | AES128_GCM        -> 16ul
  | AES256_GCM        -> 16ul

(*
inline_for_extraction
let tricky_addition (aead_alg: QUIC.Spec.ea) (h: header) (pn_len: u2) (pn: u62) (plain_len: U32.t {
    3 <= U32.v plain_len /\
    U32.v plain_len < QUIC.Spec.max_plain_length
  }):
  Stack U32.t
    (requires fun h0 -> header_live h h0)
    (ensures fun h0 x h1 ->
      h0 == h1 /\
      U32.v x = HeaderS.header_len (g_header h h0 pn) + U32.v plain_len +
        Spec.Agile.AEAD.tag_length aead_alg)
=
  HeaderI.header_len h `U32.add` plain_len `U32.add` tag_len aead_alg
*)

open FStar.Mul

#push-options "--z3rlimit 32"

unfold
let encrypt_core_pre
  (#gi:G.erased index)
  (s:state (G.reveal gi))
  (dst:B.buffer U8.t)
  (h:header)
  (plain: B.buffer U8.t)
  (plain_len: U32.t {
    B.length plain = U32.v plain_len
  })
  (stack: G.erased B.loc)
  (this_iv:B.buffer U8.t)
  (bpn12: B.lbuffer U8.t 12)
  (h0: HS.mem)
: Tot Type0
= let i = G.reveal gi in
  assert_norm (pow2 62 < pow2 (8 * 12));
  let stack = G.reveal stack in
  // Memory & preservation
  B.(all_live h0 [ buf dst; buf plain; buf this_iv; buf bpn12 ]) /\
  header_live h h0 /\
  B.(all_disjoint [ stack; footprint h0 s; loc_buffer dst;
    header_footprint h; loc_buffer plain ]) /\
  B.loc_disjoint (B.loc_buffer this_iv) (B.loc_buffer bpn12) /\

  invariant h0 s /\

  // Local stuff
  B.(loc_includes stack (loc_buffer this_iv)) /\
  B.(loc_includes stack (loc_buffer bpn12)) /\
  B.length this_iv = 12 /\ (

  // Packet number
  let ctr = g_last_packet_number (B.deref h0 s) h0 `U64.add` 1uL in
  B.as_seq h0 bpn12 == FStar.Endianness.n_to_be 12 (U64.v ctr) /\ 

  incrementable s h0 /\ (
  let clen = if is_retry h then 0 else U32.v plain_len + Spec.Agile.AEAD.tag_length i.aead_alg in
  (if is_retry h then U32.v plain_len == 0 else 3 <= U32.v plain_len /\ U32.v plain_len < QSpec.max_plain_length) /\
  (has_payload_length h ==> U64.v (payload_length h) == clen) /\
  B.length dst == U32.v (header_len h) + clen
  ))

#pop-options

val encrypt_core: #i:G.erased index -> (
  let i = G.reveal i in
  s:state i ->
  dst:B.buffer U8.t ->
  h:header ->
  plain: B.buffer U8.t ->
  plain_len: U32.t {
    B.length plain = U32.v plain_len
  } ->
  stack: G.erased B.loc ->
  this_iv:B.buffer U8.t ->
  bpn12: B.lbuffer U8.t 12 ->
  Stack unit
    (requires fun h0 -> encrypt_core_pre #i s dst h plain plain_len stack this_iv bpn12 h0
    )
    (ensures fun h0 r h1 ->
        // Memory & preservation
        B.(modifies (stack `loc_union`
          footprint_s h0 (deref h0 s) `loc_union` loc_buffer dst)) h0 h1 /\
        invariant h1 s /\
        footprint_s h1 (B.deref h1 s) == footprint_s h0 (B.deref h0 s) /\ (
        // Functional correctness
        let s0 = g_traffic_secret (B.deref h0 s) in
        let open QUIC.Spec in
        let k = derive_secret i.hash_alg s0 label_key (Spec.Agile.AEAD.key_length i.aead_alg) in
        let iv = derive_secret i.hash_alg s0 label_iv 12 in
        let pne = derive_secret i.hash_alg s0 label_hp (ae_keysize i.aead_alg) in
        let plain = B.as_seq h0 plain in
        let packet: packet = B.as_seq h1 dst in
        let ctr = g_last_packet_number (B.deref h0 s) h0 `U64.add` 1uL in
        packet `Seq.equal`
          QUIC.Spec.encrypt i.aead_alg k iv pne (g_header h h0 ctr) plain
)))

#push-options "--z3rlimit 1024"

let encrypt_core #i s dst h plain plain_len stack this_iv bpn12 =
  (**) let h0 = ST.get () in
  (**) let m_loc = G.hide B.(G.reveal stack `loc_union`
  (**)   footprint_s h0 (deref h0 s) `loc_union` loc_buffer dst) in
  (**) assert_norm (pow2 62 < pow2 (8 * 12));
  let State hash_alg aead_alg e_traffic_secret e_initial_pn
    aead_state iv hp_key bpn ctr_state = !*s
  in
  let last_pn = !* bpn in
  let pn = last_pn `U64.add` 1uL in
  let dst_h = B.sub dst 0ul (HeaderI.header_len h) in
  HeaderI.header_len_correct h h0 pn;
  HeaderI.write_header dst h pn;
  (**) let h1 = ST.get () in
  (**) frame_invariant B.(loc_buffer dst) s h0 h1;
  (**) assert (footprint_s h0 (B.deref h0 s) == footprint_s h1 (B.deref h1 s));
  (**) B.(modifies_loc_includes (G.reveal m_loc) h0 h1 (loc_buffer dst));
  frame_header h pn (B.loc_buffer dst) h0 h1;
  assert (header_live h h1);
  if is_retry h
  then ()
  else begin
    let dst_ciphertag = B.sub dst (HeaderI.header_len h) (plain_len `U32.add` tag_len aead_alg) in
    let dst_cipher = B.sub dst_ciphertag 0ul plain_len in
    let dst_tag = B.sub dst_ciphertag plain_len (tag_len aead_alg) in
    let pn_len = pn_length h `U32.sub` 1ul in
    C.Loops.map2 this_iv bpn12 iv 12ul U8.logxor;
    (**) let h2 = ST.get () in
    (**) frame_invariant B.(loc_buffer this_iv) s h1 h2;
    (**) assert (footprint_s h1 (B.deref h1 s) == footprint_s h2 (B.deref h2 s));
    (**) B.(modifies_loc_includes (G.reveal m_loc) h1 h2 (loc_buffer this_iv));
    (**) B.(modifies_trans (G.reveal m_loc) h0 h1 (G.reveal m_loc) h2);
    (**) pointwise_seq_map2 U8.logxor (B.as_seq h1 bpn12) (B.as_seq h1 iv) 0;
    (**) assert (
      let open QUIC.Spec in
      let npn: lbytes (1 + U32.v pn_len) = Seq.slice (B.as_seq h0 bpn12) (11 - U32.v pn_len) 12 in
      let s0 = g_traffic_secret (B.deref h0 s) in
      let siv = derive_secret i.hash_alg s0 label_iv 12 in
      B.as_seq h2 this_iv `Seq.equal` QUIC.Spec.Lemmas.xor_inplace (B.as_seq h0 bpn12) siv 0
    );
    assert (B.loc_disjoint (header_footprint h) (B.loc_buffer this_iv));
    frame_header h pn (B.loc_buffer this_iv) h1 h2;
    assert (header_live h h2);
    let l = HeaderI.header_len h in
    let r = AEAD.encrypt #(G.hide aead_alg) aead_state
      this_iv 12ul dst_h (HeaderI.header_len h) plain plain_len dst_cipher dst_tag in
    (**) let h3 = ST.get () in
    (**) assert (invariant h3 s);
    (**) assert (footprint_s h2 (B.deref h2 s) == footprint_s h2 (B.deref h3 s));
    (**) B.(modifies_loc_includes (G.reveal m_loc) h2 h3
      (AEAD.footprint h2 aead_state `loc_union` loc_buffer dst));
    (**) B.(modifies_trans (G.reveal m_loc) h0 h2 (G.reveal m_loc) h3);
    (**) assert (r = Success);
    (**) assert (
      let open QUIC.Spec in
      let s0 = g_traffic_secret (B.deref h0 s) in
      let siv = derive_secret i.hash_alg s0 label_iv 12 in
      let k = derive_secret i.hash_alg s0 label_key (Spec.Agile.AEAD.key_length i.aead_alg) in
      let h = g_header h h0 pn in
      let plain = B.as_seq h0 plain in
      let a = aead_alg in
      let pnb = FStar.Endianness.n_to_be 12 (U64.v pn) in
      let npn: lbytes (1 + U32.v pn_len) = Seq.slice pnb (11 - U32.v pn_len) 12 in
      let header = HeaderS.format_header h in
      let iv = QUIC.Spec.Lemmas.xor_inplace pnb siv 0 in
      let cipher = Spec.Agile.AEAD.encrypt #a k iv header plain in
      cipher `Seq.equal` B.as_seq h3 dst_ciphertag
    );
    frame_header h pn (AEAD.footprint h2 aead_state `B.loc_union` (B.loc_buffer dst_cipher `B.loc_union` B.loc_buffer dst_tag)) h2 h3;
    assert (header_live h h3);
    let clen = plain_len `U32.add` tag_len aead_alg in
    let dst_len = header_len h `U32.add` clen in
    let e_cipher = G.hide ((B.as_seq h3 dst_ciphertag) <: QUIC.Spec.cbytes) in
    let e_iv = G.hide (B.as_seq h3 this_iv) in
    QUIC.Spec.header_encrypt_ct_correct i.aead_alg (g_hp_key h3 s) (g_header h h3 pn) (G.reveal e_cipher);
    header_encrypt i dst dst_len s h e_cipher pn;
    (**) let h4 = ST.get () in
    (**) assert (invariant h4 s);
    (**) assert (footprint_s h3 (B.deref h3 s) == footprint_s h4 (B.deref h4 s));
    (**) B.(modifies_loc_includes (G.reveal m_loc) h3 h4
      (footprint_s h3 (B.deref h3 s) `loc_union` loc_buffer dst));
    (**) B.(modifies_trans (G.reveal m_loc) h0 h3 (G.reveal m_loc) h4);
    (**) assert (
      let open QUIC.Spec in
      let s0 = g_traffic_secret (B.deref h0 s) in
      let siv = derive_secret i.hash_alg s0 label_iv 12 in
      let k = derive_secret i.hash_alg s0 label_key (Spec.Agile.AEAD.key_length i.aead_alg) in
      let h = g_header h h0 pn in
      let plain = B.as_seq h0 plain in
      let a = aead_alg in
      let hpk = g_hp_key h0 s in
      let pn_len = U32.v pn_len in
      B.as_seq h4 dst `Seq.equal` QUIC.Spec.encrypt a k siv hpk h plain
    )
  end

#pop-options

#push-options "--z3rlimit 1024 --max_ifuel 0 --initial_ifuel 0 --using_facts_from '*,-LowStar.Monotonic.Buffer.unused_in_not_unused_in_disjoint_2'"

let encrypt #i s dst dst_pn h plain plain_len =
  (**) let h0 = ST.get () in
  let State hash_alg aead_alg e_traffic_secret e_initial_pn
    aead_state iv hp_key pn ctr_state = !*s
  in
  let last_pn: U64.t = !*pn in
  let pn_value = last_pn `U64.add` 1uL in
  push_frame ();
  (**) let h1 = ST.get () in
  frame_header h pn_value B.loc_none h0 h1;
  header_live_loc_not_unused_in_footprint h h1;
  B.loc_unused_in_not_unused_in_disjoint h1;
  let pnb0 = B.alloca 0uy 16ul in
  assert (header_footprint h `B.loc_disjoint` B.loc_buffer pnb0);
  let h11 = ST.get () in
  frame_header h pn_value B.loc_none h1 h11;
  header_live_loc_not_unused_in_footprint h h11;
  B.loc_unused_in_not_unused_in_disjoint h11;
  let this_iv = B.alloca 0uy 12ul in
  assert (header_footprint h `B.loc_disjoint` B.loc_buffer this_iv);
  (**) let mloc = G.hide B.(loc_buffer pnb0 `loc_union` loc_buffer this_iv `loc_union`
    footprint_s h0 (deref h0 s) `loc_union` loc_buffer dst `loc_union` loc_buffer dst_pn) in
  (**) let h2 = ST.get () in
  (**) frame_invariant B.(loc_none) s h1 h2;
  (**) assert (footprint_s h1 (B.deref h1 s) == footprint_s h2 (B.deref h2 s));
  (**) B.(modifies_loc_includes (G.reveal mloc) h1 h2 loc_none);
  let pn128: FStar.UInt128.t = FStar.Int.Cast.Full.uint64_to_uint128 pn_value in
  LowStar.Endianness.store128_be pnb0 pn128;
  (**) let h3 = ST.get () in
  (**) frame_invariant B.(loc_buffer pnb0) s h2 h3;
  (**) assert (footprint_s h2 (B.deref h2 s) == footprint_s h3 (B.deref h3 s));
  (**) B.(modifies_trans (G.reveal mloc) h1 h2 (G.reveal mloc) h3);
  let pnb = B.sub pnb0 4ul 12ul in
  FStar.Math.Lemmas.pow2_le_compat (8 * 12) (8 * 8);
  n_to_be_lower 12 16 (U64.v pn_value);
  frame_header h pn_value B.loc_none h0 h3;
  encrypt_core #i s dst h plain plain_len
    (G.hide B.(loc_buffer this_iv `loc_union` loc_buffer pnb0)) this_iv pnb;
  (**) let h4 = ST.get () in
  (**) assert (invariant h4 s);
  (**) assert (footprint_s h3 (B.deref h3 s) == footprint_s h4 (B.deref h4 s));
  (**) B.(modifies_trans (G.reveal mloc) h1 h3 (G.reveal mloc) h4);
  (**) assert_norm (pow2 62 < pow2 64);
  pn *= pn_value;
  (**) let h5 = ST.get () in
  (**) assert (invariant h5 s);
  (**) assert (footprint_s h4 (B.deref h4 s) == footprint_s h5 (B.deref h5 s));
  (**) B.(modifies_trans (G.reveal mloc) h1 h4 (G.reveal mloc) h5);
  dst_pn *= pn_value;
  (**) let h6 = ST.get () in
  (**) assert (invariant h6 s);
  (**) assert (footprint_s h5 (B.deref h5 s) == footprint_s h6 (B.deref h6 s));
  (**) B.(modifies_trans (G.reveal mloc) h1 h5 (G.reveal mloc) h6);  
  pop_frame ();
  (**) let h7 = ST.get () in
  (**) B.modifies_fresh_frame_popped h0 h1
  (**)   B.(loc_buffer dst `loc_union` loc_buffer dst_pn `loc_union` footprint_s h0 (B.deref h0 s)) h6 h7;
  (**) assert (footprint_s h6 (B.deref h6 s) == footprint_s h7 (B.deref h7 s));
  Success

#pop-options
*)


/// Initial secrets
/// ---------------

// TODO: these three should be immutable buffers but we don't have const
// pointers yet for HKDF.
#push-options "--warn_error -272"
let initial_salt: initial_salt:B.buffer U8.t {
  B.length initial_salt = 20 /\
  B.recallable initial_salt
} =
  [@inline_let]
  let l = [
    0xc3uy; 0xeeuy; 0xf7uy; 0x12uy; 0xc7uy; 0x2euy; 0xbbuy; 0x5auy;
    0x11uy; 0xa7uy; 0xd2uy; 0x43uy; 0x2buy; 0xb4uy; 0x63uy; 0x65uy;
    0xbeuy; 0xf9uy; 0xf5uy; 0x02uy
  ] in
  assert_norm (List.Tot.length l = 20);
  B.gcmalloc_of_list HS.root l

let server_in: server_in:B.buffer U8.t {
  B.length server_in = 9 /\
  B.recallable server_in
} =
  [@inline_let]
  let l = [
    0x73uy; 0x65uy; 0x72uy; 0x76uy; 0x65uy; 0x72uy; 0x20uy; 0x69uy; 0x6euy
  ] in
  assert_norm (List.Tot.length l = 9);
  B.gcmalloc_of_list HS.root l

let client_in: client_in:B.buffer U8.t {
  B.length client_in = 9 /\
  B.recallable client_in
} =
  [@inline_let]
  let l = [
    0x63uy; 0x6cuy; 0x69uy; 0x65uy; 0x6euy; 0x74uy; 0x20uy; 0x69uy; 0x6euy
  ] in
  assert_norm (List.Tot.length l = 9);
  B.gcmalloc_of_list HS.root l
#pop-options

let initial_secrets dst_client dst_server cid cid_len =
  (**) let h0 = ST.get () in
  (**) B.recall initial_salt;
  (**) B.recall server_in;
  (**) B.recall client_in;
  assert_norm (Spec.Agile.Hash.(hash_length SHA2_256) = 32);

  push_frame ();
  (**) let h1 = ST.get () in
  (**) let mloc = G.hide (B.(loc_buffer dst_client `loc_union`
    loc_buffer dst_server `loc_union` loc_region_only true (HS.get_tip h1))) in

  assume False;
  let secret = B.alloca 0uy 32ul in
  (**) let h2 = ST.get () in
  (**) B.(modifies_loc_includes (G.reveal mloc) h1 h2 loc_none);

  (**) hash_is_keysized_ Spec.Agile.Hash.SHA2_256;
  EverCrypt.HKDF.extract Spec.Agile.Hash.SHA2_256 secret initial_salt 20ul
    cid cid_len;
  (**) let h3 = ST.get () in
  (**) B.(modifies_loc_includes (G.reveal mloc) h2 h3 (loc_buffer secret));
  (**) B.(modifies_trans (G.reveal mloc) h1 h2 (G.reveal mloc) h3);

  EverCrypt.HKDF.expand Spec.Agile.Hash.SHA2_256 dst_client secret 32ul client_in 9ul 32ul;
  (**) let h4 = ST.get () in
  (**) B.(modifies_loc_includes (G.reveal mloc) h3 h4 (loc_buffer dst_client));
  (**) B.(modifies_trans (G.reveal mloc) h1 h3 (G.reveal mloc) h4);

  EverCrypt.HKDF.expand Spec.Agile.Hash.SHA2_256 dst_server secret 32ul server_in 9ul 32ul;
  (**) let h5 = ST.get () in
  (**) B.(modifies_loc_includes (G.reveal mloc) h4 h5 (loc_buffer dst_server));
  (**) B.(modifies_trans (G.reveal mloc) h1 h4 (G.reveal mloc) h5);

  pop_frame ();
  (**) let h6 = ST.get () in
  (**) B.modifies_fresh_frame_popped h0 h1
  (**)   B.(loc_buffer dst_client `loc_union` loc_buffer dst_server) h5 h6

let p62: x:U64.t { U64.v x = pow2 62 } =
  assert_norm (pow2 62 = 4611686018427387904);
  4611686018427387904UL

#restart-solver

let decrypt
  #i s dst packet len cid_len
= assume False;
  UnsupportedAlgorithm

(*

let header_decrypt_pre (i:index)
  (s: state i)
  (packet: B.buffer U8.t)
  (packet_len: U32.t)
  (cid_len: U8.t)
  (h0: HS.mem)
=
  U8.v cid_len <= 20 /\
  B.live h0 packet /\
  B.length packet == U32.v packet_len /\
  invariant h0 s /\
  incrementable s h0 /\
  B.loc_disjoint (B.loc_buffer packet) (footprint h0 s)

#push-options "--max_ifuel 2 --initial_ifuel 2"

noeq
type header_decrypt_aux_t = {
  is_short: bool;
  is_retry: bool;
  pn_offset: U32.t;
  pn_len: U32.t;
}

unfold
let header_decrypt_aux_post (i:index)
  (s: state i)
  (packet: B.buffer U8.t)
  (packet_len: U32.t)
  (cid_len: U8.t)
  (locals: B.loc)
  (h0: HS.mem)
  (r: option header_decrypt_aux_t)
  (h1: HS.mem)
: Ghost Type0
  (requires (
    header_decrypt_pre i s packet packet_len cid_len h0
  ))
  (ensures (fun _ -> True))
=
  let a = i.aead_alg in
  let hpk = g_hp_key h0 s in
  let spec_result = QUIC.Spec.header_decrypt_aux_ct a hpk (U8.v cid_len) (B.as_seq h0 packet) 
  in
  invariant h1 s /\
  footprint_s h0 (B.deref h0 s) == footprint_s h1 (B.deref h1 s) /\
  g_hp_key h0 s == g_hp_key h1 s /\
  B.as_seq h0 (State?.iv (B.deref h0 s)) `Seq.equal` B.as_seq h1 (State?.iv (B.deref h1 s)) /\
  B.deref h0 (State?.pn (B.deref h0 s)) == B.deref h1 (State?.pn (B.deref h1 s)) /\
  begin match r with
  | None ->
    B.modifies (B.loc_buffer packet `B.loc_union` footprint_s h0 (B.deref h0 s) `B.loc_union` locals) h0 h1 /\
    None? spec_result
  | Some result ->
    begin match spec_result with
    | None -> False
    | Some spec_result ->
      result.is_short == spec_result.Spec.is_short /\
      result.is_retry == spec_result.Spec.is_retry /\
      B.as_seq h1 packet `Seq.equal` spec_result.Spec.packet /\
      begin if result.is_retry
      then
        B.modifies locals h0 h1
      else
        U32.v result.pn_offset == spec_result.Spec.pn_offset /\
        U32.v result.pn_len == (spec_result.Spec.pn_len <: nat) /\
        U32.v result.pn_offset + U32.v result.pn_len <= B.length packet /\
        B.modifies (locals `B.loc_union` footprint_s h0 (B.deref h0 s) `B.loc_union` B.loc_buffer packet) h0 h1
      end
    end
  end

#push-options "--z3rlimit 1024 --max_ifuel 3 --initial_ifuel 3"

#restart-solver

let header_decrypt_aux_core
  (i:G.erased index)
  (s: state i)
  (packet: B.buffer U8.t)
  (packet_len: U32.t)
  (cid_len: U8.t)
  (mask: B.buffer U8.t)
  (pn_mask: B.buffer U8.t)
: Stack (option header_decrypt_aux_t)
  (requires (fun h0 ->
    header_decrypt_pre i s packet packet_len cid_len h0 /\
    B.live h0 mask /\
    B.live h0 pn_mask /\
    B.all_disjoint [ footprint h0 s; B.loc_buffer packet; B.loc_buffer mask; B.loc_buffer pn_mask] /\
    B.length mask == 16 /\
    B.length pn_mask == 4
  ))
  (ensures (fun h0 r h1 ->
    header_decrypt_aux_post i s packet packet_len cid_len (B.loc_buffer mask `B.loc_union` B.loc_buffer pn_mask) h0 r h1
  ))
= let h0 = ST.get () in
  if packet_len = 0ul
  then None
  else
    let f = B.index packet 0ul in
    let is_short = BF.uint8.BF.get_bitfield f 7 8 = 0uy in
    let is_retry = not is_short && BF.uint8.BF.get_bitfield f 4 6 = 3uy in
    if is_retry
    then
      Some ({
        is_short = is_short;
        is_retry = is_retry;
        pn_offset = 0ul;
        pn_len = 0ul;
      })
    else begin
      let pn_offset = HeaderI.putative_pn_offset (FStar.Int.Cast.uint8_to_uint32 cid_len) packet packet_len in
      if pn_offset = 0ul
      then None
      else if (packet_len `U32.sub` pn_offset) `U32.lt` 20ul
      then None
      else begin
        let State _ aead_alg _ _ aead_state _ k _ ctr_state = !*s in
        let sample_offset = pn_offset `U32.add` 4ul in
        let sample = B.sub packet sample_offset 16ul in
        block_of_sample (as_cipher_alg aead_alg) mask ctr_state k sample;
        let fmask = B.index mask 0ul in
        let f' =
          if is_short
          then BF.uint8.BF.set_bitfield f 0 5 (BF.uint8.BF.get_bitfield (f `U8.logxor` fmask) 0 5)
          else BF.uint8.BF.set_bitfield f 0 4 (BF.uint8.BF.get_bitfield (f `U8.logxor` fmask) 0 4)
        in
        let pn_len = BF.uint8.BF.get_bitfield f' 0 2 in
        B.upd packet 0ul f' ;
        let h2 = ST.get () in
        assert (B.as_seq h2 packet `Seq.equal` Seq.cons f' (Seq.slice (B.as_seq h0 packet) 1 (B.length packet)));
        pn_sizemask pn_mask pn_len;
        let sub_mask = B.sub mask 1ul 4ul in
        let h3 = ST.get () in
        op_inplace pn_mask 4ul sub_mask 4ul 0ul U8.logand;
        pointwise_seq_map2 U8.logand (B.as_seq h3 pn_mask) (B.as_seq h3 sub_mask) 0;
        and_inplace_commutative (B.as_seq h3 pn_mask) (B.as_seq h3 sub_mask);
        pointwise_seq_map2 U8.logand (B.as_seq h3 sub_mask) (B.as_seq h3 pn_mask) 0;
        op_inplace packet packet_len pn_mask 4ul pn_offset U8.logxor;
        Some ({
          is_short = is_short;
          is_retry = is_retry;
          pn_offset = pn_offset;
          pn_len = FStar.Int.Cast.uint8_to_uint32 pn_len;
        })
      end
    end

#pop-options

let header_decrypt_aux
  (i:G.erased index)
  (s: state i)
  (packet: B.buffer U8.t)
  (packet_len: U32.t)
  (cid_len: U8.t)
: Stack (option header_decrypt_aux_t)
  (requires (fun h0 ->
    header_decrypt_pre i s packet packet_len cid_len h0
  ))
  (ensures (fun h0 r h1 ->
    header_decrypt_aux_post i s packet packet_len cid_len B.loc_none h0 r h1
  ))
= ST.push_frame ();
  let mask = B.alloca 0uy 16ul in
  let pn_mask = B.alloca 0uy 4ul in
  let res = header_decrypt_aux_core i s packet packet_len cid_len mask pn_mask in
  ST.pop_frame ();
  res

unfold
let header_decrypt_post (i:index)
  (s: state i)
  (packet: B.buffer U8.t)
  (packet_len: U32.t)
  (cid_len: U8.t)
  (h0: HS.mem)
  (r: (option (header & U32.t & U32.t & u62)))
  (h1: HS.mem)
: Ghost Type0
  (requires (
    header_decrypt_pre i s packet packet_len cid_len h0
  ))
  (ensures (fun _ -> True))
=
  let a = i.aead_alg in
  let hpk = g_hp_key h0 s in
  let last_pn = U64.v (B.deref h0 (State?.pn (B.deref h0 s))) in
  let spec_result = QUIC.Spec.header_decrypt a hpk (U8.v cid_len) last_pn (B.as_seq h0 packet) 
  in
  invariant h1 s /\
  footprint_s h0 (B.deref h0 s) == footprint_s h1 (B.deref h1 s) /\
  g_hp_key h0 s == g_hp_key h1 s /\
  B.as_seq h0 (State?.iv (B.deref h0 s)) `Seq.equal` B.as_seq h1 (State?.iv (B.deref h1 s)) /\
  B.deref h0 (State?.pn (B.deref h0 s)) == B.deref h1 (State?.pn (B.deref h1 s)) /\
  begin match r with
  | None ->
    QSpec.H_Failure? spec_result
  | Some (header, header_len, cipher_len, pn) ->
    begin match spec_result with
    | QSpec.H_Failure -> False
    | QSpec.H_Success spec_header spec_cipher spec_rem ->
      header_len == HeaderI.header_len header /\
      U32.v header_len + U32.v cipher_len <= B.length packet /\
      B.loc_buffer (B.gsub packet 0ul header_len) `B.loc_includes` header_footprint header /\
      header_live header h1 /\
      g_header header h1 pn == spec_header /\
      Seq.slice (B.as_seq h1 packet) 0 (U32.v header_len) `Seq.equal` HeaderI.format_header spec_header /\
      Seq.slice (B.as_seq h0 packet) (U32.v header_len) (U32.v header_len + U32.v cipher_len) == spec_cipher /\
      Seq.slice (B.as_seq h0 packet) (U32.v header_len + U32.v cipher_len) (B.length packet) == spec_rem
    end
  end

[@CMacro]
let max_cipher_length : (max_cipher_length: U64.t { U64.v max_cipher_length == QSpec.max_cipher_length }) =
  [@inline_let]
  let v = 4294950796uL in
  [@inline_let]
  let _ = assert_norm (U64.v v == QSpec.max_cipher_length) in
  v

val header_decrypt: i:G.erased index ->
  (s: state i) ->
  (packet: B.buffer U8.t) ->
  (packet_len: U32.t) ->
  (cid_len: U8.t) ->
  Stack (option (header & U32.t & U32.t & u62))
    (requires (fun h0 ->
      header_decrypt_pre i s packet packet_len cid_len h0 /\
      B.(loc_disjoint (loc_buffer packet) (footprint h0 s)) /\
      invariant h0 s))
    (ensures (fun h0 r h1 ->
      header_decrypt_post i s packet packet_len cid_len h0 r h1 /\
      begin match r with
      | None ->
        B.modifies (B.loc_buffer packet `B.loc_union` footprint_s h0 (B.deref h0 s)) h0 h1
      | Some (header, header_len, cipher_len, pn) ->
        B.modifies (B.loc_buffer (B.gsub packet 0ul header_len) `B.loc_union` footprint_s h0 (B.deref h0 s)) h0 h1
      end
    ))

#push-options "--z3rlimit 1024 --max_ifuel 4 --initial_ifuel 4"

#restart-solver

let header_decrypt i s packet packet_len cid_len =
  let h0 = ST.get () in
  let State hash_alg aead_alg e_traffic_secret e_initial_pn
    aead_state iv hp_key bpn ctr_state = !*s
  in
  let last_pn = !* bpn in
  Spec.header_decrypt_aux_ct_correct i.aead_alg (g_hp_key h0 s) (U8.v cid_len) (B.as_seq h0 packet);
  match header_decrypt_aux i s packet packet_len cid_len with
  | None -> None
  | Some ({ is_short; is_retry; pn_offset; pn_len }) ->
    begin match HeaderI.read_header packet packet_len (FStar.Int.Cast.uint8_to_uint32 cid_len) last_pn with
    | None ->
      let h1 = ST.get () in
      let phi () : Lemma
        (requires (HeaderS.H_Success? (HeaderS.parse_header (U8.v cid_len) (U64.v last_pn) (B.as_seq h1 packet))))
        (ensures False)
      = QSpec.header_decrypt_aux_post_parse i.aead_alg (g_hp_key h0 s) (U8.v cid_len) (U64.v last_pn) (B.as_seq h0 packet);
        HeaderS.lemma_header_parsing_post (U8.v cid_len) (U64.v last_pn) (B.as_seq h1 packet);
        HeaderS.putative_pn_offset_correct (HeaderS.H_Success?.h (HeaderS.parse_header (U8.v cid_len) (U64.v last_pn) (B.as_seq h1 packet))) (U8.v cid_len)
      in
      Classical.move_requires phi ();
      None
    | Some (header, pn, header_len) ->
      let h1 = ST.get () in
      QSpec.header_decrypt_aux_post_parse i.aead_alg (g_hp_key h0 s) (U8.v cid_len) (U64.v last_pn) (B.as_seq h0 packet);
      B.modifies_loc_buffer_from_to_intro packet 0ul header_len (footprint_s h0 (B.deref h0 s)) h0 h1;
      HeaderI.header_len_correct header h1 pn;
      HeaderS.lemma_header_parsing_post (U8.v cid_len) (U64.v last_pn) (B.as_seq h1 packet);
      assert (Seq.slice (B.as_seq h1 packet) 0 (U32.v header_len) == HeaderS.format_header (g_header header h1 pn));
      if is_retry
      then
        Some (header, header_len, 0ul, pn)
      else
        let rem'_length = FStar.Int.Cast.uint32_to_uint64 (packet_len `U32.sub` header_len) in
        if has_payload_length header && rem'_length `U64.lt` payload_length header
        then
          None
        else
          let clen = if has_payload_length header then payload_length header else rem'_length in
          if 19uL `U64.lte` clen && clen `U64.lt` max_cipher_length
          then
            let _ = FStar.Math.Lemmas.lemma_mod_lt (U64.v clen) (pow2 32) in
            let res = Some (header, header_len, FStar.Int.Cast.uint64_to_uint32 clen, pn) in
            let _ = assert (header_decrypt_post i s packet packet_len cid_len h0 res h1) in
            res
          else
            None
      end

#pop-options

val decrypt_core: #i:G.erased index -> (
  let i = G.reveal i in
  s:state i ->
  dst: B.pointer result ->
  packet: B.buffer U8.t ->
  len: U32.t{
    B.length packet == U32.v len
  } ->
  cid_len: U8.t ->
  bpn128: B.buffer U8.t ->
  biv: B.buffer U8.t ->
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
      U8.v cid_len <= 20 /\
      B.live h0 packet /\ B.live h0 dst /\
      B.live h0 bpn128 /\ B.live h0 biv /\
      B.(all_disjoint [ loc_buffer dst; loc_buffer packet; footprint h0 s; loc_buffer bpn128; loc_buffer biv ]) /\
      invariant h0 s /\
      incrementable s h0 /\
      B.length biv == 12 /\
      B.length bpn128 == 16
    )
    (ensures fun h0 res h1 ->
      let r = B.deref h1 dst in
      decrypt_post i s dst packet len cid_len h0 res h1 /\
      begin match res with
      | Success ->
      // Contents
      B.(modifies (footprint_s h0 (deref h0 s) `loc_union`
        loc_buffer (gsub packet 0ul r.total_len) `loc_union` loc_buffer dst `loc_union` loc_buffer bpn128 `loc_union` loc_buffer biv) h0 h1)
      | DecodeError ->
        B.modifies (footprint_s h0 (B.deref h0 s) `B.loc_union` B.loc_buffer packet) h0 h1
      | AuthenticationFailure ->
        B.(modifies (footprint_s h0 (deref h0 s) `loc_union`
        loc_buffer (gsub packet 0ul r.total_len) `loc_union` loc_buffer dst `loc_union` loc_buffer bpn128 `loc_union` loc_buffer biv) h0 h1)
      | _ -> False
      end
    )
  )

#push-options "--z3rlimit 1024 --using_facts_from '*,-LowStar.Monotonic.Buffer.unused_in_loc_unused_in_disjoint_2'"

#restart-solver

let decrypt_core #i s dst packet packet_len cid_len bpn128 biv =
  let h0 = ST.get () in
  let State hash_alg aead_alg e_traffic_secret e_initial_pn
    aead_state siv hp_key blastpn ctr_state = !*s
  in
  let lastpn = !* blastpn in
  match header_decrypt i s packet packet_len cid_len with
  | None -> DecodeError
  | Some (header, header_len, cipher_len, pn) ->
    if is_retry header
    then begin
      dst *= ({ pn = 0uL; header = header; header_len = header_len; plain_len = 0ul; total_len = header_len });
      Success
    end else begin
      let aad = B.sub packet 0ul header_len in
      let pn128: FStar.UInt128.t = FStar.Int.Cast.Full.uint64_to_uint128 pn in
      LowStar.Endianness.store128_be bpn128 pn128;
      let bpn = B.sub bpn128 4ul 12ul in
      FStar.Math.Lemmas.pow2_le_compat (8 * 12) (8 * 8);
      n_to_be_lower 12 16 (U64.v pn);
      let h1 = ST.get () in
      C.Loops.map2 biv bpn siv 12ul U8.logxor;
      pointwise_seq_map2 U8.logxor (B.as_seq h1 bpn) (B.as_seq h1 siv) 0;
      let h2 = ST.get () in
      (**) assert (
        let open QUIC.Spec in
        let s0 = g_traffic_secret (B.deref h2 s) in
        let siv = derive_secret i.hash_alg s0 label_iv 12 in
        B.as_seq h2 biv `Seq.equal` QUIC.Spec.Lemmas.xor_inplace (B.as_seq h1 bpn) siv 0
      );
      let plain_len = cipher_len `U32.sub` tag_len aead_alg in
      let plain = B.sub packet header_len plain_len in
      let tag = B.sub packet (header_len `U32.add` plain_len) (tag_len aead_alg) in
      let res_decrypt = AEAD.decrypt #(G.hide aead_alg) aead_state biv 12ul aad header_len plain plain_len tag plain in
      assert (B.as_seq h1 (B.gsub packet 0ul header_len) == HeaderS.format_header (g_header header h1 pn));
      let h3 = ST.get () in
      assert_norm (pow2 62 < pow2 (8 `op_Multiply` 12));
      assert (B.as_seq h1 bpn == FStar.Endianness.n_to_be 12 (U64.v pn));
      assert ((B.as_seq h0 plain `Seq.append` B.as_seq h0 tag) `Seq.equal` Seq.slice (B.as_seq h0 packet) (U32.v header_len) (U32.v header_len + U32.v cipher_len));
      match res_decrypt with
      | AuthenticationFailure ->
        dst *= ({ pn = 0uL; header = header; header_len = header_len; plain_len = 0ul; total_len = header_len `U32.add` cipher_len });
        AuthenticationFailure
      | Success ->
        dst *= ({ pn = pn; header = header; header_len = header_len; plain_len = plain_len; total_len = header_len `U32.add` cipher_len });
        let newlastpn = if pn `U64.gt` lastpn then pn else lastpn in
        blastpn *= newlastpn;
        Success
      | _ ->
        assert False;
        InvalidKey
    end

#pop-options

#restart-solver

let decrypt #i s dst packet packet_len cid_len =
  ST.push_frame ();
  let bpn128 = B.alloca 0uy 16ul in
  let biv = B.alloca 0uy 12ul in
  let res = decrypt_core #i s dst packet packet_len cid_len bpn128 biv in
  ST.pop_frame ();
  res
