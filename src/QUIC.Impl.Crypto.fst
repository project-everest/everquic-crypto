module QUIC.Impl.Crypto

module Cipher = EverCrypt.Cipher
module AEAD = EverCrypt.AEAD
module HKDF = EverCrypt.HKDF
module CTR = EverCrypt.CTR
module IB = LowStar.ImmutableBuffer
module U32 = FStar.UInt32

module Seq = QUIC.Secret.Seq

friend QUIC.Spec.Crypto (* for the _l list constants *)

open LowStar.BufferOps (* for the !* notation *)

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
      initial_pn:G.erased PN.packet_number_t ->
      aead_state:EverCrypt.AEAD.state the_aead_alg ->
      iv:EverCrypt.AEAD.iv_p the_aead_alg { B.length iv == 12 } ->
      hp_key:B.buffer Secret.uint8 { B.length hp_key = QUIC.Spec.ae_keysize the_aead_alg } ->
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
  Secret.v initial_pn <= Secret.v (B.deref h pn) /\
  AEAD.as_kv (B.deref h aead_state) ==
    derive_secret i.hash_alg (G.reveal traffic_secret) label_key (Spec.Agile.AEAD.key_length aead_alg) /\
  (B.as_seq h iv) ==
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
  let open FStar.HyperStack.ST in (* for the !* notation *)
  let State the_hash_alg _ _ _ _ _ _ _ _ = !*s in
  the_hash_alg

let last_packet_number_of_state #i s =
  let State _ _ _ _ _ _ _ pn _ = !*s in
  !*pn

/// Helpers & globals
/// -----------------

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
let label_key = LowStar.ImmutableBuffer.igcmalloc_of_list HS.root label_key_l
let label_iv = LowStar.ImmutableBuffer.igcmalloc_of_list HS.root label_iv_l
let label_hp = LowStar.ImmutableBuffer.igcmalloc_of_list HS.root label_hp_l
let prefix = LowStar.ImmutableBuffer.igcmalloc_of_list HS.root QUIC.Spec.prefix_l
#pop-options

/// Actual code
/// -----------

#push-options "--max_ifuel 1 --initial_ifuel 1"
/// One ifuel for inverting on the hash algorithm for computing bounds (the
/// various calls to assert_norm should help ensure this proof goes through
/// reliably). Note that I'm breaking from the usual convention where lengths
/// are UInt32's, mostly to avoid trouble reasoning with modulo when casting
/// from UInt32 to UInt8 to write the label for the key derivation. This could
/// be fixed later.
val derive_secret: a: QUIC.Spec.ha ->
  dst:B.buffer Secret.uint8 ->
  dst_len: U8.t { B.length dst = U8.v dst_len /\ U8.v dst_len <= 255 } ->
  secret:B.buffer Secret.uint8 { B.length secret = Spec.Hash.Definitions.hash_length a } ->
  label:IB.ibuffer U8.t ->
  label_len:U8.t { IB.length label = U8.v label_len /\ U8.v label_len <= 244 } ->
  HST.Stack unit
    (requires fun h0 ->
      B.(all_live h0 [ buf secret; buf label; buf dst ]) /\
      B.disjoint dst secret)
    (ensures fun h0 _ h1 ->
      assert_norm (255 < pow2 61);
      assert_norm (pow2 61 < pow2 125);
      B.(modifies (loc_buffer dst) h0 h1) /\
      B.as_seq h1 dst == QUIC.Spec.derive_secret a (B.as_seq h0 secret)
        (IB.as_seq h0 label) (U8.v dst_len))
#pop-options

#push-options "--z3rlimit 100"
let derive_secret a dst dst_len secret label label_len =
  LowStar.ImmutableBuffer.recall prefix;
  LowStar.ImmutableBuffer.recall_contents prefix QUIC.Spec.prefix;
  (**) let h0 = HST.get () in

  HST.push_frame ();
  (**) let h1 = HST.get () in

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

  (**) let h2 = HST.get () in
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
  assume False; // TODO: hide `info`
  HKDF.expand a dst secret (Hacl.Hash.Definitions.hash_len a) info info_len dst_len32;
  (**) let h3 = HST.get () in
  HST.pop_frame ();
  (**) let h4 = HST.get () in
  (**) B.modifies_fresh_frame_popped h0 h1 (B.loc_buffer dst) h3 h4;
  (**) assert (HST.equal_domains h0 h4)
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
  initial_pn:PN.packet_number_t ->
  traffic_secret:B.buffer Secret.uint8 {
    B.length traffic_secret = Spec.Hash.Definitions.hash_length i.hash_alg
  } ->
  aead_state:AEAD.state i.aead_alg ->
  ctr_state:CTR.state (as_cipher_alg i.aead_alg) ->
  HST.ST unit
    (requires fun h0 ->
      QUIC.Impl.Lemmas.hash_is_keysized_ i.hash_alg; (
      HST.is_eternal_region r /\
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
      AEAD.as_kv (B.deref h0 aead_state) ==
        QUIC.Spec.(derive_secret i.hash_alg (B.as_seq h0 traffic_secret) label_key
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

      G.reveal initial_pn' == initial_pn)))

#push-options "--z3rlimit 50"
let create_in_core i r dst initial_pn traffic_secret aead_state ctr_state =
  LowStar.ImmutableBuffer.recall label_key;
  LowStar.ImmutableBuffer.recall_contents label_key QUIC.Spec.label_key;
  LowStar.ImmutableBuffer.recall label_iv;
  LowStar.ImmutableBuffer.recall_contents label_iv QUIC.Spec.label_iv;
  LowStar.ImmutableBuffer.recall label_hp;
  LowStar.ImmutableBuffer.recall_contents label_hp QUIC.Spec.label_hp;

  (**) let h0 = HST.get () in
  (**) assert_norm FStar.Mul.(8 * 12 <= pow2 64 - 1);

  // The modifies clauses that we will transitively carry across this function body.
  let mloc = G.hide (B.(loc_buffer dst `loc_union` loc_unused_in h0)) in
  let e_traffic_secret: G.erased (Spec.Hash.Definitions.bytes_hash i.hash_alg) =
    G.hide (B.as_seq h0 traffic_secret) in
  let e_initial_pn: G.erased PN.packet_number_t = G.hide (initial_pn) in

  let iv = B.malloc r (Secret.to_u8 0uy) 12ul in
  let hp_key = B.malloc r (Secret.to_u8 0uy) (key_len32 i.aead_alg) in
  let pn = B.malloc r initial_pn 1ul in
  (**) let h1 = HST.get () in
  (**) B.(modifies_loc_includes (G.reveal mloc) h0 h1 loc_none);
  (**) assert (B.length hp_key = QUIC.Spec.ae_keysize i.aead_alg);

  let s: state_s i = State #i
    i.hash_alg i.aead_alg e_traffic_secret e_initial_pn
    aead_state iv hp_key pn ctr_state
  in

  let s:B.pointer_or_null (state_s i) = B.malloc r s 1ul in
  (**) let h2 = HST.get () in
  (**) B.(modifies_loc_includes (G.reveal mloc) h1 h2 loc_none);
  (**) B.(modifies_trans (G.reveal mloc) h0 h1 (G.reveal mloc) h2);

  derive_secret i.hash_alg iv 12uy traffic_secret label_iv 2uy;
  (**) let h3 = HST.get () in
  (**) B.(modifies_loc_includes (G.reveal mloc) h2 h3 (loc_buffer iv));
  (**) B.(modifies_trans (G.reveal mloc) h0 h2 (G.reveal mloc) h3);

  derive_secret i.hash_alg hp_key (key_len i.aead_alg) traffic_secret label_hp 2uy;
  (**) let h4 = HST.get () in
  (**) B.(modifies_loc_includes (G.reveal mloc) h3 h4 (loc_buffer hp_key));
  (**) B.(modifies_trans (G.reveal mloc) h0 h3 (G.reveal mloc) h4);

  dst *= s;
  (**) let h5 = HST.get () in
  (**) B.(modifies_loc_includes (G.reveal mloc) h4 h5 (loc_buffer dst));
  (**) B.(modifies_trans (G.reveal mloc) h0 h4 (G.reveal mloc) h5);
  (**) B.(modifies_only_not_unused_in (loc_buffer dst) h0 h5)
#pop-options

#push-options "--z3rlimit 256"
let create_in i r dst initial_pn traffic_secret =
  LowStar.ImmutableBuffer.recall label_key;
  LowStar.ImmutableBuffer.recall_contents label_key QUIC.Spec.label_key;

  (**) let h0 = HST.get () in

  HST.push_frame ();
  (**) let h1 = HST.get () in
  let mloc = G.hide (B.(loc_region_only true (HS.get_tip h1) `loc_union` loc_buffer dst
    `loc_union` loc_unused_in h0)) in

  let aead_key = B.alloca (Secret.to_u8 0uy) (key_len32 i.aead_alg) in
  let aead_state: B.pointer (B.pointer_or_null (AEAD.state_s i.aead_alg)) =
    B.alloca B.null 1ul in
  let ctr_state: B.pointer (B.pointer_or_null (CTR.state_s (as_cipher_alg i.aead_alg))) =
    B.alloca (B.null #(CTR.state_s (as_cipher_alg i.aead_alg))) 1ul in
  let dummy_iv = B.alloca (Secret.to_u8 0uy) 12ul in

  (**) let h2 = HST.get () in
  (**) B.(modifies_loc_includes (G.reveal mloc) h1 h2 (loc_none));

  derive_secret i.hash_alg aead_key (key_len i.aead_alg) traffic_secret label_key 3uy;
  (**) let h3 = HST.get () in
  (**) B.(modifies_loc_includes (G.reveal mloc) h2 h3 (loc_buffer aead_key));
  (**) B.(modifies_trans (G.reveal mloc) h1 h2 (G.reveal mloc) h3);

  let ret = AEAD.create_in #i.aead_alg r aead_state aead_key in
  (**) let h4 = HST.get () in
  (**) B.(modifies_loc_includes (G.reveal mloc) h3 h4 (loc_buffer aead_state));
  (**) B.(modifies_trans (G.reveal mloc) h1 h3 (G.reveal mloc) h4);

  let ret' = CTR.create_in (as_cipher_alg i.aead_alg) r ctr_state aead_key dummy_iv 12ul 0ul in
  (**) let h5 = HST.get () in
  (**) B.(modifies_loc_includes (G.reveal mloc) h4 h5 (loc_buffer ctr_state));
  (**) B.(modifies_trans (G.reveal mloc) h1 h4 (G.reveal mloc) h5);
  (**) B.(modifies_only_not_unused_in B.(loc_region_only true (HS.get_tip h1) `loc_union` loc_buffer dst) h1 h5);

  match ret with
  | UnsupportedAlgorithm ->
      HST.pop_frame ();
      (**) let h6 = HST.get () in
      (**) B.(modifies_fresh_frame_popped h0 h1 (loc_buffer dst) h5 h6);
      UnsupportedAlgorithm

  | Success ->

  match ret' with
  | UnsupportedAlgorithm ->
      HST.pop_frame ();
      (**) let h6 = HST.get () in
      (**) B.(modifies_fresh_frame_popped h0 h1 (loc_buffer dst) h5 h6);
      UnsupportedAlgorithm

  | Success ->

      let aead_state: AEAD.state i.aead_alg = !*aead_state in
      (**) assert (AEAD.invariant h5 aead_state);

      let ctr_state: CTR.state (as_cipher_alg i.aead_alg) = !*ctr_state in
      (**) assert (CTR.invariant h5 ctr_state);

      create_in_core i r dst initial_pn traffic_secret aead_state ctr_state;
      (**) let h6 = HST.get () in

      (**) B.(modifies_loc_includes
        (loc_region_only true (HS.get_tip h1) `loc_union` loc_buffer dst) h5 h6
        (loc_buffer dst));
      (**) B.(modifies_trans
        (loc_region_only true (HS.get_tip h1) `loc_union` loc_buffer dst)
        h1 h5
        (loc_region_only true (HS.get_tip h1) `loc_union` loc_buffer dst)
        h6);

      HST.pop_frame ();
      (**) let h7 = HST.get () in
      (**) B.(modifies_fresh_frame_popped h0 h1 (loc_buffer dst) h6 h7);
      (**) frame_invariant (B.loc_region_only false (HS.get_tip h6)) (B.deref h7 dst) h6 h7;

      Success
#pop-options
