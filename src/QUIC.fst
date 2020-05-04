module QUIC

module Cipher = EverCrypt.Cipher
module AEAD = EverCrypt.AEAD
module HKDF = EverCrypt.HKDF
module CTR = EverCrypt.CTR
module IB = LowStar.ImmutableBuffer
module U32 = FStar.UInt32

module Seq = QUIC.Secret.Seq
module SecretBuffer = QUIC.Secret.Buffer

module SHKDF = Spec.Agile.HKDF
module SHD = Spec.Hash.Definitions

open LowStar.BufferOps (* for the !* notation *)

module Spec = QUIC.Spec
module Impl = QUIC.Impl
module Lemmas = QUIC.Impl.Lemmas


/// Helpers
/// -------

let key_len (a: ea): x:U8.t { U8.v x = Spec.Agile.AEAD.key_length a } =
  let open Spec.Agile.AEAD in
  match a with
  | AES128_GCM -> 16uy
  | AES256_GCM -> 32uy
  | CHACHA20_POLY1305 -> 32uy

let key_len32 a = FStar.Int.Cast.uint8_to_uint32 (key_len a)


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
      the_hash_alg:ha { the_hash_alg == i.hash_alg } ->
      the_aead_alg:ea { the_aead_alg == i.aead_alg } ->
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
  // : automatic insertion of reveal does not work here
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
      Lemmas.hash_is_keysized_ i.hash_alg; (
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

      g_traffic_secret (B.deref h1 s) == B.as_seq h0 traffic_secret /\ 
      g_last_packet_number (B.deref h1 s) h1 == initial_pn /\

      G.reveal initial_pn' == initial_pn)))

#push-options "--z3rlimit 50"
let create_in_core i r dst initial_pn traffic_secret aead_state ctr_state =
  LowStar.ImmutableBuffer.recall Impl.label_key;
  LowStar.ImmutableBuffer.recall_contents Impl.label_key Spec.label_key;
  LowStar.ImmutableBuffer.recall Impl.label_iv;
  LowStar.ImmutableBuffer.recall_contents Impl.label_iv Spec.label_iv;
  LowStar.ImmutableBuffer.recall Impl.label_hp;
  LowStar.ImmutableBuffer.recall_contents Impl.label_hp Spec.label_hp;

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

  Impl.derive_secret i.hash_alg iv 12uy traffic_secret Impl.label_iv 2uy;
  (**) let h3 = HST.get () in
  (**) B.(modifies_loc_includes (G.reveal mloc) h2 h3 (loc_buffer iv));
  (**) B.(modifies_trans (G.reveal mloc) h0 h2 (G.reveal mloc) h3);

  Impl.derive_secret i.hash_alg hp_key (key_len i.aead_alg) traffic_secret Impl.label_hp 2uy;
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
  LowStar.ImmutableBuffer.recall Impl.label_key;
  LowStar.ImmutableBuffer.recall_contents Impl.label_key Spec.label_key;

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

  Impl.derive_secret i.hash_alg aead_key (key_len i.aead_alg) traffic_secret Impl.label_key 3uy;
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

#push-options "--z3rlimit 64"

let encrypt
  #i s dst dst_pn h plain plain_len
=
  let m0 = HST.get () in
  let State hash_alg aead_alg e_traffic_secret e_initial_pn
    aead_state iv hp_key bpn ctr_state = !*s
  in
  let last_pn = !* bpn in
  let pn = last_pn `Secret.add` Secret.to_u64 1uL in
  B.upd bpn 0ul pn;
  B.upd dst_pn 0ul pn;
  let m1 = HST.get () in
  assert (B.modifies (footprint m0 s `B.loc_union` B.loc_buffer dst_pn) m0 m1);
  frame_header h pn  (footprint m0 s `B.loc_union` B.loc_buffer dst_pn) m0 m1;
  Impl.encrypt aead_alg aead_state iv ctr_state hp_key dst h pn plain (Secret.to_u32 plain_len)

#pop-options


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

#push-options "--z3rlimit 64"

let initial_secrets dst_client dst_server cid cid_len =
  (**) let h0 = HST.get () in
  (**) B.recall initial_salt;
  (**) B.recall server_in;
  (**) B.recall client_in;
  assert_norm (Spec.Agile.Hash.(hash_length SHA2_256) = 32);

  HST.push_frame ();
  (**) let h1 = HST.get () in
  (**) let mloc = G.hide (B.(loc_buffer dst_client `loc_union`
    loc_buffer dst_server `loc_union` loc_region_only true (HS.get_tip h1))) in

  B.loc_unused_in_not_unused_in_disjoint h1;
  let secret = B.alloca (Secret.to_u8 0uy) 32ul in
  
  (* we allocate a temporary buffer to copy the initial_salt,
     server_in and client_in and then to hide it through
     SecretBuffer.with_whole_buffer_hide_weak_modifies, because if we
     directly hide those global buffers, then we won't be able to
     prove that the livenesses of function arguments are preserved,
     because they are not disjoint from the global buffers.  *)

  let h15 = HST.get () in
  B.loc_unused_in_not_unused_in_disjoint h15;
  let tmp = B.alloca 0uy 20ul in
  B.blit initial_salt 0ul tmp 0ul 20ul;
  
  (**) let h2 = HST.get () in

  (**) Lemmas.hash_is_keysized_ Spec.Agile.Hash.SHA2_256;
  let h25 = HST.get () in
  SecretBuffer.with_whole_buffer_hide_weak_modifies
    tmp
    h25
    (B.loc_buffer secret `B.loc_union` B.loc_buffer cid)
    (B.loc_buffer secret)
    false
    (fun _ _ m -> True)
    (fun _ bs ->
      EverCrypt.HKDF.extract Spec.Agile.Hash.SHA2_256 secret bs 20ul
        cid cid_len
    );
  (**) let h3 = HST.get () in
  (**) B.(modifies_trans (G.reveal mloc) h1 h2 (G.reveal mloc) h3);

  let tmp_client_in = B.sub tmp 0ul 9ul in
  B.blit client_in 0ul tmp_client_in 0ul 9ul;
  let h35 = HST.get () in
  SecretBuffer.with_whole_buffer_hide_weak_modifies
    tmp_client_in
    h35
    (B.loc_buffer secret `B.loc_union` B.loc_buffer dst_client)
    (B.loc_buffer dst_client)
    false
    (fun _ _ m -> True)
    (fun _ bs ->
      EverCrypt.HKDF.expand Spec.Agile.Hash.SHA2_256 dst_client secret 32ul bs 9ul 32ul
    );
  (**) let h4 = HST.get () in
  (**) B.(modifies_trans (G.reveal mloc) h1 h3 (G.reveal mloc) h4);

  let tmp_server_in = B.sub tmp 0ul 9ul in
  B.blit server_in 0ul tmp_server_in 0ul 9ul;
  let h45 = HST.get () in
  SecretBuffer.with_whole_buffer_hide_weak_modifies
    tmp_server_in
    h45
    (B.loc_buffer secret `B.loc_union` B.loc_buffer dst_server)
    (B.loc_buffer dst_server)
    false
    (fun _ _ m -> True)
    (fun _ bs ->
      EverCrypt.HKDF.expand Spec.Agile.Hash.SHA2_256 dst_server secret 32ul bs 9ul 32ul
    );
  (**) let h5 = HST.get () in
  (**) B.(modifies_trans (G.reveal mloc) h1 h4 (G.reveal mloc) h5);

  HST.pop_frame ();
  (**) let h6 = HST.get () in
  (**) B.modifies_fresh_frame_popped h0 h1
  (**)   B.(loc_buffer dst_client `loc_union` loc_buffer dst_server) h5 h6

#restart-solver


#push-options "--z3rlimit 128"

let decrypt
  #i s dst packet len cid_len
=
  let m0 = HST.get () in
  let State hash_alg aead_alg e_traffic_secret e_initial_pn
    aead_state iv hp_key bpn ctr_state = !*s
  in
  let last_pn = !* bpn in
  let res = Impl.decrypt aead_alg aead_state iv ctr_state hp_key packet len dst last_pn (FStar.Int.Cast.uint8_to_uint32 cid_len) in
  let m1 = HST.get () in
  if res = Success
  then begin
    let r = B.index dst 0ul in
    let pn = r.Base.pn in
    let pn' = Secret.max64 last_pn pn in
    B.upd bpn 0ul pn';
    let m2 = HST.get () in
    assert (B.modifies (footprint m0 s) m1 m2);
    frame_header r.header pn  (footprint m0 s) m1 m2;
    assert (
      let k = derive_k i s m0 in
      let iv = derive_iv i s m0 in
      let pne = derive_pne i s m0 in
      match Spec.decrypt i.aead_alg k iv pne (Secret.v last_pn) (U8.v cid_len) (B.as_seq m0 packet) with
      | Spec.Success gh plain rem ->
        B.as_seq m1 (B.gsub packet (Secret.reveal r.header_len) (Secret.reveal r.plain_len)) == plain
      | _ -> False
    )
  end;
  res

#pop-options
