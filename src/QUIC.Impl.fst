module QUIC.Impl

// This MUST be kept in sync with QUIC.Impl.fsti...
module G = FStar.Ghost
module B = LowStar.Buffer
module IB = LowStar.ImmutableBuffer
module Seq = QUIC.Secret.Seq
module HS = FStar.HyperStack
module ST = FStar.HyperStack.ST
module HST = FStar.HyperStack.ST

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

open QUIC.Impl.Lemmas

open LowStar.BufferOps

//module HeaderS = QUIC.Spec.Header
//module HeaderI = QUIC.Impl.Header

#set-options "--z3rlimit 16"

#restart-solver

module SAEAD = Spec.Agile.AEAD
module SCipher = Spec.Agile.Cipher
module SHKDF = Spec.Agile.HKDF

module SecretBuffer = QUIC.Secret.Buffer


(* There are a few places where EverCrypt needs public data whereas it
could/should be secret. Thus, we may need some declassification
locally using Lib.RawIntTypes, but we definitely don't want to make
secret integers globally transparent using friend *)

module ADMITDeclassify = Lib.RawIntTypes

unfold
let iv_for_encrypt_decrypt_pre
  (a: ea)
  (siv: B.buffer Secret.uint8)
  (dst: B.buffer Secret.uint8)
  (h: G.erased Spec.header { ~ (Spec.is_retry h) })
  (pn_len: PN.packet_number_length_t)
  (pn: PN.packet_number_t)
  (m: HS.mem)
: GTot Type0
=
  let a' = SAEAD.cipher_alg_of_supported_alg a in
  B.all_disjoint [
    B.loc_buffer siv;
    B.loc_buffer dst;
  ] /\
  B.live m siv /\ B.length siv == 12 /\
  B.live m dst /\ B.length dst == 12 /\
  pn_len == Spec.pn_length h /\
  pn == Spec.packet_number h

unfold
let iv_for_encrypt_decrypt_post
  (a: ea)
  (siv: B.buffer Secret.uint8)
  (dst: B.buffer Secret.uint8)
  (h: G.erased Spec.header { ~ (Spec.is_retry h) })
  (pn_len: PN.packet_number_length_t)
  (pn: PN.packet_number_t)
  (m: HS.mem)
  (m' : HS.mem)
: GTot Type0
=
  iv_for_encrypt_decrypt_pre a siv dst h pn_len pn m /\
  begin
    B.modifies (B.loc_buffer dst) m m' /\
    B.as_seq m' dst `Seq.equal`
      Spec.iv_for_encrypt_decrypt a (B.as_seq m siv) h
  end

let iv_for_encrypt_decrypt
  (a: ea)
  (siv: B.buffer Secret.uint8)
  (dst: B.buffer Secret.uint8)
  (h: G.erased Spec.header { ~ (Spec.is_retry h) })
  (pn_len: PN.packet_number_length_t)
  (pn: PN.packet_number_t)
: HST.Stack unit
  (requires (fun m ->
    iv_for_encrypt_decrypt_pre a siv dst h pn_len pn m
  ))
  (ensures (fun m _ m' ->
    iv_for_encrypt_decrypt_post a siv dst h pn_len pn m m'
  ))
= let m0 = HST.get () in
  B.fill dst (Secret.to_u8 0uy) 12ul;
  let pnb_store = B.sub dst 4ul 8ul in
  SecretBuffer.store64_be pnb_store pn;
  let m2 = HST.get () in
  assert (Seq.seq_reveal (B.as_seq m2 (B.gsub dst 0ul 4ul)) `Seq.equal` Seq.create 4 0uy);
  assert (Seq.seq_reveal (B.as_seq m2 dst) `Seq.equal` (Seq.create 4 0uy `Seq.append` FStar.Endianness.n_to_be 8 (Secret.v pn)));
  QUIC.Impl.Lemmas.n_to_be_lower' 8 12 (Secret.v pn);
  assert (Seq.seq_reveal (B.as_seq m2 dst) == FStar.Endianness.n_to_be 12 (Secret.v pn));
  QUIC.Impl.Lemmas.op_inplace dst siv 12ul 0ul (Secret.logxor #Secret.U8 #Secret.SEC);
  QUIC.Impl.Lemmas.secret_xor_inplace_eq (B.as_seq m2 dst) (B.as_seq m2 siv) 0

module SParse = QUIC.Spec.Header.Parse

unfold
let payload_encrypt_pre
  (a: ea)
  (s: AEAD.state a)
  (siv: B.buffer Secret.uint8)
  (dst: B.buffer Secret.uint8)
  (h: G.erased Spec.header { ~ (Spec.is_retry h) })
  (pn_len: PN.packet_number_length_t)
  (pn: PN.packet_number_t)
  (header_len: Secret.uint32)
  (plain: B.buffer Secret.uint8)
  (plain_len: Secret.uint32) // should be secret, because otherwise one can compute the packet number length
  (m: HS.mem)
: GTot Type0
=
  let fmt = SParse.format_header h in

  B.all_disjoint [
    AEAD.footprint m s;
    B.loc_buffer siv;
    B.loc_buffer dst;
    B.loc_buffer plain;
  ] /\

  AEAD.invariant m s /\
  B.live m siv /\ B.length siv == 12 /\
  Secret.v header_len == Seq.length fmt /\
  B.live m dst /\ B.length dst == Secret.v header_len + Secret.v plain_len + SAEAD.tag_length a /\
  pn_len == Spec.pn_length h /\
  pn == Spec.packet_number h /\
  B.live m plain /\ B.length plain == Secret.v plain_len /\ 3 <= Secret.v plain_len /\ Secret.v plain_len < max_plain_length /\
  B.as_seq m (B.gsub dst 0ul (Secret.reveal header_len)) `Seq.equal` Seq.seq_hide fmt

unfold
let payload_encrypt_post
  (a: ea)
  (s: AEAD.state a)
  (siv: B.buffer Secret.uint8)
  (dst: B.buffer Secret.uint8)
  (h: G.erased Spec.header { ~ (Spec.is_retry h) })
  (pn_len: PN.packet_number_length_t)
  (pn: PN.packet_number_t)
  (header_len: Secret.uint32)
  (plain: B.buffer Secret.uint8)
  (plain_len: Secret.uint32)
  (m: HS.mem)
  (res: error_code)
  (m' : HS.mem)
: GTot Type0
=
  let fmt = SParse.format_header h in
  payload_encrypt_pre a s siv dst h pn_len pn header_len plain plain_len m /\
  B.modifies (B.loc_buffer (B.gsub dst (Secret.reveal header_len) (B.len dst ` U32.sub` Secret.reveal header_len)) `B.loc_union` AEAD.footprint m s) m m' /\
  AEAD.invariant m' s /\ AEAD.footprint m' s == AEAD.footprint m s /\
  AEAD.preserves_freeable s m m' /\
  AEAD.as_kv (B.deref m' s) == AEAD.as_kv (B.deref m s) /\
  B.as_seq m' (B.gsub dst (Secret.reveal header_len) (B.len dst `U32.sub` Secret.reveal header_len)) `Seq.equal` Seq.seq_hide (Spec.payload_encrypt a (AEAD.as_kv (B.deref m s)) (B.as_seq m siv) h (Seq.seq_reveal (B.as_seq m plain))) /\
  res == Success

#push-options "--z3rlimit 32"

let payload_encrypt
  (a: ea)
  (s: AEAD.state a)
  (siv: B.buffer Secret.uint8)
  (dst: B.buffer Secret.uint8)
  (h: G.erased Spec.header { ~ (Spec.is_retry h) })
  (pn_len: PN.packet_number_length_t)
  (pn: PN.packet_number_t)
  (header_len: Secret.uint32)
  (plain: B.buffer Secret.uint8)
  (plain_len: Secret.uint32)
: HST.Stack error_code
  (requires (fun m ->
    payload_encrypt_pre a s siv dst h pn_len pn header_len plain plain_len m
  ))
  (ensures (fun m res m' ->
    payload_encrypt_post a s siv dst h pn_len pn header_len plain plain_len m res m'
  ))
= 
  let m0 = HST.get () in
  HST.push_frame ();
  let m1 = HST.get () in
  B.loc_unused_in_not_unused_in_disjoint m1;
  let iv = B.alloca (Secret.to_u8 0uy) 12ul in

  (* EverCrypt currently does not support secret length encryption, so
  whenever we need to define the arguments to EverCrypt.AEAD.encrypt,
  we need to (locally there and only there) declassify the lengths of
  the aad, plain, cipher and tag buffers. *)
  let aad = B.sub dst 0ul (ADMITDeclassify.u32_to_UInt32 header_len) in
  let cipher = B.sub dst (ADMITDeclassify.u32_to_UInt32 header_len) (ADMITDeclassify.u32_to_UInt32 plain_len) in
  let tag = B.sub dst (ADMITDeclassify.u32_to_UInt32 (header_len `Secret.add` plain_len)) 16ul in

  iv_for_encrypt_decrypt a siv iv h pn_len pn;
  let res = AEAD.encrypt #a s iv 12ul aad (ADMITDeclassify.u32_to_UInt32 header_len) plain (ADMITDeclassify.u32_to_UInt32 plain_len) cipher tag in
  HST.pop_frame ();
  res

#pop-options

unfold
let encrypt'_pre
  (a: ea)
  (aead: AEAD.state a)
  (siv: B.buffer Secret.uint8)
  (ctr: CTR.state (SAEAD.cipher_alg_of_supported_alg a))
  (hpk: B.buffer Secret.uint8)
  (dst: B.buffer U8.t)
  (h: header)
  (pn: PN.packet_number_t)
  (plain: B.buffer Secret.uint8)
  (plain_len: Secret.uint32) // should be secret, because otherwise one can compute the packet number length
  (m: HS.mem)
: GTot Type0
=
  let a' = SAEAD.cipher_alg_of_supported_alg a in
  B.all_disjoint [
    AEAD.footprint m aead;
    B.loc_buffer siv;
    CTR.footprint m ctr;
    B.loc_buffer hpk;
    B.loc_buffer dst;
    header_footprint h;
    B.loc_buffer plain;
  ] /\
  AEAD.invariant m aead /\
  B.live m siv /\ B.length siv == 12 /\
  CTR.invariant m ctr /\
  B.live m hpk /\ B.length hpk == Spec.Agile.Cipher.key_length a' /\
  B.live m dst /\
  header_live h m /\
  B.live m plain /\ B.length plain == Secret.v plain_len /\
  begin
    if is_retry h
    then
      B.length plain == 0 /\
      B.length dst == Secret.v (header_len h)
    else
      B.length dst == Secret.v (header_len h) + Secret.v plain_len + SAEAD.tag_length a /\
      3 <= Secret.v plain_len /\ Secret.v plain_len < max_plain_length
  end

unfold
let encrypt'_post
  (a: ea)
  (aead: AEAD.state a)
  (siv: B.buffer Secret.uint8)
  (ctr: CTR.state (SAEAD.cipher_alg_of_supported_alg a))
  (hpk: B.buffer Secret.uint8)
  (dst: B.buffer U8.t)
  (h: header)
  (pn: PN.packet_number_t)
  (plain: B.buffer Secret.uint8)
  (plain_len: Secret.uint32)
  (m: HS.mem)
  (res: error_code)
  (m' : HS.mem)
: GTot Type0
=
  encrypt'_pre a aead siv ctr hpk dst h pn plain plain_len m /\
  B.modifies (B.loc_buffer dst `B.loc_union` AEAD.footprint m aead `B.loc_union` CTR.footprint m ctr) m m' /\
  AEAD.invariant m' aead /\ AEAD.footprint m' aead == AEAD.footprint m aead /\
  AEAD.preserves_freeable aead m m' /\
  AEAD.as_kv (B.deref m' aead) == AEAD.as_kv (B.deref m aead) /\
  CTR.invariant m' ctr /\ CTR.footprint m' ctr == CTR.footprint m ctr /\
  B.as_seq m' dst `Seq.equal` Spec.encrypt a (AEAD.as_kv (B.deref m aead)) (B.as_seq m siv) (B.as_seq m hpk) (g_header h m pn) (Seq.seq_reveal (B.as_seq m plain)) /\
  res == Success

#push-options "--z3rlimit 64"

let encrypt'
  (a: ea)
  (aead: AEAD.state a)
  (siv: B.buffer Secret.uint8)
  (ctr: CTR.state (SAEAD.cipher_alg_of_supported_alg a))
  (hpk: B.buffer Secret.uint8)
  (dst: B.buffer U8.t)
  (h: header)
  (pn: PN.packet_number_t)
  (plain: B.buffer Secret.uint8)
  (plain_len: Secret.uint32)
: HST.Stack error_code
  (requires (fun m ->
    encrypt'_pre a aead siv ctr hpk dst h pn plain plain_len m
  ))
  (ensures (fun m res m' ->
    encrypt'_post a aead siv ctr hpk dst h pn plain plain_len m res m'
  ))
= let m0 = HST.get () in
  let gh = Ghost.hide (g_header h m0 pn) in
  let fmt = Ghost.hide (QUIC.Spec.Header.Parse.format_header gh) in
  let header_len = header_len h in
  QUIC.Impl.Header.Parse.header_len_correct h m0 pn;
  QUIC.Impl.Header.Base.header_len_v h;
  let isretry = is_retry h in

  (* Currently, EverParse needs the size of the destination buffer for
  writing, as a public integer, even though this is not strictly
  necessary. Since the serializers have no knowledge of the payload,
  and do not perform any declassification of the header sizes, we can
  pass the whole size of the destination buffer. *)
  QUIC.Impl.Header.Parse.write_header h pn dst
    (ADMITDeclassify.u32_to_UInt32 (header_len `Secret.add` (if isretry then Secret.to_u32 0ul else plain_len `Secret.add` Secret.to_u32 16ul)));

  if isretry
  then begin
    let dummy_pn_len = Secret.to_u32 1ul in
    let m3 = HST.get () in
    assert (
      Seq.slice (B.as_seq m3 dst) (Secret.v header_len) (B.length dst) `Seq.equal` Seq.seq_reveal (B.as_seq m0 plain)
    );
    QUIC.Impl.Header.header_encrypt a ctr hpk dst gh false true (public_header_len h) dummy_pn_len;
    let m4 = HST.get () in
    assert (B.as_seq m4 dst `Seq.equal` QUIC.Spec.Header.header_encrypt a (B.as_seq m0 hpk) gh (Seq.seq_reveal (B.as_seq m0 plain)));
    Success
  end
  else begin
    let m1 = HST.get () in
    let pn_len = pn_length h in
    let res = SecretBuffer.with_whole_buffer_hide_weak_modifies
      #error_code
      dst
      m1
      (AEAD.footprint m0 aead `B.loc_union`
        B.loc_buffer siv `B.loc_union`
        CTR.footprint m0 ctr `B.loc_union`
        B.loc_buffer hpk `B.loc_union`
        B.loc_buffer plain)
      (AEAD.footprint m0 aead)
      true
      (fun res cont m_ ->
        res == Success /\
        cont `Seq.equal` (
          fmt `Seq.append`
          Spec.payload_encrypt a (AEAD.as_kv (B.deref m0 aead)) (B.as_seq m0 siv) (g_header h m0 pn) (Seq.seq_reveal (B.as_seq m0 plain))) /\
        AEAD.invariant m_ aead /\ AEAD.footprint m_ aead == AEAD.footprint m0 aead /\
        AEAD.preserves_freeable aead m1 m_ /\
        AEAD.as_kv (B.deref m_ aead) == AEAD.as_kv (B.deref m0 aead)
      )
      (fun _ bs -> 
        let res = payload_encrypt a aead siv bs gh pn_len pn header_len plain plain_len in
        let m_ = HST.get () in
        assert (
          let cont = B.as_seq m_ bs in
          Seq.length fmt == Secret.v header_len /\
          cont `Seq.equal` (Seq.slice cont 0 (Secret.v header_len) `Seq.append` Seq.slice cont (Secret.v header_len) (Seq.length cont))
        );
        res
      )
    in
    match res with
    | Success ->
      let m3 = HST.get () in
      assert (
        Seq.slice (B.as_seq m3 dst) (Secret.v header_len) (B.length dst) `Seq.equal` Spec.payload_encrypt a (AEAD.as_kv (B.deref m0 aead)) (B.as_seq m0 siv) gh (Seq.seq_reveal (B.as_seq m0 plain))
      );
      QUIC.Impl.Header.header_encrypt a ctr hpk dst gh (BShort? h) isretry (public_header_len h) pn_len;
      let m4 = HST.get () in
      assert (B.as_seq m4 dst `Seq.equal` QUIC.Spec.Header.header_encrypt a (B.as_seq m0 hpk) gh (Spec.payload_encrypt a (AEAD.as_kv (B.deref m0 aead)) (B.as_seq m0 siv) gh (Seq.seq_reveal (B.as_seq m0 plain))));
      res
    | _ ->
      assert False;
      res
  end

#pop-options

(* At this point I need to have access to the internal state *)
friend QUIC.Impl.Crypto

#push-options "--z3rlimit 64"

let encrypt
  #i s dst dst_pn h plain plain_len
=
  let m0 = HST.get () in
  let QUIC.Impl.Crypto.State hash_alg aead_alg e_traffic_secret e_initial_pn
    aead_state iv hp_key bpn ctr_state = !*s
  in
  let last_pn = !* bpn in
  let pn = last_pn `Secret.add` Secret.to_u64 1uL in
  B.upd bpn 0ul pn;
  B.upd dst_pn 0ul pn;
  let m1 = HST.get () in
  assert (B.modifies (footprint m0 s `B.loc_union` B.loc_buffer dst_pn) m0 m1);
  frame_header h pn  (footprint m0 s `B.loc_union` B.loc_buffer dst_pn) m0 m1;
  encrypt' aead_alg aead_state iv ctr_state hp_key dst h pn plain (Secret.to_u32 plain_len)

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
  (**) let h0 = ST.get () in
  (**) B.recall initial_salt;
  (**) B.recall server_in;
  (**) B.recall client_in;
  assert_norm (Spec.Agile.Hash.(hash_length SHA2_256) = 32);

  push_frame ();
  (**) let h1 = ST.get () in
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

  let h15 = ST.get () in
  B.loc_unused_in_not_unused_in_disjoint h15;
  let tmp = B.alloca 0uy 20ul in
  B.blit initial_salt 0ul tmp 0ul 20ul;
  
  (**) let h2 = ST.get () in

  (**) hash_is_keysized_ Spec.Agile.Hash.SHA2_256;
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
  (**) let h3 = ST.get () in
  (**) B.(modifies_trans (G.reveal mloc) h1 h2 (G.reveal mloc) h3);

  let tmp_client_in = B.sub tmp 0ul 9ul in
  B.blit client_in 0ul tmp_client_in 0ul 9ul;
  let h35 = ST.get () in
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
  (**) let h4 = ST.get () in
  (**) B.(modifies_trans (G.reveal mloc) h1 h3 (G.reveal mloc) h4);

  let tmp_server_in = B.sub tmp 0ul 9ul in
  B.blit server_in 0ul tmp_server_in 0ul 9ul;
  let h45 = ST.get () in
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
  (**) let h5 = ST.get () in
  (**) B.(modifies_trans (G.reveal mloc) h1 h4 (G.reveal mloc) h5);

  pop_frame ();
  (**) let h6 = ST.get () in
  (**) B.modifies_fresh_frame_popped h0 h1
  (**)   B.(loc_buffer dst_client `loc_union` loc_buffer dst_server) h5 h6

let p62: x:U64.t { U64.v x = pow2 62 } =
  assert_norm (pow2 62 = 4611686018427387904);
  4611686018427387904UL

#restart-solver


unfold
let payload_decrypt_pre
  (a: ea)
  (s: AEAD.state a)
  (siv: B.buffer Secret.uint8)
  (dst: B.buffer Secret.uint8)
  (gh: Ghost.erased Spec.header { ~ (Spec.is_retry gh) })
  (hlen: Secret.uint32)
  (pn_len: PN.packet_number_length_t)
  (pn: PN.packet_number_t)
  (cipher_and_tag_len: Secret.uint32)
  (m: HS.mem)
: GTot Type0
=
  let fmt = SParse.format_header gh in

  B.all_disjoint [
    AEAD.footprint m s;
    B.loc_buffer siv;
    B.loc_buffer dst;
  ] /\

  AEAD.invariant m s /\
  B.live m siv /\ B.length siv == 12 /\
  Secret.v cipher_and_tag_len >= SAEAD.tag_length a /\
  Secret.v hlen == Seq.length fmt /\
  Secret.v hlen + Secret.v cipher_and_tag_len <= B.length dst /\
  Secret.v cipher_and_tag_len < max_cipher_length /\
  B.live m dst /\
  pn_len == Spec.pn_length gh /\
  pn == Spec.packet_number gh /\
  B.as_seq m (B.gsub dst 0ul (Secret.reveal hlen)) `Seq.equal` Seq.seq_hide fmt

unfold
let payload_decrypt_post
  (a: ea)
  (s: AEAD.state a)
  (siv: B.buffer Secret.uint8)
  (dst: B.buffer Secret.uint8)
  (gh: Ghost.erased Spec.header { ~ (Spec.is_retry gh) })
  (hlen: Secret.uint32)
  (pn_len: PN.packet_number_length_t)
  (pn: PN.packet_number_t)
  (cipher_and_tag_len: Secret.uint32)
  (m: HS.mem)
  (res: error_code)
  (m' : HS.mem)
: GTot Type0
=
  payload_decrypt_pre a s siv dst gh hlen pn_len pn cipher_and_tag_len m /\
  begin
    let bplain = B.gsub dst (Secret.reveal hlen) (Secret.reveal cipher_and_tag_len `U32.sub` U32.uint_to_t (SAEAD.tag_length a)) in
    B.modifies (B.loc_buffer bplain `B.loc_union` AEAD.footprint m s) m m' /\
    AEAD.invariant m' s /\ AEAD.footprint m' s == AEAD.footprint m s /\
    AEAD.preserves_freeable s m m' /\
    AEAD.as_kv (B.deref m' s) == AEAD.as_kv (B.deref m s) /\
    begin match res, Spec.payload_decrypt a (AEAD.as_kv (B.deref m s)) (B.as_seq m siv) gh (B.as_seq m (B.gsub dst (Secret.reveal hlen) (Secret.reveal cipher_and_tag_len))) with
    | Success, Some plain ->
      B.as_seq m' bplain `Seq.equal` plain
    | AuthenticationFailure, None -> True
    | _ -> False
    end
  end

#push-options "--z3rlimit 32"

let payload_decrypt
  (a: ea)
  (s: AEAD.state a)
  (siv: B.buffer Secret.uint8)
  (dst: B.buffer Secret.uint8)
  (gh: Ghost.erased Spec.header { ~ (Spec.is_retry gh) })
  (hlen: Secret.uint32)
  (pn_len: PN.packet_number_length_t)
  (pn: PN.packet_number_t)
  (cipher_and_tag_len: Secret.uint32)
: HST.Stack error_code
  (requires (fun m ->
    payload_decrypt_pre a s siv dst gh hlen pn_len pn cipher_and_tag_len m
  ))
  (ensures (fun m res m' ->
    payload_decrypt_post a s siv dst gh hlen pn_len pn cipher_and_tag_len m res m'
  ))
= 
  let m0 = HST.get () in
  HST.push_frame ();
  let m1 = HST.get () in
  B.loc_unused_in_not_unused_in_disjoint m1;
  let iv = B.alloca (Secret.to_u8 0uy) 12ul in
  let cipher_len = cipher_and_tag_len `Secret.usub` Secret.hide 16ul in

  (* EverCrypt currently does not support secret length encryption, so
  whenever we need to define the arguments to EverCrypt.AEAD.encrypt,
  we need to (locally there and only there) declassify the lengths of
  the aad, plain, cipher and tag buffers. *)
  let aad = B.sub dst 0ul (ADMITDeclassify.u32_to_UInt32 hlen) in
  let cipher = B.sub dst (ADMITDeclassify.u32_to_UInt32 hlen) (ADMITDeclassify.u32_to_UInt32 cipher_len) in
  let tag = B.sub dst (ADMITDeclassify.u32_to_UInt32 (hlen `Secret.add` cipher_len)) 16ul in

  iv_for_encrypt_decrypt a siv iv gh pn_len pn;
  let res = AEAD.decrypt #a s iv 12ul aad (ADMITDeclassify.u32_to_UInt32 hlen) cipher (ADMITDeclassify.u32_to_UInt32 cipher_len) tag cipher in
  assert (B.as_seq m0 (B.gsub dst (Secret.reveal hlen) (Secret.reveal cipher_and_tag_len)) `Seq.equal` (B.as_seq m0 cipher `Seq.append` B.as_seq m0 tag));
  HST.pop_frame ();
  res

#pop-options

unfold
let decrypt'_pre
  (a: ea)
  (aead: AEAD.state a)
  (siv: B.buffer Secret.uint8)
  (ctr: CTR.state (SAEAD.cipher_alg_of_supported_alg a))
  (hpk: B.buffer Secret.uint8)
  (dst: B.buffer U8.t)
  (dst_len: U32.t)
  (dst_hdr: B.pointer result)
  (last_pn: PN.last_packet_number_t)
  (cid_len: short_dcid_len_t)
  (m: HS.mem)
: GTot Type0
=
  let a' = SAEAD.cipher_alg_of_supported_alg a in
  B.all_disjoint [
    AEAD.footprint m aead;
    B.loc_buffer siv;
    CTR.footprint m ctr;
    B.loc_buffer hpk;
    B.loc_buffer dst;
    B.loc_buffer dst_hdr;
  ] /\
  AEAD.invariant m aead /\
  B.live m siv /\ B.length siv == 12 /\
  CTR.invariant m ctr /\
  B.live m hpk /\ B.length hpk == Spec.Agile.Cipher.key_length a' /\
  B.live m dst /\ B.length dst == U32.v dst_len /\
  B.live m dst_hdr

unfold
let decrypt'_post
  (a: ea)
  (aead: AEAD.state a)
  (siv: B.buffer Secret.uint8)
  (ctr: CTR.state (SAEAD.cipher_alg_of_supported_alg a))
  (hpk: B.buffer Secret.uint8)
  (dst: B.buffer U8.t)
  (dst_len: U32.t)
  (dst_hdr: B.pointer result)
  (last_pn: PN.last_packet_number_t)
  (cid_len: short_dcid_len_t)
  (m: HS.mem)
  (res: error_code)
  (m' : HS.mem)
: GTot Type0
=
  decrypt'_pre a aead siv ctr hpk dst dst_len dst_hdr last_pn cid_len m /\
  AEAD.invariant m' aead /\ AEAD.footprint m' aead == AEAD.footprint m aead /\
  AEAD.preserves_freeable aead m m' /\
  AEAD.as_kv (B.deref m' aead) == AEAD.as_kv (B.deref m aead) /\
  CTR.invariant m' ctr /\ CTR.footprint m' ctr == CTR.footprint m ctr /\
  begin match res, Spec.decrypt a (AEAD.as_kv (B.deref m aead)) (B.as_seq m siv) (B.as_seq m hpk) (Secret.v last_pn) (U32.v cid_len) (B.as_seq m dst) with
  | AuthenticationFailure, Spec.Failure ->
    let r = B.deref m' dst_hdr in
    Secret.v r.total_len <= B.length dst /\
    B.modifies (AEAD.footprint m aead `B.loc_union` CTR.footprint m ctr `B.loc_union` B.loc_buffer dst_hdr `B.loc_union` B.loc_buffer (B.gsub dst 0ul (Secret.reveal r.total_len))) m m'
  | DecodeError, Spec.Failure ->
    B.modifies B.loc_none m m'
  | Success, Spec.Success gh plain rem ->
    let r = B.deref m' dst_hdr in
    let h = r.header in
    header_live h m' /\
    gh == g_header h m' r.pn /\
    r.header_len == header_len h /\
    Secret.v r.plain_len == Seq.length plain /\
    Secret.v r.header_len + Secret.v r.plain_len <= Secret.v r.total_len /\
    Secret.v r.total_len <= B.length dst /\
    B.loc_buffer (B.gsub dst 0ul (public_header_len h)) `B.loc_includes` header_footprint h /\
    (
      B.modifies (AEAD.footprint m aead `B.loc_union` CTR.footprint m ctr `B.loc_union` B.loc_buffer dst_hdr `B.loc_union` B.loc_buffer (B.gsub dst 0ul (Secret.reveal r.total_len))) m m' /\
      B.as_seq m' (B.gsub dst 0ul (Secret.reveal r.header_len)) `Seq.equal` QUIC.Spec.Header.Parse.format_header (g_header h m' r.pn) /\
      B.as_seq m' (B.gsub dst (Secret.reveal r.header_len) (Secret.reveal r.plain_len)) `Seq.equal` plain /\
      B.as_seq m' (B.gsub dst (Secret.reveal r.total_len) (B.len dst `U32.sub` Secret.reveal r.total_len)) `Seq.equal` rem
    )
  | _ -> False
  end

#push-options "--z3rlimit 256"

#restart-solver

let decrypt'
  (a: ea)
  (aead: AEAD.state a)
  (siv: B.buffer Secret.uint8)
  (ctr: CTR.state (SAEAD.cipher_alg_of_supported_alg a))
  (hpk: B.buffer Secret.uint8)
  (dst: B.buffer U8.t)
  (dst_len: U32.t)
  (dst_hdr: B.pointer result)
  (last_pn: PN.last_packet_number_t)
  (cid_len: short_dcid_len_t)
: HST.Stack error_code
  (requires (fun m ->
    decrypt'_pre a aead siv ctr hpk dst dst_len dst_hdr last_pn cid_len m
  ))
  (ensures (fun m res m' ->
    decrypt'_post a aead siv ctr hpk dst dst_len dst_hdr last_pn cid_len m res m'
  ))
= let m0 = HST.get () in
  match QUIC.Impl.Header.header_decrypt a ctr hpk cid_len last_pn dst dst_len with
  | QUIC.Impl.Header.H_Failure -> DecodeError
  | QUIC.Impl.Header.H_Success h pn cipher_and_tag_len ->
    assert (
      match QUIC.Spec.Header.header_decrypt a (B.as_seq m0 hpk) (U32.v cid_len) (Secret.v last_pn) (B.as_seq m0 dst) with
      | QUIC.Spec.Header.H_Success _ ct _ ->
        Seq.length ct == Secret.v cipher_and_tag_len
      | _ -> False
    );
    let m1 = HST.get () in
    let hlen = header_len h in
    QUIC.Impl.Header.Parse.header_len_correct h m1 pn;
    if is_retry h
    then begin
      let r = {
        pn = pn;
        header = h;
        header_len = hlen;
        plain_len = Secret.hide 0ul;
        total_len = hlen;
      } in
      B.upd dst_hdr 0ul r;
      let m2 = HST.get () in
      QUIC.Impl.Header.Base.frame_header h pn (B.loc_buffer dst_hdr) m1 m2;
      Success
    end else begin
      let gh : Ghost.erased Spec.header = Ghost.hide (g_header h m1 pn) in
      let pn_len = pn_length h in
      B.gsub_zero_length dst;
      assert (Secret.v cipher_and_tag_len >= 16);
      assert (SAEAD.tag_length a == 16);
      let plain_len = cipher_and_tag_len `Secret.sub` Secret.hide 16ul in
      let res = SecretBuffer.with_buffer_hide_from
        #error_code
        dst
        0ul
        m1
        (AEAD.footprint m1 aead `B.loc_union`
          B.loc_buffer siv `B.loc_union`
          CTR.footprint m1 ctr `B.loc_union`
          B.loc_buffer hpk)
        (AEAD.footprint m1 aead)
        1ul 0ul (Secret.reveal hlen) (Secret.reveal hlen `U32.add` (Secret.reveal cipher_and_tag_len `U32.sub` U32.uint_to_t (SAEAD.tag_length a)))
        (fun res _ cont m_ ->
          begin match res, Spec.payload_decrypt a (AEAD.as_kv (B.deref m1 aead)) (B.as_seq m1 siv) gh (Seq.seq_hide (B.as_seq m1 (B.gsub dst (Secret.reveal hlen) (Secret.reveal cipher_and_tag_len)))) with
          | Success, Some plain ->
            Seq.slice cont (Secret.v hlen) (Secret.v hlen + (Secret.v cipher_and_tag_len - SAEAD.tag_length a)) == Seq.seq_reveal plain
          | AuthenticationFailure, None -> True
          | _ -> False
          end /\
          AEAD.invariant m_ aead /\ AEAD.footprint m_ aead == AEAD.footprint m0 aead /\
          AEAD.preserves_freeable aead m1 m_ /\
          AEAD.as_kv (B.deref m_ aead) == AEAD.as_kv (B.deref m0 aead)
        )
        (fun _ _ bs ->
          let res = payload_decrypt a aead siv bs gh hlen pn_len pn cipher_and_tag_len in
          let m_ = HST.get () in
          assert (
            let cont = Seq.seq_reveal (B.as_seq m_ bs) in
            match res, Spec.payload_decrypt a (AEAD.as_kv (B.deref m1 aead)) (B.as_seq m1 siv) gh (Seq.seq_hide (B.as_seq m1 (B.gsub dst (Secret.reveal hlen) (Secret.reveal cipher_and_tag_len)))) with
            | Success, Some plain ->
            Seq.slice cont (Secret.v hlen) (Secret.v hlen + (Secret.v cipher_and_tag_len - SAEAD.tag_length a)) `Seq.equal` Seq.seq_reveal plain
            | AuthenticationFailure, None -> True
            | _ -> False
          );
          res
        )
      in
      let r = {
        pn = pn;
        header = h;
        header_len = hlen;
        plain_len = plain_len;
        total_len = hlen `Secret.add` cipher_and_tag_len;
      } in
      B.upd dst_hdr 0ul r;
      let m3 = HST.get () in
      QUIC.Impl.Header.Base.frame_header h pn
        (AEAD.footprint m1 aead `B.loc_union` CTR.footprint m1 ctr `B.loc_union` B.loc_buffer dst_hdr `B.loc_union` B.loc_buffer (B.gsub dst (Secret.reveal hlen) (B.len dst `U32.sub` Secret.reveal hlen))) m1 m3;
      res
    end

#pop-options

#push-options "--z3rlimit 128"

let decrypt
  #i s dst packet len cid_len
=
  let m0 = HST.get () in
  let QUIC.Impl.Crypto.State hash_alg aead_alg e_traffic_secret e_initial_pn
    aead_state iv hp_key bpn ctr_state = !*s
  in
  let last_pn = !* bpn in
  let res = decrypt' aead_alg aead_state iv ctr_state hp_key packet len dst last_pn (FStar.Int.Cast.uint8_to_uint32 cid_len) in
  let m1 = HST.get () in
  if res = Success
  then begin
    let r = B.index dst 0ul in
    let pn = r.pn in
    let pn' = Secret.max last_pn pn in
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
