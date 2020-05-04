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
  (h: header { ~ (is_retry h) })
  (pn: Ghost.erased (PN.packet_number_t))
  (cipher_and_tag_len: Secret.uint32)
  (m: HS.mem)
: GTot Type0
=
  let gh = g_header h m pn in
  let fmt = SParse.format_header gh in
  let hlen = header_len h in

  B.all_disjoint [
    AEAD.footprint m s;
    B.loc_buffer siv;
    B.loc_buffer dst;
  ] /\

  AEAD.invariant m s /\
  B.live m siv /\ B.length siv == 12 /\
  Secret.v cipher_and_tag_len >= SAEAD.tag_length a /\
  Secret.v hlen + Secret.v cipher_and_tag_len <= B.length dst /\
  Secret.v cipher_and_tag_len < max_cipher_length /\
  B.live m dst /\
  B.as_seq m (B.gsub dst 0ul (Secret.reveal hlen)) `Seq.equal` Seq.seq_hide fmt

unfold
let payload_decrypt_post
  (a: ea)
  (s: AEAD.state a)
  (siv: B.buffer Secret.uint8)
  (dst: B.buffer Secret.uint8)
  (h: header { ~ (is_retry h) })
  (pn: G.erased PN.packet_number_t)
  (cipher_and_tag_len: Secret.uint32)
  (m: HS.mem)
  (res: error_code)
  (m' : HS.mem)
: GTot Type0
=
  payload_decrypt_pre a s siv dst h pn cipher_and_tag_len m /\
  begin
    let bplain = B.gsub dst (Secret.reveal (header_len h)) (Secret.reveal cipher_and_tag_len `U32.sub` U32.uint_to_t (SAEAD.tag_length a)) in
    B.modifies (B.loc_buffer bplain `B.loc_union` AEAD.footprint m s) m m' /\
    AEAD.invariant m' s /\ AEAD.footprint m' s == AEAD.footprint m s /\
    AEAD.preserves_freeable s m m' /\
    AEAD.as_kv (B.deref m' s) == AEAD.as_kv (B.deref m s) /\
    begin match res, Spec.payload_decrypt a (AEAD.as_kv (B.deref m s)) (B.as_seq m siv) (g_header h m pn) (B.as_seq m (B.gsub dst (Secret.reveal (header_len h)) (Secret.reveal cipher_and_tag_len))) with
    | Success, Some plain ->
True //      B.as_seq m' bplain `Seq.equal` plain
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
  (h: header { ~ (is_retry h) })
  (pn: PN.packet_number_t)
  (cipher_and_tag_len: Secret.uint32)
: HST.Stack error_code
  (requires (fun m ->
    payload_decrypt_pre a s siv dst h pn cipher_and_tag_len m
  ))
  (ensures (fun m res m' ->
    payload_decrypt_post a s siv dst h pn cipher_and_tag_len m res m'
  ))
= 
  let m0 = HST.get () in
  let hlen = header_len h in
  QUIC.Impl.Header.Parse.header_len_correct h m0 pn;
  let pn_len = pn_length h in
  let gh = Ghost.hide (g_header h m0 pn) in
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
  | Success, Spec.Success h plain rem ->
    let r = B.deref m' dst_hdr in
    let h = r.header in
    header_live h m' /\
    r.header_len == header_len h /\
    Secret.v r.plain_len == Seq.length plain /\
    Secret.v r.header_len + Secret.v r.plain_len == Secret.v r.total_len /\
    Secret.v r.total_len <= B.length dst /\ (
      let dst_mod = B.gsub dst 0ul (Secret.reveal r.total_len) in
      B.modifies (AEAD.footprint m aead `B.loc_union` CTR.footprint m ctr `B.loc_union` B.loc_buffer dst_hdr `B.loc_union` B.loc_buffer dst_mod) m m' /\
      B.as_seq m' dst `Seq.equal` (QUIC.Spec.Header.Parse.format_header (g_header h m' r.pn) `Seq.append` plain `Seq.append` rem)
    )
  | _ -> False
  end

(*
#push-options "--z3rlimit 64"
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
      let res = SecretBuffer.with_whole_buffer_hide_weak_modifies
        #error_code
        dst
        m1
        (AEAD.footprint m0 aead `B.loc_union`
          B.loc_buffer siv `B.loc_union`
          CTR.footprint m0 ctr `B.loc_union`
          B.loc_buffer hpk `B.loc_union`
          B.loc_buffer dst_hdr)
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

  
      let res = payload_decrypt a aead siv dst h pn cipher_and_tag_len in
      let plain_len = cipher_and_tag_len `Secret.sub` Secret.hide 16ul in
      let r = {
        pn = pn;
        header = h;
        header_len = hlen;
        plain_len = plain_len;
        total_len = hlen `Secret.add` plain_len;
      } in
      B.upd dst_hdr 0ul r;
      res
    end
*)    


let decrypt
  #i s dst packet len cid_len
= assume False;
  UnsupportedAlgorithm


(*



let m0 = HST.get () in
  let gh = Ghost.hide (g_header h m0 pn) in
  let fmt = Ghost.hide (QUIC.Spec.Header.Parse.format_header gh) in
  let header_len = header_len h in
  QUIC.Impl.Header.Parse.header_len_correct h m0 pn;
  QUIC.Impl.Header.Base.header_len_v h;
  let isretry = is_retry h in

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
