module QUIC.Impl.Header
friend QUIC.Spec.Header

open QUIC.Impl.Header.Base

module ParseSpec = QUIC.Spec.Header.Parse
module Spec = QUIC.Spec.Header
module PN = QUIC.Spec.PacketNumber.Base

module B = LowStar.Buffer

module Cipher = EverCrypt.Cipher
module AEAD = EverCrypt.AEAD
module HKDF = EverCrypt.HKDF

module U8 = FStar.UInt8
module HST = FStar.HyperStack.ST
module U32 = FStar.UInt32
module G = FStar.Ghost
module Seq = QUIC.Secret.Seq
module Secret = QUIC.Secret.Int
module SecretBuffer = QUIC.Secret.Buffer

module Lemmas = QUIC.Impl.Lemmas
module BF = LowParse.BitFields

(* There are a few places where EverCrypt needs public data whereas it
could/should be secret. Thus, we may need some declassification
locally using Lib.RawIntTypes, but we definitely don't want to make
secret integers globally transparent using friend *)

module ADMITDeclassify = Lib.RawIntTypes

let block_len (a: Spec.Agile.Cipher.cipher_alg):
  x:U32.t { U32.v x = Spec.Agile.Cipher.block_length a }
=
  let open Spec.Agile.Cipher in
  match a with | CHACHA20 -> 64ul | _ -> 16ul

#push-options "--z3rlimit 256"
inline_for_extraction
let block_of_sample (a: Spec.Agile.Cipher.cipher_alg)
  (dst: B.buffer Secret.uint8)
  (s: CTR.state a)
  (k: B.buffer Secret.uint8)
  (sample: B.buffer Secret.uint8):
  HST.Stack unit
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
        Spec.block_of_sample a (B.as_seq h0 k) (B.as_seq h0 sample) /\
      CTR.footprint h0 s == CTR.footprint h1 s /\
      CTR.invariant h1 s)
=
  HST.push_frame ();
  (**) let h0 = HST.get () in
  let zeroes = B.alloca (Secret.to_u8 0uy) (block_len a) in
  let dst_block = B.alloca (Secret.to_u8 0uy) (block_len a) in
  begin match a with
  | Spec.Agile.Cipher.CHACHA20 ->
      let ctr = SecretBuffer.load32_le (B.sub sample 0ul 4ul) in
      let iv = B.sub sample 4ul 12ul in
      (**) let h1 = HST.get () in
      (* EverCrypt currently does not support secret counters,
         so we need to declassify the counter value here and only here. *)
      CTR.init (G.hide a) s k iv 12ul (ADMITDeclassify.u32_to_UInt32 ctr);
      CTR.update_block (G.hide a) s dst_block zeroes;
      (**) let h2 = HST.get () in
      (**) Lemmas.seq_map2_xor0 (B.as_seq h1 dst_block)
      (**)   (Spec.Agile.Cipher.ctr_block a (B.as_seq h0 k) (B.as_seq h1 iv) (Secret.v ctr));
      (**) assert (B.as_seq h2 dst_block `Seq.equal`
      (**)   Spec.Agile.Cipher.ctr_block a (B.as_seq h0 k) (B.as_seq h1 iv) (Secret.v ctr));
      let dst_slice = B.sub dst_block 0ul 16ul in
      (**) assert (B.as_seq h2 dst_slice `Seq.equal` Seq.slice (
      (**)   Spec.Agile.Cipher.ctr_block a (B.as_seq h0 k) (B.as_seq h1 iv) (Secret.v ctr)
      (**) ) 0 16);
      B.blit dst_slice 0ul dst 0ul 16ul
  | _ ->
      let ctr = SecretBuffer.load32_be (B.sub sample 12ul 4ul) in
      let iv = B.sub sample 0ul 12ul in
      (**) let h1 = HST.get () in
      (* EverCrypt currently does not support secret counters,
         so we need to declassify the counter value here and only here. *)
      CTR.init (G.hide a) s k iv 12ul (ADMITDeclassify.u32_to_UInt32 ctr);
      CTR.update_block (G.hide a) s dst_block zeroes;
      (**) let h2 = HST.get () in
      (**) Lemmas.seq_map2_xor0 (B.as_seq h1 dst_block)
      (**)   (Spec.Agile.Cipher.ctr_block a (B.as_seq h0 k) (B.as_seq h1 iv) (Secret.v ctr));
      (**) assert (B.as_seq h2 dst_block `Seq.equal`
      (**)   Spec.Agile.Cipher.ctr_block a (B.as_seq h0 k) (B.as_seq h1 iv) (Secret.v ctr));
      let dst_slice = B.sub dst_block 0ul 16ul in
      (**) assert (B.as_seq h2 dst_slice `Seq.equal` Seq.slice (
      (**)   Spec.Agile.Cipher.ctr_block a (B.as_seq h0 k) (B.as_seq h1 iv) (Secret.v ctr)
      (**) ) 0 16);
      B.blit dst_slice 0ul dst 0ul 16ul
  end;
  HST.pop_frame ()
#pop-options

(* A more careful version of header_encrypt wrt. constant-time issues, which does not test or truncate on pn_len *)

let pn_sizemask_ct (pn_len:nat { pn_len < 4 }) : Tot (lbytes 4) =
  let open FStar.Endianness in
  FStar.Math.Lemmas.pow2_lt_compat 32 (24 - (8 `op_Multiply` pn_len));
  FStar.Endianness.n_to_be 4 (pow2 32 - pow2 (24 - (8 `op_Multiply` pn_len)))

let index_pn_sizemask_ct_right
  (pn_len: nat { pn_len < 4 })
  (i: nat {i > pn_len /\ i < 4})
: Lemma
  (Seq.index (pn_sizemask_ct pn_len) i == 0uy)
= let open FStar.Endianness in
  let open FStar.Math.Lemmas in
  let open FStar.Mul in
  pow2_lt_compat 32 (24 - (8 `op_Multiply` pn_len));
  pow2_plus (24 - (8 * pn_len)) (8 * (pn_len + 1));
  Lemmas.index_n_to_be_zero_right 4 (pow2 32 - pow2 (24 - (8 * pn_len))) i

let header_encrypt_ct
  (a:ea)
  (hpk: Spec.Agile.Cipher.key (Spec.Agile.AEAD.cipher_alg_of_supported_alg a))
  (h: Spec.header)
  (c: cbytes' (Spec.is_retry h))
: GTot packet
= 
  assert_norm(max_cipher_length < pow2 62);
  let r = ParseSpec.format_header h `Seq.append` c in
  if Spec.is_retry h
  then
    r
  else
    let pn_offset = ParseSpec.pn_offset h in
    let pn_len = Secret.v (Spec.pn_length h) - 1 in
    let sample = Seq.seq_hide (Seq.slice c (3-pn_len) (19-pn_len)) in
    let mask = Seq.seq_reveal (Spec.block_of_sample (Spec.Agile.AEAD.cipher_alg_of_supported_alg a) hpk sample) in
    let pnmask = Lemmas.and_inplace (Seq.slice mask 1 5) (pn_sizemask_ct pn_len) 0 in
    let f = Seq.index r 0 in
    let protected_bits = if Spec.MShort? h then 5 else 4 in
    let f' = BF.set_bitfield (U8.v f) 0 protected_bits (BF.get_bitfield (U8.v f `FStar.UInt.logxor` U8.v (Seq.index mask 0)) 0 protected_bits) in
    let r = Lemmas.xor_inplace r pnmask pn_offset in
    let r = Seq.cons (U8.uint_to_t f') (Seq.slice r 1 (Seq.length r)) in
    r

#push-options "--z3rlimit 256"

let header_encrypt_ct_correct
  (a:ea)
  (hpk: Spec.Agile.Cipher.key (Spec.Agile.AEAD.cipher_alg_of_supported_alg a))
  (h: Spec.header)
  (c: cbytes' (Spec.is_retry h))
: Lemma
  (header_encrypt_ct a hpk h c `Seq.equal` Spec.header_encrypt a hpk h c)
=
  assert_norm(max_cipher_length < pow2 62);
  let r = ParseSpec.format_header h `Seq.append` c in
  if Spec.is_retry h
  then ()
  else begin
    let pn_offset = ParseSpec.pn_offset h in
    let pn_len = Secret.v (ParseSpec.pn_length h) - 1 in
    let sample = Seq.seq_hide (Seq.slice c (3-pn_len) (19-pn_len)) in
    let mask = Seq.seq_reveal (Spec.block_of_sample (Spec.Agile.AEAD.cipher_alg_of_supported_alg a) hpk sample) in
    let pnmask_ct = Lemmas.and_inplace (Seq.slice mask 1 5) (pn_sizemask_ct pn_len) 0 in
    let pnmask_naive = Lemmas.and_inplace (Seq.slice mask 1 (pn_len + 2)) (Spec.pn_sizemask pn_len) 0 in
    Lemmas.pointwise_op_split U8.logand (Seq.slice mask 1 5) (pn_sizemask_ct pn_len) 0 (pn_len + 1);
    assert (pnmask_naive `Seq.equal` Seq.slice pnmask_ct 0 (pn_len + 1));
    Seq.lemma_split r (pn_offset + pn_len + 1);
    Lemmas.pointwise_op_split U8.logxor r pnmask_ct pn_offset (pn_offset + pn_len + 1);
    Lemmas.pointwise_op_split U8.logxor r pnmask_naive pn_offset (pn_offset + pn_len + 1);
    Lemmas.pointwise_op_empty U8.logxor (Seq.slice r (pn_offset + pn_len + 1) (Seq.length r)) (Seq.slice pnmask_naive (pn_len + 1) (Seq.length pnmask_naive)) 0;
    Lemmas.xor_inplace_zero (Seq.slice r (pn_offset + pn_len + 1) (Seq.length r)) (Seq.slice pnmask_ct (pn_len + 1) 4)
      (fun i ->
        Lemmas.and_inplace_zero
          (Seq.slice mask (pn_len + 2) 5)
          (Seq.slice (pn_sizemask_ct pn_len) (pn_len + 1) 4)
          (fun j -> index_pn_sizemask_ct_right pn_len (j + (pn_len + 1)))
          i
      )
      0
  end

#pop-options

let header_encrypt_ct_secret_preserving_not_retry_spec
  (a:ea)
  (hpk: Spec.Agile.Cipher.key (Spec.Agile.AEAD.cipher_alg_of_supported_alg a))
  (h: Spec.header { ~ (Spec.is_retry h) })
  (r: Seq.seq Secret.uint8 {
    Seq.length r >= ParseSpec.pn_offset h + 20
  })
: GTot (Seq.seq Secret.uint8)
= 
  let pn_offset = ParseSpec.pn_offset h in
  let pn_len = Secret.v (Spec.pn_length h) - 1 in
  let sample = (Seq.slice r (pn_offset + 4) (pn_offset + 20)) in
  let mask = (Spec.block_of_sample (Spec.Agile.AEAD.cipher_alg_of_supported_alg a) hpk sample) in
  let pnmask = Lemmas.secret_and_inplace (Seq.slice mask 1 5) (Seq.seq_hide (pn_sizemask_ct pn_len)) 0 in
  let f = Seq.index r 0 in
  let protected_bits = if Spec.MShort? h then 5ul else 4ul in
  let f' = Secret.set_bitfield f 0ul protected_bits (Secret.get_bitfield (f `Secret.logxor` Seq.index mask 0) 0ul protected_bits) in
  let r = Lemmas.secret_xor_inplace r pnmask pn_offset in
  let r = Seq.cons f' (Seq.slice r 1 (Seq.length r)) in
  r

#push-options "--z3rlimit 256 --query_stats --z3cliopt smt.arith.nl=false --fuel 2 --ifuel 2"

#restart-solver

let header_encrypt_ct_secret_preserving_not_retry_spec_correct
  (a:ea)
  (hpk: Spec.Agile.Cipher.key (Spec.Agile.AEAD.cipher_alg_of_supported_alg a))
  (h: Spec.header)
  (c: cbytes)
: Lemma
  (requires (
    (~ (Spec.is_retry h))
  ))
  (ensures (
    let r = ParseSpec.format_header h `Seq.append` c in
    Seq.length r >= ParseSpec.pn_offset h + 20 /\
    Spec.header_encrypt a hpk h c == Seq.seq_reveal (header_encrypt_ct_secret_preserving_not_retry_spec a hpk h (Seq.seq_hide r))
  ))
= header_encrypt_ct_correct a hpk h c;
  let fmt = ParseSpec.format_header h in
  let len = Seq.length fmt in
  let pr = fmt `Seq.append` c in
  assert (Seq.length pr >= ParseSpec.pn_offset h + 20);
  let pn_len = Secret.v (Spec.pn_length h) - 1 in
  let psample = Seq.slice c (3 - pn_len) (19 - pn_len) in
  assert (c `Seq.equal` Seq.slice pr len (Seq.length pr));
  let pn_off = ParseSpec.pn_offset h in
  assert (pn_off + pn_len + 1 == len);
  assert (c == Seq.slice pr (pn_off + pn_len + 1) (Seq.length pr));
  Seq.slice_slice pr (pn_off + pn_len + 1) (Seq.length pr) (3 - pn_len) (19 - pn_len);
  assert (psample == Seq.slice pr (pn_off + 4) (pn_off + 20));
  let r = Seq.seq_hide #Secret.U8 pr in
  let sample = Seq.slice r (pn_off + 4) (pn_off + 20) in
  assert (sample == Seq.seq_hide #Secret.U8 psample);
  let mask = Spec.block_of_sample (Spec.Agile.AEAD.cipher_alg_of_supported_alg a) hpk sample in
  let pmask = Seq.seq_reveal mask in
  assert (mask == Seq.seq_hide pmask);
  let mask15 = Seq.slice mask 1 5 in
  let ppnszmask = pn_sizemask_ct pn_len in
  let pnszmask = Seq.seq_hide ppnszmask in
  let pnmask = Lemmas.secret_and_inplace mask15 pnszmask 0 in
  let pmask15 = Seq.slice pmask 1 5 in
  let ppnmask = Lemmas.and_inplace pmask15 ppnszmask 0 in
  Lemmas.secret_and_inplace_eq mask15 pnszmask 0;
  assert (pnmask == Seq.seq_hide #Secret.U8 ppnmask);
  let f = Seq.index r 0 in
  let pf : Secret.uint_t Secret.U8 Secret.PUB = Seq.index pr 0 in
  assert (f == Secret.hide #Secret.U8 #Secret.PUB pf);
  let protected_bits = if Spec.MShort? h then 5ul else 4ul in
  let pf' = U8.uint_to_t (BF.set_bitfield (U8.v pf) 0 (U32.v protected_bits) (BF.get_bitfield (U8.v pf `FStar.UInt.logxor` U8.v (Seq.index pmask 0)) 0 (U32.v protected_bits))) in
  let f' = Secret.set_bitfield f 0ul protected_bits (Secret.get_bitfield (f `Secret.logxor` Seq.index mask 0) 0ul protected_bits) in
  assert (U8.v pf' == Secret.v f');
  assert (f' == Secret.hide #Secret.U8 pf');
  let pr1 = Lemmas.xor_inplace pr ppnmask pn_off in
  let r1 = Lemmas.secret_xor_inplace r pnmask pn_off in
  Lemmas.secret_xor_inplace_eq r pnmask pn_off;
  assert (r1 == Seq.seq_hide #Secret.U8 pr1);
  let r2 = Seq.cons f' (Seq.slice r1 1 (Seq.length r1)) in
  let pr2 = Seq.cons pf' (Seq.slice pr1 1 (Seq.length pr1)) in
  Seq.cons_seq_hide #Secret.U8 pf' (Seq.slice pr1 1 (Seq.length pr1));
  assert (r2 == Seq.seq_hide #Secret.U8 pr2)

#pop-options

inline_for_extraction
noextract
let pn_sizemask (dst: B.buffer Secret.uint8) (pn_len: PN.packet_number_length_t): HST.Stack unit
  (requires fun h0 ->
    B.live h0 dst /\ B.length dst == 4)
  (ensures fun h0 _ h1 ->
    B.as_seq h1 dst `Seq.equal` Seq.seq_hide (pn_sizemask_ct (Secret.v pn_len - 1)) /\
    B.(modifies (loc_buffer dst) h0 h1))
= admit ()

#push-options "--z3rlimit 512 --query_stats --z3cliopt smt.arith.nl=false --fuel 2 --ifuel 1"

#restart-solver

let header_encrypt_ct_secret_preserving_not_retry
  (a: ea)
  (s: CTR.state (Spec.Agile.AEAD.cipher_alg_of_supported_alg a))
  (k: B.buffer Secret.uint8)
  (h: Ghost.erased Spec.header)
  (is_short: bool)
  (pn_offset: U32.t)
  (pn_len: PN.packet_number_length_t)
  (dst: B.buffer Secret.uint8)
: HST.Stack unit
  (requires (fun m ->
    let fmt = (Parse.format_header h) in
    let hlen = Seq.length fmt in
    B.all_live m [B.buf k; B.buf dst] /\
    CTR.invariant m s /\
    B.all_disjoint
      [ CTR.footprint m s; B.loc_buffer k; B.loc_buffer dst] /\
    B.length k == Spec.Agile.Cipher.key_length (Spec.Agile.AEAD.cipher_alg_of_supported_alg a) /\
    (~ (Spec.is_retry h)) /\
    is_short == (Spec.MShort? h) /\
    U32.v pn_offset == Parse.pn_offset h /\
    pn_len == Parse.pn_length h /\
    hlen + 19 <= B.length dst /\
    Seq.slice (Seq.seq_reveal #Secret.U8 (B.as_seq m dst)) 0 hlen == fmt
  ))
  (ensures (fun m _ m' ->
    B.modifies (B.loc_buffer dst `B.loc_union` CTR.footprint m s) m m' /\
    CTR.invariant m' s /\
    CTR.footprint m s == CTR.footprint m' s /\
    header_encrypt_ct_secret_preserving_not_retry_spec a (B.as_seq m k) h (B.as_seq m dst) == B.as_seq m' dst
  ))
= assert (U32.v pn_offset + 20 <= B.length dst);
  let m0 = HST.get () in
  HST.push_frame ();
  let m01 = HST.get () in
  let mask = B.alloca (Secret.to_u8 0uy) 16ul in
  B.loc_unused_in_not_unused_in_disjoint m01;
  let m02 = HST.get () in
  B.loc_unused_in_not_unused_in_disjoint m02;
  let pn_sm = B.alloca (Secret.to_u8 0uy) 4ul in
  let m03 = HST.get () in
  assert (B.loc_disjoint (B.loc_buffer mask) (B.loc_buffer pn_sm));
  assert (CTR.footprint m03 s == CTR.footprint m0 s);
  assert (B.loc_disjoint (B.loc_buffer mask `B.loc_union` B.loc_buffer pn_sm) (CTR.footprint m0 s `B.loc_union` B.loc_buffer k `B.loc_union` B.loc_buffer dst));
  let sample = B.sub dst (pn_offset `U32.add` 4ul) 16ul in
  let m1 = HST.get () in
  let gsample = Ghost.hide (Seq.slice (B.as_seq m0 dst) (U32.v pn_offset + 4) (U32.v pn_offset + 20)) in
  assert (B.as_seq m1 sample == Ghost.reveal gsample);
  block_of_sample (Spec.Agile.AEAD.cipher_alg_of_supported_alg a) mask s k sample;
  let m2 = HST.get () in
  let gmask = Ghost.hide (Spec.block_of_sample (Spec.Agile.AEAD.cipher_alg_of_supported_alg a) (B.as_seq m0 k) gsample) in
  assert (B.as_seq m2 mask == Ghost.reveal gmask);
  pn_sizemask pn_sm pn_len;
  let m3 = HST.get () in
  assert (B.as_seq m3 mask == Ghost.reveal gmask);
  let gpn_sm = Ghost.hide (Seq.seq_hide #Secret.U8 (pn_sizemask_ct (Secret.v pn_len - 1))) in
  assert (B.as_seq m3 pn_sm == Ghost.reveal gpn_sm);
  let pnmask = B.sub mask 1ul 4ul in
  Lemmas.op_inplace pnmask pn_sm 4ul 0ul (Secret.logand #Secret.U8 #Secret.SEC);
  let m4 = HST.get () in
  let gpnmask = Ghost.hide (Lemmas.secret_and_inplace (Seq.slice gmask 1 5) gpn_sm 0) in
  assert (B.as_seq m4 pnmask == Ghost.reveal gpnmask);
  let protected_bits = if is_short then 5ul else 4ul in
  let mask_0 = B.index mask 0ul in
  assert (mask_0 == Seq.index (B.as_seq m4 (B.gsub mask 0ul 1ul)) 0);
  assert (mask_0 == Seq.index gmask 0);
  let f_ = B.index dst 0ul in
  assert (f_ == Seq.index (B.as_seq m0 dst) 0);
  let f' = Secret.set_bitfield f_ 0ul protected_bits (Secret.get_bitfield (f_ `Secret.logxor` mask_0) 0ul protected_bits) in
  Lemmas.op_inplace dst pnmask 4ul pn_offset (Secret.logxor #Secret.U8 #Secret.SEC);
  let m5 = HST.get () in
  let gr1 = Ghost.hide (Lemmas.secret_xor_inplace (B.as_seq m0 dst) gpnmask (U32.v pn_offset)) in
  assert (B.as_seq m5 dst == Ghost.reveal gr1);
  B.upd dst 0ul f' ;
  HST.pop_frame ();
  let m6 = HST.get () in
  assert (B.as_seq m6 dst `Seq.equal` (f' `Seq.cons` Seq.slice (Ghost.reveal gr1) 1 (B.length dst)))

(*
let open FStar.Mul in
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
*)

#restart-solver

let header_encrypt
  a s k dst h is_short is_retry public_len pn_len
= if is_retry
  then ()
  else begin
    let m = HST.get () in
    let hpk = Ghost.hide (B.as_seq m k) in
    let fmt = Ghost.hide (ParseSpec.format_header (G.reveal h)) in
    let cipher = Ghost.hide (Seq.slice (B.as_seq m dst) (Seq.length fmt)  (B.length dst)) in
    assert (B.as_seq m dst `Seq.equal` (fmt `Seq.append` cipher));
    header_encrypt_ct_secret_preserving_not_retry_spec_correct a hpk h cipher;
    assert (U32.v public_len + 20 <= B.length dst);
    let post (cont: Seq.lseq Secret.uint8 (B.length dst)) (m1: HS.mem) : GTot Type0 =
      header_encrypt_ct_secret_preserving_not_retry_spec a hpk h (Seq.seq_hide (B.as_seq m dst)) == cont /\
      CTR.invariant m1 s /\
      CTR.footprint m1 s == CTR.footprint m s
    in
    SecretBuffer.with_whole_buffer_hide_weak_modifies'
      #unit
      dst
      m
      (CTR.footprint m s `B.loc_union` B.loc_buffer k)
      (CTR.footprint m s)
      true
      (fun _ cont m1 ->
        post cont m1
      )
      (fun _ bs ->
        header_encrypt_ct_secret_preserving_not_retry a s k h is_short public_len pn_len bs
      )
    ;
    let m' = HST.get () in
    assert (B.as_seq m' dst == Seq.seq_reveal (header_encrypt_ct_secret_preserving_not_retry_spec a hpk h (Seq.seq_hide (B.as_seq m dst))));
    assert (B.as_seq m' dst == Spec.header_encrypt a (B.as_seq m k) h cipher)
  end

#pop-options

(*

Secret.reveal f' `Seq.cons` (pub `Seq.append` Seq.seq_reveal pn_and_c')

  (a:ea)
  (hpk: Spec.Agile.Cipher.key (Spec.Agile.AEAD.cipher_alg_of_supported_alg a))
  (is_short: bool)
  (pn_len: PN.packet_number_length_t)
  (f: Secret.uint8)
  (pn_and_c: Seq.seq Secret.uint8 { Seq.length pn_and_c >= 20 })



let header_encrypt_ct_secret_preserving_not_retry_spec_correct
header_encrypt_ct_secret_preserving_not_retry_spec_correct
  (a:ea)
  (hpk: Spec.Agile.Cipher.key (Spec.Agile.AEAD.cipher_alg_of_supported_alg a))
  (h: Spec.header)
  (c: cbytes)
  (f: Secret.uint8)
  (pub: Seq.seq U8.t)
  (pn_and_c: Seq.seq Secret.uint8)
  
  
  
  
  
  (a:ea)
  (hpk: Spec.Agile.Cipher.key (Spec.Agile.AEAD.cipher_alg_of_supported_alg a))
  (h: Spec.header)
  (c: cbytes)
  (b: B.buffer U8.t)
: HST.Stack unit
  (requires (fun m ->
    B.live m b /\
    B.as_seq m b == ParseSpec.format_header h `Seq.append` c
  ))
  (ensures (fun m _ m' ->
    B.modifies (B.loc_buffer b)
  ))



(*

let h0 = HST.get () in
  let dst0 = B.sub dst 0ul ofs in
  let dst1 = B.sub dst ofs src_len in
  let dst2 = B.sub dst (ofs `U32.add` src_len) (dst_len `U32.sub` (ofs `U32.add` src_len)) in
  C.Loops.in_place_map2 dst1 src src_len op;
  let h1 = HST.get () in
  assert (B.modifies (B.loc_buffer dst) h0 h1);
  let post () : Lemma (
      B.as_seq h1 dst `Seq.equal`
        QUIC.Spec.Lemmas.pointwise_op op (B.as_seq h0 dst) (B.as_seq h0 src) (U32.v ofs) /\
      Seq.slice (B.as_seq h0 dst) 0 (U32.v ofs) `Seq.equal`
        Seq.slice (B.as_seq h1 dst) 0 (U32.v ofs) /\
      Seq.slice (B.as_seq h0 dst) (U32.v (ofs `U32.add` src_len)) (U32.v dst_len) `Seq.equal`
      Seq.slice (B.as_seq h1 dst) (U32.v (ofs `U32.add` src_len)) (U32.v dst_len)
  )
  =
    let r1 = B.as_seq h1 dst in
    Lemmas.lemma_slice3 (B.as_seq h1 dst) (U32.v ofs) (U32.v (ofs `U32.add` src_len));
    let r2 =
      Seq.slice (B.as_seq h1 dst) 0 (U32.v ofs) `Seq.append`
      (Seq.slice (B.as_seq h1 dst) (U32.v ofs) (U32.v (ofs `U32.add` src_len))) `Seq.append`
      (Seq.slice (B.as_seq h1 dst) (U32.v (ofs `U32.add` src_len)) (B.length dst))
    in
    assert (r1 `Seq.equal` r2);
    let r3 = 
      Seq.slice (B.as_seq h0 dst) 0 (U32.v ofs) `Seq.append`
      (Seq.slice (B.as_seq h1 dst) (U32.v ofs) (U32.v (ofs `U32.add` src_len))) `Seq.append`
      (Seq.slice (B.as_seq h0 dst) (U32.v (ofs `U32.add` src_len)) (B.length dst))
    in
    assert (r2 `Seq.equal` r3);
    Lemmas.pointwise_seq_map2 op (B.as_seq h0 dst1) (B.as_seq h0 src) 0;
    let r4 =
      Seq.slice (B.as_seq h0 dst) 0 (U32.v ofs) `Seq.append`
      (QUIC.Spec.Lemmas.pointwise_op op
        (Seq.slice (B.as_seq h0 dst) (U32.v ofs) (U32.v (ofs `U32.add` src_len)))
        (B.as_seq h0 src)
        0) `Seq.append`
      (Seq.slice (B.as_seq h0 dst) (U32.v (ofs `U32.add` src_len)) (B.length dst))
    in
    assert (r3 `Seq.equal` r4);
    QUIC.Spec.Lemmas.pointwise_op_suff op (Seq.slice (B.as_seq h0 dst) 0 (U32.v ofs))
      (Seq.slice (B.as_seq h0 dst) (U32.v ofs) (U32.v (ofs `U32.add` src_len)))
      (B.as_seq h0 src)
      (U32.v ofs);
    let r5 =
      QUIC.Spec.Lemmas.pointwise_op op
        (Seq.append (Seq.slice (B.as_seq h0 dst) 0 (U32.v ofs))
          (Seq.slice (B.as_seq h0 dst) (U32.v ofs) (U32.v (ofs `U32.add` src_len))))
        (B.as_seq h0 src)
        (U32.v ofs) `Seq.append`
      (Seq.slice (B.as_seq h0 dst) (U32.v (ofs `U32.add` src_len)) (B.length dst))
    in
    assert (r4 `Seq.equal` r5);
    Lemmas.lemma_slice1 (B.as_seq h0 dst) (U32.v ofs) (U32.v (ofs `U32.add` src_len));    
    let r6 =
      QUIC.Spec.Lemmas.pointwise_op op
        (Seq.slice (B.as_seq h0 dst) 0 (U32.v (ofs `U32.add` src_len)))
        (B.as_seq h0 src)
        (U32.v ofs) `Seq.append`
      (Seq.slice (B.as_seq h0 dst) (U32.v (ofs `U32.add` src_len)) (B.length dst))
    in
    assert (r5 `Seq.equal` r6);
    QUIC.Spec.Lemmas.pointwise_op_pref op
      (Seq.slice (B.as_seq h0 dst) 0 (U32.v (ofs `U32.add` src_len)))
      (Seq.slice (B.as_seq h0 dst) (U32.v (ofs `U32.add` src_len)) (B.length dst))
      (B.as_seq h0 src)
      (U32.v ofs);
    let r7 =
        QUIC.Spec.Lemmas.pointwise_op op
      (Seq.slice (B.as_seq h0 dst) 0 (U32.v (ofs `U32.add` src_len)) `Seq.append`
      (Seq.slice (B.as_seq h0 dst) (U32.v (ofs `U32.add` src_len)) (B.length dst)))
      (B.as_seq h0 src)
      (U32.v ofs)
    in
    assert (r6 `Seq.equal` r7);
    Lemmas.lemma_slice (B.as_seq h0 dst) (U32.v (ofs `U32.add` src_len));
    let r8 =
      QUIC.Spec.Lemmas.pointwise_op op
        (B.as_seq h0 dst)
        (B.as_seq h0 src)
        (U32.v ofs)
    in
    assert (r7 `Seq.equal` r8)
  in
  post ()

(*


  let h1 = HST.get () in  
  calc (Seq.equal) {
  (Seq.equal) {  }
  (Seq.equal) {  }
  (Seq.equal) {  }
  (Seq.equal) { 
  }
  (Seq.equal) {  }
  }
#pop-options

(*
open QUIC.Impl.Base
open QUIC.Spec.Header

open QUIC.Impl.PacketNumber

open FStar.HyperStack.ST

open LowParse.Spec.Int
open LowParse.Spec.BitSum

open LowParse.Spec.BoundedInt

module U64 = FStar.UInt64
module U32 = FStar.UInt32
module U16 = FStar.UInt16
module U8 = FStar.UInt8
module Cast = FStar.Int.Cast

module FB = FStar.Bytes
open LowParse.Spec.Bytes

module LC = LowParse.Low.Combinators
module LB = LowParse.Low.Bytes
module LI = LowParse.Low.BoundedInt
module LJ = LowParse.Low.Int
module LL = LowParse.Low.BitSum

open QUIC.Impl.VarInt

inline_for_extraction
let validate_common_long : LC.validator parse_common_long =
  LB.validate_u32 () `LC.validate_nondep_then` (LB.validate_bounded_vlbytes 0 20 `LC.validate_nondep_then` LB.validate_bounded_vlbytes 0 20)

inline_for_extraction
noextract
let validate_payload_length_pn
  (last: last_packet_number_t)
  (pn_length: packet_number_length_t)
: Tot (LC.validator (parse_payload_length_pn last pn_length))
= LC.validate_filter validate_varint read_varint (payload_and_pn_length_prop pn_length) (fun x -> payload_and_pn_length_prop pn_length x) `LC.validate_nondep_then` validate_packet_number last pn_length

#push-options "--z3rlimit 64 --max_fuel 8 --max_ifuel 8 --initial_fuel 8 --initial_ifuel 8"

[@filter_bitsum'_t_attr]
inline_for_extraction
noextract
let validate_header_body_cases
  (short_dcid_len: short_dcid_len_t)
  (last: last_packet_number_t)
  (k' : bitsum'_key_type first_byte)
: Tot (LC.validator (dsnd (parse_header_body short_dcid_len last k')))
= match coerce (bitsum'_key_type first_byte) k' with
  | (| Short, (| (), (| (), (| pn_length, () |) |) |) |) ->
    LC.validate_weaken (strong_parser_kind 0 20 None) (LB.validate_flbytes (U32.v short_dcid_len) short_dcid_len) () `LC.validate_nondep_then` validate_packet_number last pn_length
  | (| Long, (| (), (| Initial, (| (), (| pn_length, () |) |) |) |) |) ->
    validate_common_long `LC.validate_nondep_then` (LB.validate_bounded_vlgenbytes 0 0ul token_max_len (U32.uint_to_t token_max_len) (validate_bounded_varint 0ul (U32.uint_to_t token_max_len)) (read_bounded_varint 0 token_max_len) `LC.validate_nondep_then` validate_payload_length_pn last pn_length)
  | (| Long, (| (), (| ZeroRTT, (| (), (| pn_length, () |) |) |) |) |) ->
    validate_common_long `LC.validate_nondep_then` validate_payload_length_pn last pn_length
  | (| Long, (| (), (| Handshake, (| (), (| pn_length, () |) |) |) |) |) ->
    validate_common_long `LC.validate_nondep_then` validate_payload_length_pn last pn_length
  | (| Long, (| (), (| Retry, () |) |) |) ->
    validate_common_long `LC.validate_nondep_then` LB.validate_bounded_vlbytes 0 20

#pop-options

(* I can no longer use mk_filter_bitsum'_t' and similar automatic
   destructors/constructors by normalization, because these would
   branch on pn_len, which would no longer be constant-time. So I use
   tactics to structurally build (i.e. in a syntax-directed way)
   tailored destructors in a convenient way without the tedium of
   providing arguments every time. *)

module T = FStar.Tactics
module BF = LowParse.BitFields

inline_for_extraction
let is_fixed_bit
  (x: BF.bitfield uint8 1)
: Tot (y: bool { y == list_mem x (list_map snd fixed_bit) })
= x = 1uy

inline_for_extraction
let key_of_fixed_bit
  (x: enum_repr fixed_bit) 
: Tot (y: enum_key fixed_bit { y == enum_key_of_repr fixed_bit x })
= ()

inline_for_extraction
let are_reserved_bits
  (x: LowParse.BitFields.bitfield uint8 2)
: Tot (y: bool { y == list_mem x (list_map snd reserved_bits) })
= x = 0uy

inline_for_extraction
let key_of_reserved_bits
  (x: enum_repr reserved_bits)
: Tot (y: enum_key reserved_bits { y == enum_key_of_repr reserved_bits x })
= ()

(* this is constant-time, no longer branches on pn_len *)
inline_for_extraction
let is_packet_number_length
  (x: BF.bitfield uint8 2)
: Tot (y: bool { y == list_mem x (list_map snd packet_number_length) })
= true

(* this is constant-time, no longer branches on pn_len *)
inline_for_extraction
let key_of_packet_number_length
  (x: enum_repr packet_number_length)
: Tot (y: enum_key packet_number_length { y == enum_key_of_repr packet_number_length x })
= Cast.uint8_to_uint32 x `U32.add` 1ul

inline_for_extraction
noextract
let filter_rrpp
: filter_bitsum'_t rrpp
= _ by (
  let open FStar.Tactics in
  T.apply (`filter_bitsum'_bitsum_gen);
  T.apply (`are_reserved_bits);
  T.apply (`key_of_reserved_bits);
  let _ = T.intro () in
  T.apply (`filter_bitsum'_bitsum_gen);
  T.apply (`is_packet_number_length);
  T.apply (`key_of_packet_number_length);
  let _ = T.intro () in
  T.exact_with_ref (`filter_bitsum'_bitstop uint8)
  )

module L = FStar.List.Tot

let append_l_nil (#t: Type) (l: list t) : Tot (squash (l == l `L.append` [])) =
  L.append_l_nil l

let filter_first_byte'
: (filter_bitsum'_t first_byte)
= _ by (
  let open FStar.Tactics in
  T.apply (`filter_bitsum'_bitsum'_intro);
  T.apply (`filter_bitsum'_bitsum'_cons);
  (* long *)
  T.apply (`filter_bitsum'_bitsum_gen);
  T.exact (`is_fixed_bit);
  T.exact (`key_of_fixed_bit);
  let _ = T.intro () in
  T.apply (`filter_bitsum'_bitsum'_intro);
  T.apply (`filter_bitsum'_bitsum'_cons);
  (* initial *)
  T.exact_with_ref (`filter_rrpp);
  T.apply (`filter_bitsum'_bitsum'_cons);
  (* ZeroRTT *)
  T.exact_with_ref (`filter_rrpp);
  T.apply (`filter_bitsum'_bitsum'_cons);
  (* Handshake *)
  T.exact_with_ref (`filter_rrpp);
  T.apply (`filter_bitsum'_bitsum'_cons);
  (* Retry *)
  T.apply (`filter_bitsum'_bitfield);
  T.exact_with_ref (`filter_bitsum'_bitstop uint8);
  T.apply (`filter_bitsum'_bitsum'_nil);
  T.apply (`append_l_nil);
  T.apply (`filter_bitsum'_bitsum'_cons);
  (* short *)
  T.apply (`filter_bitsum'_bitsum_gen);
  T.exact (`is_fixed_bit);
  T.exact (`key_of_fixed_bit);
  let _ = T.intro () in
  T.apply (`filter_bitsum'_bitfield);
  T.apply (`filter_bitsum'_bitsum_gen);
  T.apply (`are_reserved_bits);
  T.apply (`key_of_reserved_bits);
  let _ = T.intro () in
  T.apply (`filter_bitsum'_bitfield);
  T.apply (`filter_bitsum'_bitsum_gen);
  T.apply (`is_packet_number_length);
  T.apply (`key_of_packet_number_length);
  let _ = T.intro () in
  T.exact_with_ref (`filter_bitsum'_bitstop uint8);
  T.apply (`filter_bitsum'_bitsum'_nil);
  T.apply (`append_l_nil)
  )

inline_for_extraction
let filter_first_byte
  (short_dcid_len: short_dcid_len_t)
  (last: last_packet_number_t)
: Tot (filter_bitsum'_t first_byte)
= coerce (filter_bitsum'_t first_byte) filter_first_byte'

(* same here *)

inline_for_extraction
noextract
let validate_rrpp
: LL.validate_bitsum_cases_t rrpp
= _ by (
  let open FStar.Tactics in
  T.apply (`LL.validate_bitsum_cases_bitsum_gen);
  T.exact (`key_of_reserved_bits);
  let _ = T.intro () in
  T.apply (`LL.validate_bitsum_cases_bitsum_gen);
  T.apply (`key_of_packet_number_length);
  let _ = T.intro () in
  T.exact_with_ref (`LL.validate_bitsum_cases_bitstop uint8)
)

inline_for_extraction
noextract
let mk_validate_header_body_cases'
: LL.validate_bitsum_cases_t first_byte
= _ by (
  let open FStar.Tactics in
  T.apply (`LL.validate_bitsum_cases_bitsum'_intro);
  T.apply (`LL.validate_bitsum_cases_bitsum'_cons);
  (* long *)
  T.apply (`LL.validate_bitsum_cases_bitsum_gen);
  T.exact (`key_of_fixed_bit);
  let _ = T.intro () in
  T.apply (`LL.validate_bitsum_cases_bitsum'_intro);
  T.apply (`LL.validate_bitsum_cases_bitsum'_cons);
  (* initial *)
  T.exact_with_ref (`validate_rrpp);
  T.apply (`LL.validate_bitsum_cases_bitsum'_cons);
  (* ZeroRTT *)
  T.exact_with_ref (`validate_rrpp);
  T.apply (`LL.validate_bitsum_cases_bitsum'_cons);
  (* Handshake *)
  T.exact_with_ref (`validate_rrpp);
  T.apply (`LL.validate_bitsum_cases_bitsum'_cons);
  (* Retry *)
  T.apply (`LL.validate_bitsum_cases_bitfield);
  T.exact_with_ref (`LL.validate_bitsum_cases_bitstop uint8);
  T.apply (`LL.validate_bitsum_cases_bitsum'_nil);
  T.apply (`append_l_nil);
  T.apply (`LL.validate_bitsum_cases_bitsum'_cons);
  (* short *)
  T.apply (`LL.validate_bitsum_cases_bitsum_gen);
  T.exact (`key_of_fixed_bit);
  let _ = T.intro () in
  T.apply (`LL.validate_bitsum_cases_bitfield);
  T.apply (`LL.validate_bitsum_cases_bitsum_gen);
  T.apply (`key_of_reserved_bits);
  let _ = T.intro () in
  T.apply (`LL.validate_bitsum_cases_bitfield);
  T.apply (`LL.validate_bitsum_cases_bitsum_gen);
  T.apply (`key_of_packet_number_length);
  let _ = T.intro () in
  T.exact_with_ref (`LL.validate_bitsum_cases_bitstop uint8);
  T.apply (`LL.validate_bitsum_cases_bitsum'_nil);
  T.apply (`append_l_nil)
  )

inline_for_extraction
noextract
let mk_validate_header_body_cases
  (short_dcid_len: short_dcid_len_t)
  (last: last_packet_number_t)
: LL.validate_bitsum_cases_t first_byte
= coerce (LL.validate_bitsum_cases_t first_byte) mk_validate_header_body_cases' 

let validate_header
  (short_dcid_len: short_dcid_len_t)
  (last: last_packet_number_t)
: Tot (LL.validator (lp_parse_header short_dcid_len last))
= LL.validate_bitsum
    first_byte
    (first_byte_of_header short_dcid_len last)
    (header_body_type short_dcid_len last)
    (header_synth short_dcid_len last)
    (LJ.validate_u8 ())
    LJ.read_u8
    (filter_first_byte short_dcid_len last)
    (parse_header_body short_dcid_len last)
    (validate_header_body_cases short_dcid_len last)
    (mk_validate_header_body_cases short_dcid_len last)


module Impl = QUIC.Impl.Base

(* same here *)

inline_for_extraction
noextract
let destr_rrpp
: destr_bitsum'_t rrpp
= _ by (
  let open FStar.Tactics in
  T.apply (`destr_bitsum'_bitsum_gen);
  T.exact (`key_of_reserved_bits);
  let _ = T.intro () in
  T.apply (`destr_bitsum'_bitsum_gen);
  T.apply (`key_of_packet_number_length);
  let _ = T.intro () in
  T.exact_with_ref (`destr_bitsum'_bitstop uint8)
)

inline_for_extraction
noextract
let destr_first_byte
: (destr_bitsum'_t first_byte <: Type u#1)
= _ by (
  let open FStar.Tactics in
  T.apply (`destr_bitsum'_bitsum_intro);
  T.apply (`destr_bitsum'_bitsum_cons);
  (* long *)
  T.apply (`destr_bitsum'_bitsum_gen);
  T.exact (`key_of_fixed_bit);
  let _ = T.intro () in
  T.apply (`destr_bitsum'_bitsum_intro);
  T.apply (`destr_bitsum'_bitsum_cons);
  (* initial *)
  T.exact_with_ref (`destr_rrpp);
  T.apply (`destr_bitsum'_bitsum_cons);
  (* ZeroRTT *)
  T.exact_with_ref (`destr_rrpp);
  T.apply (`destr_bitsum'_bitsum_cons);
  (* Handshake *)
  T.exact_with_ref (`destr_rrpp);
  T.apply (`destr_bitsum'_bitsum_cons_nil);
  (* Retry *)
  T.apply (`destr_bitsum'_bitfield);
  T.exact_with_ref (`destr_bitsum'_bitstop uint8);
  T.apply (`destr_bitsum'_bitsum_cons_nil);
  (* short *)
  T.apply (`destr_bitsum'_bitsum_gen);
  T.exact (`key_of_fixed_bit);
  let _ = T.intro () in
  T.apply (`destr_bitsum'_bitfield);
  T.apply (`destr_bitsum'_bitsum_gen);
  T.apply (`key_of_reserved_bits);
  let _ = T.intro () in
  T.apply (`destr_bitsum'_bitfield);
  T.apply (`destr_bitsum'_bitsum_gen);
  T.apply (`key_of_packet_number_length);
  let _ = T.intro () in
  T.exact_with_ref (`destr_bitsum'_bitstop uint8)
  )

inline_for_extraction
noextract
let read_header_body_t
  (sl: LL.slice (B.trivial_preorder _) (B.trivial_preorder _))
  (cid_len: U32.t { U32.v cid_len <= 20 } )
  (last: uint62_t { U64.v last + 1 < pow2 62 })
  (tg: bitsum'_type first_byte)
: Tot (Type u#0)
= (len: U32.t) ->
  HST.Stack (option (Impl.header & uint62_t))
  (requires (fun h ->
    let p = dsnd (parse_header_body cid_len last (bitsum'_key_of_t first_byte tg)) in
    LL.valid_pos (lp_parse_header cid_len last) h sl 0ul len /\
    1 <= U32.v sl.LL.len /\
    LL.valid_pos p h sl 1ul len /\
    LL.contents (lp_parse_header cid_len last) h sl 0ul == (header_synth cid_len last).f tg (LL.contents p h sl 1ul)
  ))
  (ensures (fun h res h' ->
    let hd = LL.contents (lp_parse_header cid_len last) h sl 0ul in
    B.modifies B.loc_none h h' /\
    (None? res <==> ((~ (Spec.is_retry hd)) /\ U32.v len + 4 > U32.v sl.LL.len)) /\
    begin match res with
      | None -> True
      | Some (x, pn) ->
        Impl.header_live x h' /\
        LL.loc_slice_from_to sl 0ul len `B.loc_includes` Impl.header_footprint x /\
        Impl.g_header x h' pn == hd
    end
  ))

#push-options "--z3rlimit 64 --z3cliopt smt.arith.nl=false --using_facts_from '*,-FStar.Int.Cast' --query_stats --max_fuel 9 --initial_fuel 9 --max_ifuel 9 --initial_ifuel 9 --query_stats"

let read_header_body_short
  (sl: LL.slice (B.trivial_preorder _) (B.trivial_preorder _))
  (cid_len: U32.t { U32.v cid_len <= 20 } )
  (last: uint62_t { U64.v last + 1 < pow2 62 })
  (spin: BF.bitfield uint8 1)
  (key_phase: BF.bitfield uint8 1)
  (pn_length: packet_number_length_t)
: Tot (read_header_body_t sl cid_len last (| Short, (| (), (spin, (| (), (key_phase, (| pn_length, () |) ) |) ) |) |) )
= fun len ->
    let h0 = HST.get () in
    assert_norm (bitsum'_key_of_t first_byte (| Short, (| (), (spin, (| (), (key_phase, (| pn_length, () |) ) |) ) |) |) == (| Short, (| (), (| (), (| pn_length, () |) |) |) |) );
    if (sl.LL.len `U32.sub` len) `U32.lt` 4ul
    then None
    else begin
      LL.valid_nondep_then h0 (weaken (strong_parser_kind 0 20 None) (parse_flbytes (U32.v cid_len))) (parse_packet_number last pn_length) sl 1ul;
      LL.valid_weaken (strong_parser_kind 0 20 None) (parse_flbytes (U32.v cid_len)) h0 sl 1ul;
      LB.valid_flbytes_elim h0 (U32.v cid_len) sl 1ul;
      let pos = LB.jump_flbytes (U32.v cid_len) cid_len sl 1ul in
      let dcid = B.sub sl.LL.base 1ul (pos `U32.sub` 1ul) in
      let pn = read_packet_number last pn_length sl pos in
      Some (Impl.BShort (spin = 1uy) (key_phase = 1uy) dcid cid_len pn_length, pn)
    end

#pop-options

#push-options "--z3rlimit 128 --z3cliopt smt.arith.nl=false --query_stats --max_fuel 9 --initial_fuel 9 --max_ifuel 9 --initial_ifuel 9 --query_stats"

#restart-solver

let read_header_body_long_retry
  (sl: LL.slice (B.trivial_preorder _) (B.trivial_preorder _))
  (cid_len: U32.t { U32.v cid_len <= 20 } )
  (last: uint62_t { U64.v last + 1 < pow2 62 })
  (unused: BF.bitfield uint8 4)
: Tot (read_header_body_t sl cid_len last (| Long, (| (), (| Retry, (unused, ()) |) |) |) )
= fun len ->
    let h0 = HST.get () in
    assert_norm (bitsum'_key_of_t first_byte (| Long, (| (), (| Retry, (unused, ()) |) |) |)  == (| Long, (| (), (| Retry, () |) |) |) );
    LL.valid_nondep_then h0 parse_common_long (parse_bounded_vlbytes 0 20) sl 1ul;
    LL.valid_nondep_then h0 parse_u32 (parse_bounded_vlbytes 0 20 `nondep_then` parse_bounded_vlbytes 0 20) sl 1ul;
    let version = LJ.read_u32 sl 1ul in
    let pos1 = LJ.jump_u32 sl 1ul in
    LL.valid_nondep_then h0 (parse_bounded_vlbytes 0 20) (parse_bounded_vlbytes 0 20) sl pos1;
    let dcid = LB.get_vlbytes_contents 0 20 sl pos1 in
    let dcid_len = LB.bounded_vlbytes_payload_length 0 20 sl pos1 in
    let pos2 = LB.jump_bounded_vlbytes 0 20 sl pos1 in
    let scid = LB.get_vlbytes_contents 0 20 sl pos2 in
    let scid_len = LB.bounded_vlbytes_payload_length 0 20 sl pos2 in
    let pos3 = LB.jump_bounded_vlbytes 0 20 sl pos2 in
    let odcid = LB.get_vlbytes_contents 0 20 sl pos3 in
    let odcid_len = LB.bounded_vlbytes_payload_length 0 20 sl pos3 in
    let spec = Impl.BRetry unused odcid odcid_len in
    Some (Impl.BLong version dcid dcid_len scid scid_len spec, last (* dummy, this packet does not have a packet number *) )

#pop-options

#push-options "--z3rlimit 1024 --z3cliopt smt.arith.nl=false --query_stats --max_fuel 9 --initial_fuel 9 --max_ifuel 9 --initial_ifuel 9 --query_stats"

#restart-solver

let read_header_body_long_initial
  (sl: LL.slice (B.trivial_preorder _) (B.trivial_preorder _))
  (cid_len: U32.t { U32.v cid_len <= 20 } )
  (last: uint62_t { U64.v last + 1 < pow2 62 })
  (pn_length: packet_number_length_t)
: Tot (read_header_body_t sl cid_len last (| Long, (| (), (| Initial, (| (), (| pn_length, () |) |) |) |) |) )
= fun len ->
    let h0 = HST.get () in
    assert_norm (bitsum'_key_of_t first_byte (| Long, (| (), (| Initial, (| (), (| pn_length, () |) |) |) |) |) == (| Long, (| (), (| Initial, (| (), (| pn_length, () |) |) |) |) |) );
    if (sl.LL.len `U32.sub` len) `U32.lt` 4ul
    then None
    else begin
      LL.valid_nondep_then h0 parse_common_long (parse_bounded_vlgenbytes 0 token_max_len (parse_bounded_varint 0 token_max_len) `nondep_then` parse_payload_length_pn last pn_length) sl 1ul;
      LL.valid_nondep_then h0 parse_u32 (parse_bounded_vlbytes 0 20 `nondep_then` parse_bounded_vlbytes 0 20) sl 1ul;
      let version = LJ.read_u32 sl 1ul in
      let pos1 = LJ.jump_u32 sl 1ul in
      LL.valid_nondep_then h0 (parse_bounded_vlbytes 0 20) (parse_bounded_vlbytes 0 20) sl pos1;
      let dcid = LB.get_vlbytes_contents 0 20 sl pos1 in
      let dcid_len = LB.bounded_vlbytes_payload_length 0 20 sl pos1 in
      let pos2 = LB.jump_bounded_vlbytes 0 20 sl pos1 in
      let scid = LB.get_vlbytes_contents 0 20 sl pos2 in
      let scid_len = LB.bounded_vlbytes_payload_length 0 20 sl pos2 in
      let pos3 = LB.jump_bounded_vlbytes 0 20 sl pos2 in
      LL.valid_nondep_then h0 (parse_bounded_vlgenbytes 0 token_max_len (parse_bounded_varint 0 token_max_len)) (parse_payload_length_pn last pn_length) sl pos3;
      let token = LB.get_bounded_vlgenbytes_contents 0 token_max_len (read_bounded_varint 0 token_max_len) (jump_bounded_varint 0 token_max_len) sl pos3 in
      let token_len = LB.bounded_vlgenbytes_payload_length 0 token_max_len (read_bounded_varint 0 token_max_len) sl pos3 in
      let pos4 = LB.jump_bounded_vlgenbytes 0 token_max_len (jump_bounded_varint 0 token_max_len) (read_bounded_varint 0 token_max_len) sl pos3 in
      LL.valid_nondep_then h0 (parse_varint `parse_filter` payload_and_pn_length_prop pn_length) (parse_packet_number last pn_length) sl pos4;
      let payload_and_pn_length = LC.read_filter read_varint (payload_and_pn_length_prop pn_length) sl pos4 in
      let pos5 = LC.jump_filter jump_varint (payload_and_pn_length_prop pn_length) sl pos4 in
      let pn = read_packet_number last pn_length sl pos5 in
      //    assert (LL.loc_slice_from_to sl 0ul len `B.loc_includes` B.loc_buffer token);
      let spec = Impl.BInitial (payload_and_pn_length `U64.sub` Cast.uint32_to_uint64 pn_length) pn_length token token_len in
      Some (Impl.BLong version dcid dcid_len scid scid_len spec, pn)
    end

#pop-options

#push-options "--z3rlimit 512 --z3cliopt smt.arith.nl=false --query_stats --max_fuel 9 --initial_fuel 9 --max_ifuel 9 --initial_ifuel 9 --query_stats"

#restart-solver

let read_header_body_long_handshake
  (sl: LL.slice (B.trivial_preorder _) (B.trivial_preorder _))
  (cid_len: U32.t { U32.v cid_len <= 20 } )
  (last: uint62_t { U64.v last + 1 < pow2 62 })
  (pn_length: packet_number_length_t)
: Tot (read_header_body_t sl cid_len last (| Long, (| (), (| Handshake, (| (), (| pn_length, () |) |) |) |) |) )
= fun len ->
    let h0 = HST.get () in
    assert_norm (bitsum'_key_of_t first_byte (| Long, (| (), (| Handshake, (| (), (| pn_length, () |) |) |) |) |) == (| Long, (| (), (| Handshake, (| (), (| pn_length, () |) |) |) |) |) );
    if (sl.LL.len `U32.sub` len) `U32.lt` 4ul
    then None
    else begin
      LL.valid_nondep_then h0 parse_common_long (parse_payload_length_pn last pn_length) sl 1ul;
      LL.valid_nondep_then h0 parse_u32 (parse_bounded_vlbytes 0 20 `nondep_then` parse_bounded_vlbytes 0 20) sl 1ul;
      let version = LJ.read_u32 sl 1ul in
      let pos1 = LJ.jump_u32 sl 1ul in
      LL.valid_nondep_then h0 (parse_bounded_vlbytes 0 20) (parse_bounded_vlbytes 0 20) sl pos1;
      let dcid = LB.get_vlbytes_contents 0 20 sl pos1 in
      let dcid_len = LB.bounded_vlbytes_payload_length 0 20 sl pos1 in
      let pos2 = LB.jump_bounded_vlbytes 0 20 sl pos1 in
      let scid = LB.get_vlbytes_contents 0 20 sl pos2 in
      let scid_len = LB.bounded_vlbytes_payload_length 0 20 sl pos2 in
      let pos3 = LB.jump_bounded_vlbytes 0 20 sl pos2 in
      LL.valid_nondep_then h0 (parse_varint `parse_filter` payload_and_pn_length_prop pn_length) (parse_packet_number last pn_length) sl pos3;
      let payload_and_pn_length = LC.read_filter read_varint (payload_and_pn_length_prop pn_length) sl pos3 in
      let pos4 = LC.jump_filter jump_varint (payload_and_pn_length_prop pn_length) sl pos3 in
      let pn = read_packet_number last pn_length sl pos4 in
      let spec = Impl.BHandshake (payload_and_pn_length `U64.sub` Cast.uint32_to_uint64 pn_length) pn_length in
      Some (Impl.BLong version dcid dcid_len scid scid_len spec, pn)
    end

#restart-solver

let read_header_body_long_ZeroRTT
  (sl: LL.slice (B.trivial_preorder _) (B.trivial_preorder _))
  (cid_len: U32.t { U32.v cid_len <= 20 } )
  (last: uint62_t { U64.v last + 1 < pow2 62 })
  (pn_length: packet_number_length_t)
: Tot (read_header_body_t sl cid_len last (| Long, (| (), (| ZeroRTT, (| (), (| pn_length, () |) |) |) |) |) )
= fun len ->
    let h0 = HST.get () in
    assert_norm (bitsum'_key_of_t first_byte (| Long, (| (), (| ZeroRTT, (| (), (| pn_length, () |) |) |) |) |) == (| Long, (| (), (| ZeroRTT, (| (), (| pn_length, () |) |) |) |) |) );
    if (sl.LL.len `U32.sub` len) `U32.lt` 4ul
    then None
    else begin
      LL.valid_nondep_then h0 parse_common_long (parse_payload_length_pn last pn_length) sl 1ul;
      LL.valid_nondep_then h0 parse_u32 (parse_bounded_vlbytes 0 20 `nondep_then` parse_bounded_vlbytes 0 20) sl 1ul;
      let version = LJ.read_u32 sl 1ul in
      let pos1 = LJ.jump_u32 sl 1ul in
      LL.valid_nondep_then h0 (parse_bounded_vlbytes 0 20) (parse_bounded_vlbytes 0 20) sl pos1;
      let dcid = LB.get_vlbytes_contents 0 20 sl pos1 in
      let dcid_len = LB.bounded_vlbytes_payload_length 0 20 sl pos1 in
      let pos2 = LB.jump_bounded_vlbytes 0 20 sl pos1 in
      let scid = LB.get_vlbytes_contents 0 20 sl pos2 in
      let scid_len = LB.bounded_vlbytes_payload_length 0 20 sl pos2 in
      let pos3 = LB.jump_bounded_vlbytes 0 20 sl pos2 in
      LL.valid_nondep_then h0 (parse_varint `parse_filter` payload_and_pn_length_prop pn_length) (parse_packet_number last pn_length) sl pos3;
      let payload_and_pn_length = LC.read_filter read_varint (payload_and_pn_length_prop pn_length) sl pos3 in
      let pos4 = LC.jump_filter jump_varint (payload_and_pn_length_prop pn_length) sl pos3 in
      let pn = read_packet_number last pn_length sl pos4 in
      let spec = Impl.BZeroRTT (payload_and_pn_length `U64.sub` Cast.uint32_to_uint64 pn_length) pn_length in
      Some (Impl.BLong version dcid dcid_len scid scid_len spec, pn)
    end

inline_for_extraction
noextract
let read_header_body
  (sl: LL.slice (B.trivial_preorder _) (B.trivial_preorder _))
  (cid_len: U32.t { U32.v cid_len <= 20 } )
  (last: uint62_t { U64.v last + 1 < pow2 62 })
  (tg: bitsum'_type first_byte)
: Tot (read_header_body_t sl cid_len last tg)
= fun len ->
  let h0 = HST.get () in
  match tg with
  | (| Short, (| (), (spin, (| (), (key_phase, (| pn_length, () |) ) |) ) |) |) ->
    read_header_body_short sl cid_len last spin key_phase pn_length len
  | (| Long, (| (), (| Retry, (unused, ()) |) |) |) ->
    read_header_body_long_retry sl cid_len last unused len
  | (| Long, (| (), (| Initial, (| (), (| pn_length, () |) |) |) |) |) ->
    read_header_body_long_initial sl cid_len last pn_length len
  | (| Long, (| (), (| Handshake, (| (), (| pn_length, () |) |) |) |) |) ->
    read_header_body_long_handshake sl cid_len last pn_length len
  | (| Long, (| (), (| ZeroRTT, (| (), (| pn_length, () |) |) |) |) |) ->
    read_header_body_long_ZeroRTT sl cid_len last pn_length len

#pop-options

#restart-solver

#push-options "--z3rlimit 512 --z3cliopt smt.arith.nl=false --query_stats"

let read_header
  packet packet_len cid_len last
=
  let h0 = HST.get () in
  let sl = LL.make_slice packet packet_len in
  LL.valid_facts (lp_parse_header cid_len last) h0 sl 0ul;
  assert (B.as_seq h0 packet `Seq.equal` LL.bytes_of_slice_from h0 sl 0ul);
  assert_norm (
    let k = parse_header_kind' cid_len last in
    Some? k.parser_kind_high /\
    Some?.v k.parser_kind_high <= U32.v LL.validator_max_length /\
    k.parser_kind_subkind == Some ParserStrong
  );
  let len = LL.validate_bounded_strong_prefix (validate_header cid_len last) sl 0ul in
  if len `U32.gt` LL.validator_max_length
  then None
  else begin
    let g = Ghost.hide (LL.contents (lp_parse_header cid_len last) h0 sl 0ul) in
    LL.valid_bitsum_elim
      #parse_u8_kind
      #8
      #U8.t
      #uint8
      first_byte
      #(header' cid_len last)
      (first_byte_of_header cid_len last)
      (header_body_type cid_len last)
      (header_synth cid_len last)
      parse_u8
      (parse_header_body cid_len last)
      h0
      sl
      0ul;
    let r = LJ.read_u8 sl 0ul in
    let res = destr_first_byte
      (read_header_body_t sl cid_len last)
      (fun _ cond dt df len' -> if cond then dt () len' else df () len')
      (read_header_body sl cid_len last)
      r
      len
    in
    lemma_header_parsing_post (U32.v cid_len) (U64.v last) (LL.bytes_of_slice_from h0 sl 0ul);
    match res with
    | None -> None
    | Some (res, pn) -> Some (res, pn, len)
  end

#pop-options

module HS = FStar.HyperStack
module LW = LowParse.Low.Writers.Instances

(* same as destr_first_byte here *)

inline_for_extraction
let repr_of_reserved_bits
  (x: enum_key reserved_bits)
: Tot (y: enum_repr reserved_bits { y == enum_repr_of_key reserved_bits x })
= 0uy

(* this is constant-time, no longer branches on pn_len *)
inline_for_extraction
let repr_of_packet_number_length
  (x: enum_key packet_number_length)
: Tot (y: enum_repr packet_number_length { y == enum_repr_of_key packet_number_length x })
= assert_norm (pow2 8 == 256);
//  FStar.Math.Lemmas.small_mod (U32.v (x `U32.sub` 1ul)) (pow2 8);
  Cast.uint32_to_uint8 ((x <: packet_number_length_t) `U32.sub` 1ul) <: U8.t

inline_for_extraction
noextract
let synth_rrpp
: synth_bitsum'_recip_t rrpp
= _ by (
  let open FStar.Tactics in
  T.apply (`synth_bitsum'_recip_BitSum_gen);
  T.exact (`repr_of_reserved_bits);
  let _ = T.intro () in
  T.apply (`synth_bitsum'_recip_BitSum_gen);
  T.apply (`repr_of_packet_number_length);
  let _ = T.intro () in
  T.exact_with_ref (`synth_bitsum'_recip_BitStop uint8)
)

inline_for_extraction
let repr_of_fixed_bit
  (x: enum_key fixed_bit) 
: Tot (y: enum_repr fixed_bit { y == enum_repr_of_key fixed_bit x })
= 1uy

inline_for_extraction
noextract
let synth_first_byte
: (synth_bitsum'_recip_t first_byte)
= _ by (
  let open FStar.Tactics in
  T.apply (`synth_bitsum'_recip_BitSum_intro);
  T.apply (`synth_bitsum'_recip_BitSum_cons);
  (* long *)
  T.apply (`synth_bitsum'_recip_BitSum_gen);
  T.exact (`repr_of_fixed_bit);
  let _ = T.intro () in
  T.apply (`synth_bitsum'_recip_BitSum_intro);
  T.apply (`synth_bitsum'_recip_BitSum_cons);
  (* initial *)
  T.exact_with_ref (`synth_rrpp);
  T.apply (`synth_bitsum'_recip_BitSum_cons);
  (* ZeroRTT *)
  T.exact_with_ref (`synth_rrpp);
  T.apply (`synth_bitsum'_recip_BitSum_cons);
  (* Handshake *)
  T.exact_with_ref (`synth_rrpp);
  T.apply (`synth_bitsum'_recip_BitSum_cons_nil);
  (* Retry *)
  T.apply (`synth_bitsum'_recip_BitField);
  T.exact_with_ref (`synth_bitsum'_recip_BitStop uint8);
  T.apply (`synth_bitsum'_recip_BitSum_cons_nil);
  (* short *)
  T.apply (`synth_bitsum'_recip_BitSum_gen);
  T.exact (`repr_of_fixed_bit);
  let _ = T.intro () in
  T.apply (`synth_bitsum'_recip_BitField);
  T.apply (`synth_bitsum'_recip_BitSum_gen);
  T.apply (`repr_of_reserved_bits);
  let _ = T.intro () in
  T.apply (`synth_bitsum'_recip_BitField);
  T.apply (`synth_bitsum'_recip_BitSum_gen);
  T.apply (`repr_of_packet_number_length);
  let _ = T.intro () in
  T.exact_with_ref (`synth_bitsum'_recip_BitStop uint8)
  )

#push-options "--z3rlimit 64 --max_fuel 4 --initial_fuel 4"

inline_for_extraction
noextract
let swrite_header_short
  (spin: bool)
  (phase: bool)
  (cid: B.buffer U8.t)
  (cid_len: U32.t {
    let l = U32.v cid_len in
    l == B.length cid /\
    0 <= l /\ l <= 20
  })
  (pn_len: packet_number_length_t)
  (last: last_packet_number_t)
  (pn: packet_number_t last pn_len)
  (h0: HS.mem {
    B.live h0 cid
  })
  (out: LW.slice (B.trivial_preorder _) (B.trivial_preorder _) {
    (parse_header_kind' cid_len last).parser_kind_subkind == Some ParserStrong /\
    B.loc_disjoint (B.loc_buffer cid) (LW.loc_slice_from out 0ul)
  })
: Tot (w: LW.swriter (serialize_header cid_len last) h0 (4 - U32.v pn_len) out 0ul {
    LW.swvalue w == g_header (BShort spin phase cid cid_len pn_len) h0 pn
  })
= [@inline_let]
  let tg : bitsum'_type first_byte =
    (| Short, (| (), ((if spin then 1uy else 0uy), (| (), ((if phase then 1uy else 0uy), (| pn_len, () |) ) |) ) |) |)
  in
  [@inline_let]
  let k : bitsum'_key_type first_byte =
    (| Short, (| (), (| (), (| pn_len, () |) |) |) |)
  in
  [@inline_let]
  let _ =
    assert_norm (bitsum'_key_of_t first_byte tg == k);
    assert_norm (first_byte_of_header cid_len last (g_header (BShort spin phase cid cid_len pn_len) h0 pn) == tg)
  in
  [@inline_let]
  let s : LW.swriter (serialize_header_body cid_len last k) h0 _ out 0ul =
    LW.swrite_weaken (strong_parser_kind 0 20 None) (LW.swrite_flbytes h0 out 0ul cid_len cid) `LW.swrite_nondep_then` swrite_packet_number last pn_len pn h0 out 0ul
  in
  LW.swrite_bitsum
    h0
    _
    out
    0ul
    #parse_u8_kind
    #8
    #U8.t
    first_byte
    #(header' cid_len last)
    (first_byte_of_header cid_len last)
    (header_body_type cid_len last)
    (header_synth cid_len last)
    #parse_u8
    #serialize_u8
    LJ.write_u8
    synth_first_byte
    #(parse_header_body cid_len last)
    (serialize_header_body cid_len last)
    tg
    s

#pop-options

inline_for_extraction
noextract
let swrite_common_long
  (version: U32.t)
  (dcid: B.buffer U8.t)
  (dcid_len: U32.t {
    let len = U32.v dcid_len in
    len == B.length dcid /\
    0 <= len /\ len <= 20
  })
  (scid: B.buffer U8.t)
  (scid_len: U32.t {
    let len = U32.v scid_len in
    len == B.length scid /\
    0 <= len /\ len <= 20
  })
  (h0: HS.mem {
    B.live h0 dcid /\
    B.live h0 scid
  })
  (out: LW.slice (B.trivial_preorder _) (B.trivial_preorder _) {
    B.loc_disjoint (B.loc_buffer dcid `B.loc_union` B.loc_buffer scid) (LW.loc_slice_from out 0ul)
  })
: Tot (w: LW.swriter serialize_common_long h0 0 out 0ul {
    LW.swvalue w == (version, (FB.hide (B.as_seq h0 dcid), FB.hide (B.as_seq h0 scid)))
  })
= LW.swrite_leaf LJ.write_u32 h0 out 0ul version `LW.swrite_nondep_then` (
    LW.swrite_bounded_vlbytes h0 out 0ul 0 20 dcid_len dcid `LW.swrite_nondep_then`
    LW.swrite_bounded_vlbytes h0 out 0ul 0 20 scid_len scid
  )

inline_for_extraction
let swrite_payload_length_pn
  (last: last_packet_number_t)
  (pn_length: packet_number_length_t)
  (payload_and_pn_length: parse_filter_refine (payload_and_pn_length_prop pn_length))
  (pn: packet_number_t last pn_length)
  (h0: HS.mem)
  (out: LW.slice (B.trivial_preorder _) (B.trivial_preorder _))
: Tot (w: LW.swriter (serialize_payload_length_pn last pn_length) h0 (4 - U32.v pn_length) out 0ul {
    LW.swvalue w == (payload_and_pn_length, pn)
  })
= (payload_and_pn_length_prop pn_length `LW.swrite_filter` LW.swrite_leaf (LC.leaf_writer_strong_of_serializer32 serialize_varint ()) h0 out 0ul payload_and_pn_length) `LW.swrite_nondep_then` swrite_packet_number last pn_length pn h0 out 0ul

#push-options "--z3rlimit 128 --max_fuel 4 --initial_fuel 4"

inline_for_extraction
noextract
let swrite_header_long_initial
  (short_dcid_len: short_dcid_len_t)
  (last: last_packet_number_t)
  (version: U32.t)
  (dcid: B.buffer U8.t)
  (dcid_len: U32.t {
    let len = U32.v dcid_len in
    len == B.length dcid /\
    0 <= len /\ len <= 20
  })
  (scid: B.buffer U8.t)
  (scid_len: U32.t {
    let len = U32.v scid_len in
    len == B.length scid /\
    0 <= len /\ len <= 20
  })
  (payload_length: uint62_t)
  (packet_number_length: packet_number_length_t { U64.v payload_length + U32.v packet_number_length < pow2 62 })
  (token: B.buffer U8.t)
  (token_length: U32.t {
    let v = U32.v token_length in
    v == B.length token /\
    0 <= v /\ v <= token_max_len
  })
  (pn: packet_number_t last packet_number_length)
  (h0: HS.mem {
    B.live h0 dcid /\
    B.live h0 scid /\
    B.live h0 token
  })
  (out: LW.slice (B.trivial_preorder _) (B.trivial_preorder _) {
    (parse_header_kind' short_dcid_len last).parser_kind_subkind == Some ParserStrong /\
    B.loc_disjoint ((B.loc_buffer dcid `B.loc_union` B.loc_buffer scid) `B.loc_union` B.loc_buffer token) (LW.loc_slice_from out 0ul)
  })
: Tot (w: LW.swriter (serialize_header short_dcid_len last) h0 (4 - U32.v packet_number_length) out 0ul {
    LW.swvalue w == g_header (BLong version dcid dcid_len scid scid_len (BInitial payload_length packet_number_length token token_length)) h0 pn
  })
= [@inline_let]
  let tg : bitsum'_type first_byte =
    (| Long, (| (), (| Initial, (| (), (| packet_number_length, () |) |) |) |) |)
  in
  [@inline_let]
  let k : bitsum'_key_type first_byte =
    (| Long, (| (), (| Initial, (| (), (| packet_number_length, () |) |) |) |) |)
  in
  [@inline_let]
  let _ =
    assert_norm (bitsum'_key_of_t first_byte tg == k);
    assert_norm (first_byte_of_header short_dcid_len last (g_header (BLong version dcid dcid_len scid scid_len (BInitial payload_length packet_number_length token token_length)) h0 pn) == tg)
  in
  [@inline_let]
  let s : LW.swriter (serialize_header_body short_dcid_len last k) h0 _ out 0ul =
    swrite_common_long version dcid dcid_len scid scid_len h0 out `LW.swrite_nondep_then` (
      LW.swrite_bounded_vlgenbytes h0 out 0ul 0 token_max_len (LL.leaf_writer_strong_of_serializer32 (serialize_bounded_varint 0 token_max_len) ()) token_length token `LW.swrite_nondep_then`
      swrite_payload_length_pn last packet_number_length (payload_length `U64.add` Cast.uint32_to_uint64 packet_number_length) pn h0 out
    )
  in
  LW.swrite_bitsum
    h0
    _
    out
    0ul
    #parse_u8_kind
    #8
    #U8.t
    first_byte
    #(header' short_dcid_len last)
    (first_byte_of_header short_dcid_len last)
    (header_body_type short_dcid_len last)
    (header_synth short_dcid_len last)
    #parse_u8
    #serialize_u8
    LJ.write_u8
    synth_first_byte
    #(parse_header_body short_dcid_len last)
    (serialize_header_body short_dcid_len last)
    tg
    s

inline_for_extraction
noextract
let swrite_header_long_zeroRTT
  (short_dcid_len: short_dcid_len_t)
  (last: last_packet_number_t)
  (version: U32.t)
  (dcid: B.buffer U8.t)
  (dcid_len: U32.t {
    let len = U32.v dcid_len in
    len == B.length dcid /\
    0 <= len /\ len <= 20
  })
  (scid: B.buffer U8.t)
  (scid_len: U32.t {
    let len = U32.v scid_len in
    len == B.length scid /\
    0 <= len /\ len <= 20
  })
  (payload_length: uint62_t)
  (packet_number_length: packet_number_length_t { U64.v payload_length + U32.v packet_number_length < pow2 62 })
  (pn: packet_number_t last packet_number_length)
  (h0: HS.mem {
    B.live h0 dcid /\
    B.live h0 scid
  })
  (out: LW.slice (B.trivial_preorder _) (B.trivial_preorder _) {
    (parse_header_kind' short_dcid_len last).parser_kind_subkind == Some ParserStrong /\
    B.loc_disjoint (B.loc_buffer dcid `B.loc_union` B.loc_buffer scid) (LW.loc_slice_from out 0ul)
  })
: Tot (w: LW.swriter (serialize_header short_dcid_len last) h0 (4 - U32.v packet_number_length) out 0ul {
      LW.swvalue w == g_header (BLong version dcid dcid_len scid scid_len (BZeroRTT payload_length packet_number_length)) h0 pn
  })
= [@inline_let]
  let tg : bitsum'_type first_byte =
    (| Long, (| (), (| ZeroRTT, (| (), (| packet_number_length, () |) |) |) |) |)
  in
  [@inline_let]
  let k : bitsum'_key_type first_byte =
    (| Long, (| (), (| ZeroRTT, (| (), (| packet_number_length, () |) |) |) |) |)
  in
  [@inline_let]
  let _ =
    assert_norm (bitsum'_key_of_t first_byte tg == k);
    assert_norm (first_byte_of_header short_dcid_len last (g_header (BLong version dcid dcid_len scid scid_len (BZeroRTT payload_length packet_number_length)) h0 pn) == tg)
  in
  [@inline_let]
  let s : LW.swriter (serialize_header_body short_dcid_len last k) h0 _ out 0ul =
    swrite_common_long version dcid dcid_len scid scid_len h0 out `LW.swrite_nondep_then`
    swrite_payload_length_pn last packet_number_length (payload_length `U64.add` Cast.uint32_to_uint64 packet_number_length) pn h0 out
  in
  LW.swrite_bitsum
    h0
    _
    out
    0ul
    #parse_u8_kind
    #8
    #U8.t
    first_byte
    #(header' short_dcid_len last)
    (first_byte_of_header short_dcid_len last)
    (header_body_type short_dcid_len last)
    (header_synth short_dcid_len last)
    #parse_u8
    #serialize_u8
    LJ.write_u8
    synth_first_byte
    #(parse_header_body short_dcid_len last)
    (serialize_header_body short_dcid_len last)
    tg
    s

inline_for_extraction
noextract
let swrite_header_long_handshake
  (short_dcid_len: short_dcid_len_t)
  (last: last_packet_number_t)
  (version: U32.t)
  (dcid: B.buffer U8.t)
  (dcid_len: U32.t {
    let len = U32.v dcid_len in
    len == B.length dcid /\
    0 <= len /\ len <= 20
  })
  (scid: B.buffer U8.t)
  (scid_len: U32.t {
    let len = U32.v scid_len in
    len == B.length scid /\
    0 <= len /\ len <= 20
  })
  (payload_length: uint62_t)
  (packet_number_length: packet_number_length_t { U64.v payload_length + U32.v packet_number_length < pow2 62 })
  (pn: packet_number_t last packet_number_length)
  (h0: HS.mem {
    B.live h0 dcid /\
    B.live h0 scid
  })
  (out: LW.slice (B.trivial_preorder _) (B.trivial_preorder _) {
    (parse_header_kind' short_dcid_len last).parser_kind_subkind == Some ParserStrong /\
    B.loc_disjoint (B.loc_buffer dcid `B.loc_union` B.loc_buffer scid) (LW.loc_slice_from out 0ul)
  })
: Tot (w: LW.swriter (serialize_header short_dcid_len last) h0 (4 - U32.v packet_number_length) out 0ul {
      LW.swvalue w == g_header (BLong version dcid dcid_len scid scid_len (BHandshake payload_length packet_number_length)) h0 pn
  })
= [@inline_let]
  let tg : bitsum'_type first_byte =
    (| Long, (| (), (| Handshake, (| (), (| packet_number_length, () |) |) |) |) |)
  in
  [@inline_let]
  let k : bitsum'_key_type first_byte =
    (| Long, (| (), (| Handshake, (| (), (| packet_number_length, () |) |) |) |) |)
  in
  [@inline_let]
  let _ =
    assert_norm (bitsum'_key_of_t first_byte tg == k);
    assert_norm (first_byte_of_header short_dcid_len last (g_header (BLong version dcid dcid_len scid scid_len (BHandshake payload_length packet_number_length)) h0 pn) == tg)
  in
  [@inline_let]
  let s : LW.swriter (serialize_header_body short_dcid_len last k) h0 _ out 0ul =
    swrite_common_long version dcid dcid_len scid scid_len h0 out `LW.swrite_nondep_then`
    swrite_payload_length_pn last packet_number_length (payload_length `U64.add` Cast.uint32_to_uint64 packet_number_length) pn h0 out
  in
  LW.swrite_bitsum
    h0
    _
    out
    0ul
    #parse_u8_kind
    #8
    #U8.t
    first_byte
    #(header' short_dcid_len last)
    (first_byte_of_header short_dcid_len last)
    (header_body_type short_dcid_len last)
    (header_synth short_dcid_len last)
    #parse_u8
    #serialize_u8
    LJ.write_u8
    synth_first_byte
    #(parse_header_body short_dcid_len last)
    (serialize_header_body short_dcid_len last)
    tg
    s

inline_for_extraction
noextract
let swrite_header_long_retry
  (short_dcid_len: short_dcid_len_t)
  (last: last_packet_number_t)
  (version: U32.t)
  (dcid: B.buffer U8.t)
  (dcid_len: U32.t {
    let len = U32.v dcid_len in
    len == B.length dcid /\
    0 <= len /\ len <= 20
  })
  (scid: B.buffer U8.t)
  (scid_len: U32.t {
    let len = U32.v scid_len in
    len == B.length scid /\
    0 <= len /\ len <= 20
  })
  (unused: bitfield 4)
  (odcid: B.buffer U8.t)
  (odcid_len: U32.t {
    let len = U32.v odcid_len in
    len == B.length odcid /\
    0 <= len /\ len <= 20
  })
  (pn: uint62_t)
  (h0: HS.mem {
    B.live h0 dcid /\
    B.live h0 scid /\
    B.live h0 odcid
  })
  (out: LW.slice (B.trivial_preorder _) (B.trivial_preorder _) {
    (parse_header_kind' short_dcid_len last).parser_kind_subkind == Some ParserStrong /\
    B.loc_disjoint ((B.loc_buffer dcid `B.loc_union` B.loc_buffer scid) `B.loc_union` B.loc_buffer odcid) (LW.loc_slice_from out 0ul)
  })
: Tot (w: LW.swriter (serialize_header short_dcid_len last) h0 0 out 0ul {
      LW.swvalue w == g_header (BLong version dcid dcid_len scid scid_len (BRetry unused odcid odcid_len)) h0 pn
  })
= [@inline_let]
  let tg : bitsum'_type first_byte =
    (| Long, (| (), (| Retry, ( unused, () ) |) |) |)
  in
  [@inline_let]
  let k : bitsum'_key_type first_byte =
    (| Long, (| (), (| Retry, () |) |) |)
  in
  [@inline_let]
  let _ =
    assert_norm (bitsum'_key_of_t first_byte tg == k);
    assert_norm (first_byte_of_header short_dcid_len last (g_header (BLong version dcid dcid_len scid scid_len (BRetry unused odcid odcid_len)) h0 pn) == tg)
  in
  [@inline_let]
  let s : LW.swriter (serialize_header_body short_dcid_len last k) h0 0 out 0ul =
    swrite_common_long version dcid dcid_len scid scid_len h0 out `LW.swrite_nondep_then`
    LW.swrite_bounded_vlbytes h0 out 0ul 0 20 odcid_len odcid
  in
  LW.swrite_bitsum
    h0
    0
    out
    0ul
    #parse_u8_kind
    #8
    #U8.t
    first_byte
    #(header' short_dcid_len last)
    (first_byte_of_header short_dcid_len last)
    (header_body_type short_dcid_len last)
    (header_synth short_dcid_len last)
    #parse_u8
    #serialize_u8
    LJ.write_u8
    synth_first_byte
    #(parse_header_body short_dcid_len last)
    (serialize_header_body short_dcid_len last)
    tg
    s

#pop-options

#restart-solver

#push-options "--z3rlimit 32"

let write_header'
  (short_dcid_len: short_dcid_len_t)
  (last: last_packet_number_t)
  (h: Impl.header)
  (pn: uint62_t)
  (out: B.buffer U8.t)
  (out_len: U32.t { U32.v out_len <= B.length out })
: HST.Stack U32.t
  (requires (fun h0 ->
    (BShort? h ==> BShort?.cid_len h == short_dcid_len) /\
    ((~ (Impl.is_retry h)) ==> in_window (U32.v (Impl.pn_length h) - 1) (U64.v last) (U64.v pn)) /\
    header_live h h0 /\
    B.live h0 out /\
    B.loc_disjoint (header_footprint h) (B.loc_buffer out) /\
    S.length (serialize (serialize_header short_dcid_len last) (g_header h h0 pn)) + (if Impl.is_retry h then 0 else 4) <= U32.v out_len
  ))
  (ensures (fun h0 len h1 ->
    let gh = g_header h h0 pn in
    let s = serialize (serialize_header short_dcid_len last) gh in
    B.modifies (B.loc_buffer out) h0 h1 /\
    U32.v len <= U32.v out_len /\
    S.slice (B.as_seq h1 out) 0 (U32.v len) == s 
  ))
= let h0 = HST.get () in
  assert_norm ((parse_header_kind' short_dcid_len last).parser_kind_subkind == Some ParserStrong);
  let sl = LW.make_slice out out_len in
  LW.serialized_length_eq (serialize_header short_dcid_len last) (g_header h h0 pn);
  let len = match h with
  | BShort spin phase cid cid_len pn_len ->
    LW.swrite (swrite_header_short spin phase cid cid_len pn_len last pn h0 sl) 0ul
  | BLong version dcid dcil scid scil spec ->
    begin match spec with
    | BInitial payload_length packet_number_length token token_length ->
      LW.swrite (swrite_header_long_initial short_dcid_len last version dcid dcil scid scil payload_length packet_number_length token token_length pn h0 sl) 0ul
    | BZeroRTT payload_length packet_number_length ->
      LW.swrite (swrite_header_long_zeroRTT short_dcid_len last version dcid dcil scid scil payload_length packet_number_length pn h0 sl) 0ul
    | BHandshake payload_length packet_number_length ->
      LW.swrite (swrite_header_long_handshake short_dcid_len last version dcid dcil scid scil payload_length packet_number_length pn h0 sl) 0ul
    | BRetry unused odcid odcil ->
      LW.swrite (swrite_header_long_retry short_dcid_len last version dcid dcil scid scil unused odcid odcil pn h0 sl) 0ul
    end  
  in
//  LW.swrite (swrite_header short_dcid_len last h pn h0 sl) 0ul in
  let h1 = HST.get () in
  LL.valid_pos_valid_exact  (lp_parse_header short_dcid_len last) h1 sl 0ul len;
  LL.valid_exact_serialize (serialize_header short_dcid_len last) h1 sl 0ul len;
  len

#restart-solver

let header_len_correct
  h m pn
= let hs = g_header h m pn in
  let f () : Lemma (U32.v (Impl.header_len h) == Spec.header_len' hs) =
    match h with
    | BLong version dcid dcil scid scil spec ->
      begin match spec with
      | BInitial payload_length packet_number_length token token_length ->
        bounded_varint_len_correct 0 token_max_len token_length;
        varint_len_correct (payload_length `U64.add` Cast.uint32_to_uint64 packet_number_length)
      | BZeroRTT payload_length packet_number_length ->
        varint_len_correct (payload_length `U64.add` Cast.uint32_to_uint64 packet_number_length)
      | BHandshake payload_length packet_number_length ->
        varint_len_correct (payload_length `U64.add` Cast.uint32_to_uint64 packet_number_length)
      | BRetry unused odcid odcil -> ()
    end
    | _ -> ()
  in
  f ();
  header_len'_correct hs

#restart-solver

let write_header
  dst x pn
= let short_dcid_len = Impl.dcid_len x in
  let last : last_packet_number_t = if Impl.is_retry x then 0uL else if pn = 0uL then 0uL else pn `U64.sub` 1uL in
  let dst_len = Impl.header_len x `U32.add` (if Impl.is_retry x then 0ul else 4ul) in
  let h0 = HST.get () in
  parse_header_prop_intro (g_header x h0 pn);
  header_len_correct x h0 pn;
  let len' = write_header' short_dcid_len last x pn dst dst_len in
  let h1 = HST.get () in
  ()

#pop-options

#push-options "--z3rlimit 32"

let putative_pn_offset
  cid_len b len
=
  let sl = LowParse.Slice.make_slice b len in
  let h0 = HST.get () in
    let _ = LL.valid_facts parse_u8 h0 sl 0ul in
    let pos1 = LL.validate_bounded_strong_prefix (LJ.validate_u8 ()) sl 0ul in
    if pos1 `U32.gt` LL.validator_max_length
    then 0ul
    else
      let _ =
        parser_kind_prop_equiv parse_u8_kind parse_u8;
        assert (pos1 == 1ul)
      in
      let hd = LJ.read_u8 sl 0ul in
      if uint8.get_bitfield hd 7 8 = 0uy
      then begin
        if not (cid_len `U32.lte` 20ul)
        then 0ul
        else
        let _ = LL.valid_facts (parse_flbytes (U32.v cid_len)) h0 sl pos1 in
        let pos2 = LL.validate_bounded_strong_prefix (LB.validate_flbytes (U32.v cid_len) cid_len) sl pos1 in
        if pos2 `U32.gt` LL.validator_max_length
        then 0ul
        else pos2
      end else
        let packet_type = uint8.get_bitfield hd 4 6 in
        if packet_type = 3uy
        then 0ul
        else
          let _ = LL.valid_facts parse_common_long h0 sl pos1 in
          let pos2 = LL.validate_bounded_strong_prefix validate_common_long sl pos1 in
          if pos2 `U32.gt` LL.validator_max_length
          then 0ul
          else
            let pos3 =
              if packet_type = 0uy
              then
                let _ = LL.valid_facts (parse_bounded_vlgenbytes 0 token_max_len (parse_bounded_varint 0 token_max_len)) h0 sl pos2 in
                let pos3 = LL.validate_bounded_strong_prefix (LB.validate_bounded_vlgenbytes 0 0ul token_max_len (U32.uint_to_t token_max_len) (validate_bounded_varint 0ul (U32.uint_to_t token_max_len)) (read_bounded_varint 0 token_max_len)) sl pos2 in
                if pos3 `U32.gt` LL.validator_max_length
                then 0ul
                else pos3
              else
                pos2
            in
            if pos3 = 0ul
            then 0ul
            else
              let _ = LL.valid_facts parse_varint h0 sl pos3 in
              let pos4 = LL.validate_bounded_strong_prefix validate_varint sl pos3 in
              if pos4 `U32.gt` LL.validator_max_length
              then 0ul
              else pos4

#pop-options

let pn_offset'
  (h: Impl.header)
: Tot U32.t
= match h with
  | BShort spin phase cid cid_len packet_number_length ->
    1ul `U32.add` cid_len
  | BLong version dcid dcil scid scil spec ->
    7ul `U32.add` dcil `U32.add` scil `U32.add`
    begin match spec with
    | BInitial payload_length packet_number_length token token_length ->
      varint_len (Cast.uint32_to_uint64 token_length) `U32.add` token_length `U32.add` varint_len (payload_length `U64.add` Cast.uint32_to_uint64 packet_number_length)
    | BZeroRTT payload_length packet_number_length ->
      varint_len (payload_length `U64.add` Cast.uint32_to_uint64 packet_number_length)
    | BHandshake payload_length packet_number_length ->
      varint_len (payload_length `U64.add` Cast.uint32_to_uint64 packet_number_length)
    | BRetry unused odcid odcil ->
      1ul `U32.add` odcil
    end

#push-options "--z3rlimit 64 --max_ifuel 2 --initial_ifuel 2"

#restart-solver

let pn_offset
  h pn
= let h0 = HST.get () in
  assert (Impl.is_retry h == Spec.is_retry (g_header h h0 (Ghost.reveal pn)));
  header_len_correct h h0 (Ghost.reveal pn);
  assert (Impl.pn_length h == Spec.pn_length (g_header h h0 (Ghost.reveal pn)));
  assert (U32.v (pn_offset' h) == U32.v (Impl.header_len h) - U32.v (Impl.pn_length h));
  pn_offset' h

#pop-options

