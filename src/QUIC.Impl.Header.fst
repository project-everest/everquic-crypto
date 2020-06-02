module QUIC.Impl.Header
friend QUIC.Spec.Header

open QUIC.Impl.Header.Base

module Parse = QUIC.Spec.Header.Parse
module ParseImpl = QUIC.Impl.Header.Parse
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

module SCipher = Spec.Agile.Cipher
module SAEAD = Spec.Agile.AEAD

(* There are a few places where EverCrypt needs public data whereas it
could/should be secret. Thus, we may need some declassification
locally using Lib.RawIntTypes, but we definitely don't want to make
secret integers globally transparent using friend *)

module ADMITDeclassify = Lib.RawIntTypes

let block_len (a: SCipher.cipher_alg):
  x:U32.t { U32.v x = SCipher.block_length a }
=
  let open SCipher in
  match a with | CHACHA20 -> 64ul | _ -> 16ul

#push-options "--z3rlimit 256"
inline_for_extraction
let block_of_sample (a: SCipher.cipher_alg)
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
      SCipher.(a == AES128 \/ a == AES256 \/ a == CHACHA20) /\
      B.length k = SCipher.key_length a /\
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
  let zeroes' = B.alloca (Secret.to_u8 0uy) 64ul in
  let zeroes = B.sub zeroes' 0ul (block_len a) in
  let dst_block' = B.alloca (Secret.to_u8 0uy) 64ul in
  let dst_block = B.sub dst_block' 0ul (block_len a) in
  begin match a with
  | SCipher.CHACHA20 ->
      let ctr = SecretBuffer.load32_le (B.sub sample 0ul 4ul) in
      let iv = B.sub sample 4ul 12ul in
      (**) let h1 = HST.get () in
      (* EverCrypt currently does not support secret counters,
         so we need to declassify the counter value here and only here. *)
      CTR.init (G.hide a) s k iv 12ul (ADMITDeclassify.u32_to_UInt32 ctr);
      CTR.update_block (G.hide a) s dst_block zeroes;
      (**) let h2 = HST.get () in
      (**) Lemmas.seq_map2_xor0 (B.as_seq h1 dst_block)
      (**)   (SCipher.ctr_block a (B.as_seq h0 k) (B.as_seq h1 iv) (Secret.v ctr));
      (**) assert (B.as_seq h2 dst_block `Seq.equal`
      (**)   SCipher.ctr_block a (B.as_seq h0 k) (B.as_seq h1 iv) (Secret.v ctr));
      let dst_slice = B.sub dst_block 0ul 16ul in
      (**) assert (B.as_seq h2 dst_slice `Seq.equal` Seq.slice (
      (**)   SCipher.ctr_block a (B.as_seq h0 k) (B.as_seq h1 iv) (Secret.v ctr)
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
      (**)   (SCipher.ctr_block a (B.as_seq h0 k) (B.as_seq h1 iv) (Secret.v ctr));
      (**) assert (B.as_seq h2 dst_block `Seq.equal`
      (**)   SCipher.ctr_block a (B.as_seq h0 k) (B.as_seq h1 iv) (Secret.v ctr));
      let dst_slice = B.sub dst_block 0ul 16ul in
      (**) assert (B.as_seq h2 dst_slice `Seq.equal` Seq.slice (
      (**)   SCipher.ctr_block a (B.as_seq h0 k) (B.as_seq h1 iv) (Secret.v ctr)
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
  (hpk: SCipher.key (SAEAD.cipher_alg_of_supported_alg a))
  (h: Spec.header)
  (c: cbytes' (Spec.is_retry h))
: GTot packet
= 
  assert_norm(max_cipher_length < pow2 62);
  let r = Parse.format_header h `Seq.append` c in
  if Spec.is_retry h
  then
    r
  else
    let pn_offset = Parse.pn_offset h in
    let pn_len = Secret.v (Spec.pn_length h) - 1 in
    let sample = Seq.seq_hide (Seq.slice c (3-pn_len) (19-pn_len)) in
    let mask = Seq.seq_reveal (Spec.block_of_sample (SAEAD.cipher_alg_of_supported_alg a) hpk sample) in
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
  (hpk: SCipher.key (SAEAD.cipher_alg_of_supported_alg a))
  (h: Spec.header)
  (c: cbytes' (Spec.is_retry h))
: Lemma
  (header_encrypt_ct a hpk h c `Seq.equal` Spec.header_encrypt a hpk h c)
=
  assert_norm(max_cipher_length < pow2 62);
  let r = Parse.format_header h `Seq.append` c in
  if Spec.is_retry h
  then ()
  else begin
    let pn_offset = Parse.pn_offset h in
    let pn_len = Secret.v (Parse.pn_length h) - 1 in
    let sample = Seq.seq_hide (Seq.slice c (3-pn_len) (19-pn_len)) in
    let mask = Seq.seq_reveal (Spec.block_of_sample (SAEAD.cipher_alg_of_supported_alg a) hpk sample) in
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

#push-options "--z3rlimit 16"

let header_encrypt_ct_secret_preserving_not_retry_spec
  (a:ea)
  (hpk: SCipher.key (SAEAD.cipher_alg_of_supported_alg a))
  (h: Spec.header { ~ (Spec.is_retry h) })
  (r: Seq.seq Secret.uint8 {
    Seq.length r >= Parse.pn_offset h + 20
  })
: GTot (Seq.seq Secret.uint8)
= 
  let pn_offset = Parse.pn_offset h in
  let pn_len = Secret.v (Spec.pn_length h) - 1 in
  let sample = (Seq.slice r (pn_offset + 4) (pn_offset + 20)) in
  let mask = (Spec.block_of_sample (SAEAD.cipher_alg_of_supported_alg a) hpk sample) in
  let pnmask = Lemmas.secret_and_inplace (Seq.slice mask 1 5) (Seq.seq_hide (pn_sizemask_ct pn_len)) 0 in
  let f = Seq.index r 0 in
  let protected_bits = if Spec.MShort? h then 5ul else 4ul in
  let f' = Secret.set_bitfield f 0ul protected_bits (Secret.get_bitfield (f `Secret.logxor` Seq.index mask 0) 0ul protected_bits) in
  let r = Lemmas.secret_xor_inplace r pnmask pn_offset in
  let r = Seq.cons f' (Seq.slice r 1 (Seq.length r)) in
  r

#pop-options

#push-options "--z3rlimit 256 --query_stats --z3cliopt smt.arith.nl=false --fuel 2 --ifuel 2"

#restart-solver

let header_encrypt_ct_secret_preserving_not_retry_spec_correct
  (a:ea)
  (hpk: SCipher.key (SAEAD.cipher_alg_of_supported_alg a))
  (h: Spec.header)
  (c: cbytes)
: Lemma
  (requires (
    (~ (Spec.is_retry h))
  ))
  (ensures (
    let r = Parse.format_header h `Seq.append` c in
    Seq.length r >= Parse.pn_offset h + 20 /\
    Spec.header_encrypt a hpk h c == Seq.seq_reveal (header_encrypt_ct_secret_preserving_not_retry_spec a hpk h (Seq.seq_hide r))
  ))
= header_encrypt_ct_correct a hpk h c;
  let fmt = Parse.format_header h in
  let len = Seq.length fmt in
  let pr = fmt `Seq.append` c in
  assert (Seq.length pr >= Parse.pn_offset h + 20);
  let pn_len = Secret.v (Spec.pn_length h) - 1 in
  let psample = Seq.slice c (3 - pn_len) (19 - pn_len) in
  assert (c `Seq.equal` Seq.slice pr len (Seq.length pr));
  let pn_off = Parse.pn_offset h in
  assert (pn_off + pn_len + 1 == len);
  assert (c == Seq.slice pr (pn_off + pn_len + 1) (Seq.length pr));
  Seq.slice_slice pr (pn_off + pn_len + 1) (Seq.length pr) (3 - pn_len) (19 - pn_len);
  assert (psample == Seq.slice pr (pn_off + 4) (pn_off + 20));
  let r = Seq.seq_hide #Secret.U8 pr in
  let sample = Seq.slice r (pn_off + 4) (pn_off + 20) in
  assert (sample == Seq.seq_hide #Secret.U8 psample);
  let mask = Spec.block_of_sample (SAEAD.cipher_alg_of_supported_alg a) hpk sample in
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

#push-options "--z3rlimit 32"

#restart-solver

[@"opaque_to_smt"]
let pn_sizemask_ct_num
  (pn_len: PN.packet_number_length_t)
: Tot (x: Secret.uint32 { pn_sizemask_ct (Secret.v pn_len - 1) == FStar.Endianness.n_to_be 4 (Secret.v x) })
=
  FStar.Math.Lemmas.pow2_lt_compat 32 (24 - (8 `op_Multiply` (Secret.v pn_len - 1)));
  [@inline_let]
  let n0 = norm [delta; zeta; iota; primops] (pow2 32 - pow2 24) in
  [@inline_let]
  let n1 = norm [delta; zeta; iota; primops] (pow2 32 - pow2 16) in
  [@inline_let]
  let n2 = norm [delta; zeta; iota; primops] (pow2 32 - pow2 8) in
  [@inline_let]
  let n3 = norm [delta; zeta; iota; primops] (pow2 32 - pow2 0) in
  let pn_len_1 = pn_len `Secret.sub` Secret.to_u32 1ul in
  ((pn_len_1 `Secret.secrets_are_equal_32_2` Secret.to_u32 0ul) `Secret.mul` Secret.to_u32 (U32.uint_to_t n0)) `Secret.add`
  ((pn_len_1 `Secret.secrets_are_equal_32_2` Secret.to_u32 1ul) `Secret.mul` Secret.to_u32 (U32.uint_to_t n1)) `Secret.add`
  ((pn_len_1 `Secret.secrets_are_equal_32_2` Secret.to_u32 2ul) `Secret.mul` Secret.to_u32 (U32.uint_to_t n2)) `Secret.add`
  ((pn_len_1 `Secret.secrets_are_equal_32_2` Secret.to_u32 3ul) `Secret.mul` Secret.to_u32 (U32.uint_to_t n3))

#pop-options

inline_for_extraction
noextract
let pn_sizemask (dst: B.buffer Secret.uint8) (pn_len: PN.packet_number_length_t): HST.Stack unit
  (requires fun h0 ->
    B.live h0 dst /\ B.length dst == 4)
  (ensures fun h0 _ h1 ->
    B.as_seq h1 dst `Seq.equal` Seq.seq_hide (pn_sizemask_ct (Secret.v pn_len - 1)) /\
    B.(modifies (loc_buffer dst) h0 h1))
= let x = pn_sizemask_ct_num pn_len in
  SecretBuffer.store32_be dst x

#push-options "--z3rlimit 512 --query_stats --z3cliopt smt.arith.nl=false --fuel 2 --ifuel 1"

#restart-solver

let header_encrypt_ct_secret_preserving_not_retry
  (a: ea)
  (s: CTR.state (SAEAD.cipher_alg_of_supported_alg a))
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
    B.length k == SCipher.key_length (SAEAD.cipher_alg_of_supported_alg a) /\
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
  block_of_sample (SAEAD.cipher_alg_of_supported_alg a) mask s k sample;
  let m2 = HST.get () in
  let gmask = Ghost.hide (Spec.block_of_sample (SAEAD.cipher_alg_of_supported_alg a) (B.as_seq m0 k) gsample) in
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
  let f_logxor = f_ `Secret.logxor` mask_0 in
  let f_get_bf = Secret.get_bitfield f_logxor 0ul protected_bits in
  let f' = Secret.set_bitfield f_ 0ul protected_bits f_get_bf in
  Lemmas.op_inplace dst pnmask 4ul pn_offset (Secret.logxor #Secret.U8 #Secret.SEC);
  let m5 = HST.get () in
  let gr1 = Ghost.hide (Lemmas.secret_xor_inplace (B.as_seq m0 dst) gpnmask (U32.v pn_offset)) in
  assert (B.as_seq m5 dst == Ghost.reveal gr1);
  B.upd dst 0ul f' ;
  HST.pop_frame ();
  let m6 = HST.get () in
  assert (B.as_seq m6 dst `Seq.equal` (f' `Seq.cons` Seq.slice (Ghost.reveal gr1) 1 (B.length dst)))

#restart-solver

let header_encrypt
  a s k dst h is_short is_retry public_len pn_len
= if is_retry
  then ()
  else begin
    let m = HST.get () in
    let hpk = Ghost.hide (B.as_seq m k) in
    let fmt = Ghost.hide (Parse.format_header (G.reveal h)) in
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


(* A constant-time specification of header_decrypt_aux which does not test or truncate on pn_len *)

let header_decrypt_aux_ct
  (a:ea)
  (hpk: SCipher.key (SAEAD.cipher_alg_of_supported_alg a))
  (cid_len: nat { cid_len <= 20 })
  (packet: packet)
: GTot (option Spec.header_decrypt_aux_t)
= let open FStar.Math.Lemmas in
  if Seq.length packet = 0
  then None
  else
    let f = Seq.index packet 0 in
    let is_short = (BF.get_bitfield (U8.v f) 7 8 = 0) in
    let is_retry = not is_short && BF.get_bitfield (U8.v f) 4 6 = 3 in
    if is_retry
    then
      Some ({
        Spec.is_short = is_short;
        Spec.is_retry = is_retry;
        Spec.packet = packet;
        Spec.pn_offset = ();
        Spec.pn_len = ();
      })
    else
      match Parse.putative_pn_offset cid_len packet with
      | None -> None
      | Some pn_offset ->
        let sample_offset = pn_offset + 4 in
        if sample_offset + 16 > Seq.length packet
        then None
        else begin
          let sample = Seq.slice packet sample_offset (sample_offset+16) in
          let mask = Seq.seq_reveal (Spec.block_of_sample (SAEAD.cipher_alg_of_supported_alg a) hpk (Seq.seq_hide sample)) in
          (* mask the least significant bits of the first byte *)
          let protected_bits = if is_short then 5 else 4 in
          let f' = BF.set_bitfield (U8.v f) 0 protected_bits (BF.get_bitfield (U8.v f `FStar.UInt.logxor` U8.v (Seq.index mask 0)) 0 protected_bits) in
          let packet' = Seq.cons (U8.uint_to_t f') (Seq.slice packet 1 (Seq.length packet)) in
          (* now the packet number length is available, so mask the packet number *)
          let pn_len = BF.get_bitfield f' 0 2 in
          let pnmask = Lemmas.and_inplace (Seq.slice mask 1 5) (pn_sizemask_ct pn_len) 0 in
          let packet'' = Lemmas.xor_inplace packet' pnmask pn_offset in
          Some ({
            Spec.is_short = is_short;
            Spec.is_retry = is_retry;
            Spec.packet = packet'';
            Spec.pn_offset = pn_offset;
            Spec.pn_len = pn_len;
          })
        end

#push-options "--z3rlimit 1024 --z3cliopt smt.arith.nl=false --query_stats"

#restart-solver

let header_decrypt_aux_ct_correct
  (a:ea)
  (hpk: SCipher.key (SAEAD.cipher_alg_of_supported_alg a))
  (cid_len: nat { cid_len <= 20 })
  (packet: packet)
: Lemma
  (header_decrypt_aux_ct a hpk cid_len packet == Spec.header_decrypt_aux a hpk cid_len packet)
= 
  let open FStar.Math.Lemmas in
  if Seq.length packet = 0
  then ()
  else
    let f = Seq.index packet 0 in
    let is_short = (BF.get_bitfield (U8.v f) 7 8 = 0) in
    let is_retry = not is_short && BF.get_bitfield (U8.v f) 4 6 = 3 in
    if is_retry
    then ()
    else
      match Parse.putative_pn_offset cid_len packet with
      | None -> ()
      | Some pn_offset ->
        let sample_offset = pn_offset + 4 in
        if sample_offset + 16 > Seq.length packet
        then ()
        else begin
          let sample = Seq.slice packet sample_offset (sample_offset+16) in
          let mask = Seq.seq_reveal #Secret.U8 (Spec.block_of_sample (SAEAD.cipher_alg_of_supported_alg a) hpk (Seq.seq_hide #Secret.U8 sample)) in
          (* mask the least significant bits of the first byte *)
          let protected_bits = if is_short then 5 else 4 in
          let f' = BF.set_bitfield (U8.v f) 0 protected_bits (BF.get_bitfield (U8.v f `FStar.UInt.logxor` U8.v (Seq.index mask 0)) 0 protected_bits) in
          let packet' = Seq.cons (U8.uint_to_t f') (Seq.slice packet 1 (Seq.length packet)) in
          (* now the packet number length is available, so mask the packet number *)
          let pn_len = BF.get_bitfield f' 0 2 in
          let pnmask_ct = Lemmas.and_inplace (Seq.slice mask 1 5) (pn_sizemask_ct pn_len) 0 in
          let pnmask_naive = Lemmas.and_inplace (Seq.slice mask 1 (pn_len + 2)) (Spec.pn_sizemask pn_len) 0 in
          Lemmas.pointwise_op_split U8.logand (Seq.slice mask 1 5) (pn_sizemask_ct pn_len) 0 (pn_len + 1);
          assert (pnmask_naive `Seq.equal` Seq.slice pnmask_ct 0 (pn_len + 1));
          let r = packet' in
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

#restart-solver

let header_decrypt_aux_ct_secret_preserving_not_retry_spec
  (a:ea)
  (hpk: SCipher.key (SAEAD.cipher_alg_of_supported_alg a))
  (cid_len: nat { cid_len <= 20 })
  (packet: Seq.seq Secret.uint8 { 
    let l = Seq.length packet in
    0 < l /\ l < pow2 32
  })
  (is_short: bool {
    let i = Secret.v #Secret.U8 (Seq.index packet 0) in
    (is_short == true <==> BF.get_bitfield #8 i 7 8 == 0) /\
    (~ (not is_short && BF.get_bitfield #8 i 4 6 = 3))
  })
  (pn_offset: nat {
    match Parse.putative_pn_offset cid_len (Seq.seq_reveal packet) with
    | None -> False
    | Some pn_offset' ->
      pn_offset == pn_offset' /\
      pn_offset + 20 <= Seq.length packet
  })
  : GTot (Spec.header_decrypt_aux_t)
=
  let f = Seq.index packet 0 in
  let sample_offset = pn_offset + 4 in
  let sample = Seq.slice packet sample_offset (sample_offset+16) in
  let mask = Spec.block_of_sample (SAEAD.cipher_alg_of_supported_alg a) hpk sample in
  (* mask the least significant bits of the first byte *)
  let protected_bits = if is_short then 5ul else 4ul in
  let f' = Secret.set_bitfield f 0ul protected_bits (Secret.get_bitfield (f `Secret.logxor` (Seq.index mask 0)) 0ul protected_bits) in
  let packet' = Seq.cons f' (Seq.slice packet 1 (Seq.length packet)) in
  (* now the packet number length is available, so mask the packet number *)
  let pn_len = Secret.get_bitfield f' 0ul 2ul in
  let pnmask = Lemmas.secret_and_inplace (Seq.slice mask 1 5) (Seq.seq_hide #Secret.U8 (pn_sizemask_ct (Secret.v pn_len))) 0 in
  let packet'' = Lemmas.secret_xor_inplace packet' pnmask pn_offset in
  {
    Spec.is_short = is_short;
    Spec.is_retry = false;
    Spec.packet = Seq.seq_reveal #Secret.U8 packet'';
    Spec.pn_offset = pn_offset;
    Spec.pn_len = Secret.v pn_len;
  }

#push-options "--z3rlimit 32"

let header_decrypt_aux_ct_secret_preserving_not_retry_spec_correct
  (a:ea)
  (hpk: SCipher.key (SAEAD.cipher_alg_of_supported_alg a))
  (cid_len: nat { cid_len <= 20 })
  (packet: Seq.seq Secret.uint8 { 
    let l = Seq.length packet in
    0 < l /\ l < pow2 32
  })
  (is_short: bool {
    let i = Secret.v #Secret.U8 (Seq.index packet 0) in
    (is_short == true <==> BF.get_bitfield #8 i 7 8 == 0) /\
    (~ (not is_short && BF.get_bitfield #8 i 4 6 = 3))
  })
  (pn_offset: nat {
    match Parse.putative_pn_offset cid_len (Seq.seq_reveal packet) with
    | None -> False
    | Some pn_offset' ->
      pn_offset == pn_offset' /\
      pn_offset + 20 <= Seq.length packet
  })
: Lemma
  (header_decrypt_aux_ct a hpk cid_len (Seq.seq_reveal packet) == Some (header_decrypt_aux_ct_secret_preserving_not_retry_spec a hpk cid_len packet is_short pn_offset))
= assert (Some? (header_decrypt_aux_ct a hpk cid_len (Seq.seq_reveal packet)));
  let ppacket = Seq.seq_reveal packet in
  let f = Seq.index packet 0 in
  let pf = Seq.index ppacket 0 in
  assert (pf == Secret.reveal f);
  let is_short = (BF.get_bitfield #8 (Secret.v f) 7 8 = 0) in
  let Some pn_offset = Parse.putative_pn_offset cid_len ppacket in
  let sample_offset = pn_offset + 4 in
  let psample = Seq.slice ppacket sample_offset (sample_offset + 16) in
  let sample = Seq.slice packet sample_offset (sample_offset + 16) in
  assert (psample == Seq.seq_reveal sample);
  let mask = Spec.block_of_sample (SAEAD.cipher_alg_of_supported_alg a) hpk sample in
  let pmask = Seq.seq_reveal mask in
  let protected_bits = if is_short then 5 else 4 in
  let pf' = U8.uint_to_t (BF.set_bitfield (U8.v pf) 0 protected_bits (BF.get_bitfield (U8.v pf `FStar.UInt.logxor` U8.v (Seq.index pmask 0)) 0 protected_bits)) in
  let f' = Secret.set_bitfield f 0ul (U32.uint_to_t protected_bits) (Secret.get_bitfield (f `Secret.logxor` Seq.index mask 0) 0ul (U32.uint_to_t protected_bits)) in
  assert (pf' == Secret.reveal f');
  let packet' = Seq.cons f' (Seq.slice packet 1 (Seq.length packet)) in
  let ppacket' = Seq.cons pf' (Seq.slice ppacket 1 (Seq.length ppacket)) in
  assert (ppacket' `Seq.equal` Seq.seq_reveal packet');
  let ppn_len = BF.get_bitfield (U8.v pf') 0 2 in
  let pn_len = Secret.get_bitfield f' 0ul 2ul in
  assert (Secret.v pn_len == ppn_len);
  let ppnmask_ct = Lemmas.and_inplace (Seq.slice pmask 1 5) (pn_sizemask_ct ppn_len) 0 in
  let pnmask_ct = Lemmas.secret_and_inplace (Seq.slice mask 1 5) (Seq.seq_hide #Secret.U8 (pn_sizemask_ct ppn_len)) 0 in
  Lemmas.secret_and_inplace_eq  (Seq.slice mask 1 5) (Seq.seq_hide #Secret.U8 (pn_sizemask_ct ppn_len)) 0;
  assert (ppnmask_ct == Seq.seq_reveal pnmask_ct);
  Lemmas.secret_xor_inplace_eq packet' pnmask_ct pn_offset

#pop-options

#push-options "--z3rlimit 256 --query_stats --z3cliopt smt.arith.nl=false --fuel 2 --ifuel 1"

#restart-solver

inline_for_extraction
let header_decrypt_aux_ct_secret_preserving_not_retry'
  (a: ea)
  (s: CTR.state (SAEAD.cipher_alg_of_supported_alg a))
  (k: B.buffer Secret.uint8)
  (cid_len: short_dcid_len_t)
  (is_short: bool)
  (pn_offset: U32.t)
  (dst: B.buffer Secret.uint8)
: HST.Stack unit
  (requires (fun m ->
    let l = B.length dst in
    B.all_live m [B.buf k; B.buf dst] /\
    CTR.invariant m s /\
    B.length k == SCipher.key_length (SAEAD.cipher_alg_of_supported_alg a) /\
    B.all_disjoint
      [ CTR.footprint m s; B.loc_buffer k; B.loc_buffer dst] /\
    0 < l /\ l < pow2 32 /\ (
    let i = Secret.v #Secret.U8 (Seq.index (B.as_seq m dst) 0) in
    (is_short == true <==> BF.get_bitfield #8 i 7 8 == 0) /\
    (~ (not is_short && BF.get_bitfield #8 i 4 6 = 3)) /\ (
    match Parse.putative_pn_offset (U32.v cid_len) (Seq.seq_reveal (B.as_seq m dst)) with
    | None -> False
    | Some pn_offset' ->
      U32.v pn_offset == pn_offset' /\
      pn_offset' + 20 <= l
  ))))
  (ensures (fun m _ m' ->
    B.modifies (B.loc_buffer dst `B.loc_union` CTR.footprint m s) m m' /\
    CTR.invariant m' s /\
    CTR.footprint m s == CTR.footprint m' s /\
    (header_decrypt_aux_ct_secret_preserving_not_retry_spec a (B.as_seq m k) (U32.v cid_len) (B.as_seq m dst) is_short (U32.v pn_offset)).Spec.packet == Seq.seq_reveal (B.as_seq m' dst)
  ))
= let m0 = HST.get () in
  let f = B.index dst 0ul in
  let sample_offset = pn_offset `U32.add` 4ul in
  let sample = B.sub dst sample_offset 16ul in
  HST.push_frame ();
  let m1 = HST.get () in
  B.loc_unused_in_not_unused_in_disjoint m1;
  let mask = B.alloca (Secret.to_u8 0uy) 16ul in
  assert (B.loc_disjoint (B.loc_buffer mask) (B.loc_buffer dst `B.loc_union` CTR.footprint m0 s));
  let m2 = HST.get () in
  B.loc_unused_in_not_unused_in_disjoint m2;
  let pn_sm = B.alloca (Secret.to_u8 0uy) 4ul in
  assert (B.loc_disjoint (B.loc_buffer mask) (B.loc_buffer pn_sm));
  assert (B.loc_disjoint (B.loc_buffer pn_sm) (B.loc_buffer dst `B.loc_union` CTR.footprint m0 s));
  let m3 = HST.get () in
  let gsample = Ghost.hide (Seq.slice (B.as_seq m0 dst) (U32.v sample_offset) (U32.v sample_offset + 16)) in
  assert (B.as_seq m3 sample == Ghost.reveal gsample);
  block_of_sample (SAEAD.cipher_alg_of_supported_alg a) mask s k sample;
  let m4 = HST.get () in
  let gmask = Ghost.hide (Spec.block_of_sample (SAEAD.cipher_alg_of_supported_alg a) (B.as_seq m0 k) gsample) in
  assert (B.as_seq m4 mask == Ghost.reveal gmask);
  let protected_bits = if is_short then 5ul else 4ul in
  let mask0 = B.index mask 0ul in
  let f_logxor = f `Secret.logxor` mask0 in
  let f_bf = Secret.get_bitfield (f_logxor) 0ul protected_bits in
  let f' = Secret.set_bitfield f 0ul protected_bits f_bf in
  B.upd dst 0ul f';
  let m5 = HST.get () in
  let gpacket' = Ghost.hide (Seq.cons f' (Seq.slice (B.as_seq m0 dst) 1 (B.length dst))) in
  assert (Ghost.reveal gpacket' `Seq.equal` B.as_seq m5 dst);
  let pn_len = Secret.get_bitfield f' 0ul 2ul in
  pn_sizemask pn_sm (Secret.cast_up Secret.U32 pn_len `Secret.add` Secret.hide 1ul);
  let pnmask = B.sub mask 1ul 4ul in
  Lemmas.op_inplace pnmask pn_sm 4ul 0ul (Secret.logand #Secret.U8 #Secret.SEC);
  let m6 = HST.get () in
  let gpnmask = Ghost.hide (Lemmas.secret_and_inplace (Seq.slice gmask 1 5) (Seq.seq_hide #Secret.U8 (pn_sizemask_ct (Secret.v pn_len))) 0) in
  assert (Ghost.reveal gpnmask == B.as_seq m6 pnmask);
  Lemmas.op_inplace dst pnmask 4ul pn_offset (Secret.logxor #Secret.U8 #Secret.SEC);
  HST.pop_frame ();
  let m7 = HST.get () in
  assert (B.as_seq m7 dst == Lemmas.secret_xor_inplace gpacket' gpnmask (U32.v pn_offset))

#pop-options

#push-options "--z3rlimit 32 --query_stats"

#restart-solver

let header_decrypt_aux_ct_secret_preserving_not_retry
  (a: ea)
  (s: CTR.state (SAEAD.cipher_alg_of_supported_alg a))
  (k: B.buffer Secret.uint8)
  (cid_len: short_dcid_len_t)
  (is_short: bool)
  (pn_offset: U32.t)
  (dst: B.buffer U8.t)
: HST.Stack unit
  (requires (fun m ->
    let l = B.length dst in
    B.all_live m [B.buf k; B.buf dst] /\
    CTR.invariant m s /\
    B.length k == SCipher.key_length (SAEAD.cipher_alg_of_supported_alg a) /\
    B.all_disjoint
      [ CTR.footprint m s; B.loc_buffer k; B.loc_buffer dst] /\
    0 < l /\ l < pow2 32 /\ (
    let i = Secret.v #Secret.U8 (Seq.index (B.as_seq m dst) 0) in
    (is_short == true <==> BF.get_bitfield #8 i 7 8 == 0) /\
    (~ (not is_short && BF.get_bitfield #8 i 4 6 = 3)) /\ (
    match Parse.putative_pn_offset (U32.v cid_len) (B.as_seq m dst) with
    | None -> False
    | Some pn_offset' ->
      U32.v pn_offset == pn_offset' /\
      pn_offset' + 20 <= l
  ))))
  (ensures (fun m _ m' ->
    match Spec.header_decrypt_aux a (B.as_seq m k) (U32.v cid_len) (B.as_seq m dst) with
    | None -> False
    | Some res ->
      let len_mod = U32.v pn_offset + res.Spec.pn_len + 1 in
      res.Spec.pn_offset == U32.v pn_offset /\
      len_mod <= B.length dst /\
      B.modifies (B.loc_buffer (B.gsub dst 0ul (U32.uint_to_t len_mod)) `B.loc_union` CTR.footprint m s) m m' /\
      CTR.invariant m' s /\
      CTR.footprint m s == CTR.footprint m' s /\
      res.Spec.packet == B.as_seq m' dst
  ))
=
  let m = HST.get () in
  SecretBuffer.with_whole_buffer_hide_weak_modifies
    #unit
    dst
    m
    (CTR.footprint m s `B.loc_union` B.loc_buffer k)
    (CTR.footprint m s)
    true
    (fun _ cont m' ->
      (header_decrypt_aux_ct_secret_preserving_not_retry_spec a (B.as_seq m k) (U32.v cid_len) (Seq.seq_hide #Secret.U8 (B.as_seq m dst)) is_short (U32.v pn_offset)).Spec.packet == cont /\
      CTR.invariant m' s /\
      CTR.footprint m s == CTR.footprint m' s
    )
    (fun _ bs ->
      header_decrypt_aux_ct_secret_preserving_not_retry' a s k cid_len is_short pn_offset bs
    );
  let m' = HST.get () in
  header_decrypt_aux_ct_secret_preserving_not_retry_spec_correct a (B.as_seq m k) (U32.v cid_len) (Seq.seq_hide #Secret.U8 (B.as_seq m dst)) is_short (U32.v pn_offset);
  header_decrypt_aux_ct_correct a (B.as_seq m k) (U32.v cid_len) (B.as_seq m dst);
  Spec.header_decrypt_aux_post a (B.as_seq m k) (U32.v cid_len) (B.as_seq m dst);
  let len_mod = Ghost.hide (U32.uint_to_t (U32.v pn_offset + (Some?.v (Spec.header_decrypt_aux a (B.as_seq m k) (U32.v cid_len) (B.as_seq m dst))).Spec.pn_len + 1)) in
  B.modifies_loc_buffer_from_to_intro dst 0ul len_mod (CTR.footprint m s) m m'

#pop-options

type header_decrypt_aux_result =
  | HD_Failure
  | HD_Success_Retry
  | HD_Success_NotRetry

unfold
let header_decrypt_aux_pre
  (a: ea)
  (s: CTR.state (SAEAD.cipher_alg_of_supported_alg a))
  (k: B.buffer Secret.uint8)
  (cid_len: short_dcid_len_t)
  (dst: B.buffer U8.t)
  (dst_len: U32.t)
  (m: HS.mem)
: GTot Type0
=
    let l = B.length dst in
    B.all_live m [B.buf k; B.buf dst] /\
    CTR.invariant m s /\
    B.length k == SCipher.key_length (SAEAD.cipher_alg_of_supported_alg a) /\
    B.all_disjoint
      [ CTR.footprint m s; B.loc_buffer k; B.loc_buffer dst] /\
    B.length dst == U32.v dst_len

unfold
let header_decrypt_aux_post
  (a: ea)
  (s: CTR.state (SAEAD.cipher_alg_of_supported_alg a))
  (k: B.buffer Secret.uint8)
  (cid_len: short_dcid_len_t)
  (dst: B.buffer U8.t)
  (dst_len: U32.t)
  (m: HS.mem)
  (rs: header_decrypt_aux_result)
  (m' : HS.mem)
: GTot Type0
=
  header_decrypt_aux_pre a s k cid_len dst dst_len m /\
  CTR.invariant m' s /\
  CTR.footprint m s == CTR.footprint m' s /\
  begin match rs, Spec.header_decrypt_aux a (B.as_seq m k) (U32.v cid_len) (B.as_seq m dst) with
    | HD_Failure, None ->
      B.modifies B.loc_none m m'
    | HD_Failure, _ -> False
    | _, Some res ->
      res.Spec.packet == B.as_seq m' dst /\
      res.Spec.is_retry == (HD_Success_Retry? rs) /\
      (if res.Spec.is_retry
      then B.modifies B.loc_none m m'
      else
        let len = res.Spec.pn_offset + res.Spec.pn_len + 1 in
        len <= B.length dst /\
        B.modifies (CTR.footprint m s `B.loc_union` B.loc_buffer (B.gsub dst 0ul (U32.uint_to_t len))) m m'
      )
    | _ -> False
  end

let header_decrypt_aux
  (a: ea)
  (s: CTR.state (SAEAD.cipher_alg_of_supported_alg a))
  (k: B.buffer Secret.uint8)
  (cid_len: short_dcid_len_t)
  (dst: B.buffer U8.t)
  (dst_len: U32.t)
: HST.Stack header_decrypt_aux_result
  (requires (fun m ->
    header_decrypt_aux_pre a s k cid_len dst dst_len m
  ))
  (ensures (fun m rs m' ->
    header_decrypt_aux_post a s k cid_len dst dst_len m rs m'
  ))
= let m = HST.get () in
  if dst_len = 0ul
  then HD_Failure
  else
    let f = B.index dst 0ul in
    let short_or_long = BF.uint8.BF.get_bitfield f 7 8 in
    let isshort = short_or_long = 0uy in
    let retry_or_other = BF.uint8.BF.get_bitfield f 4 6 in
    let isretry = not isshort && (retry_or_other = 3uy) in
    if isretry
    then HD_Success_Retry
    else match ParseImpl.putative_pn_offset cid_len dst dst_len with
    | None -> HD_Failure
    | Some pn_offset ->
      if dst_len `U32.lt` (pn_offset `U32.add` 20ul)
      then HD_Failure
      else begin
        header_decrypt_aux_ct_secret_preserving_not_retry a s k cid_len isshort pn_offset dst;
        HD_Success_NotRetry
      end

let max_cipher_length64 : (x: Secret.uint64 { Secret.v x == max_cipher_length }) =
  Secret.mk_int (norm [delta; iota; zeta; primops] (pow2 32 - header_len_bound))

let secret_max_correct
  (x y: Secret.uint64)
: Lemma
  (Secret.v (Secret.max64 x y) == Spec.max (Secret.v x) (Secret.v y))
  [SMTPat (Secret.max64 x y)]
= ()

let secret_min_correct
  (x y: Secret.uint64)
: Lemma
  (Secret.v (Secret.min64 x y) == Spec.min (Secret.v x) (Secret.v y))
  [SMTPat (Secret.min64 x y)]
= ()

#push-options "--z3rlimit 2048 --query_stats --ifuel 3 --fuel 2 --z3cliopt smt.arith.nl=false"

#restart-solver

inline_for_extraction
let header_decrypt_retry
  (a: ea)
  (s: CTR.state (SAEAD.cipher_alg_of_supported_alg a))
  (k: B.buffer Secret.uint8)
  (cid_len: short_dcid_len_t)
  (last: PN.last_packet_number_t)
  (dst:B.buffer U8.t)
  (dst_len: U32.t)
  (m0: HS.mem)
: HST.Stack h_result
  (requires (fun m ->
    header_decrypt_pre a s k cid_len last dst dst_len m0 /\
    header_decrypt_aux_post a s k cid_len dst dst_len m0 HD_Success_Retry m
  ))
  (ensures (fun _ rs m' ->
    header_decrypt_post a s k cid_len last dst dst_len m0 rs m'
  ))
= 
    let m1 = HST.get () in
    Classical.move_requires (Parse.parse_header_exists (U32.v cid_len) (Secret.v last)) (B.as_seq m1 dst);
    Classical.move_requires (Parse.parse_header_exists_recip (U32.v cid_len) (Secret.v last)) (B.as_seq m1 dst);
    (* In the Retry case, header_decrypt_aux did nothing, so we need
       to check here that the header can be parsed. *)
    Spec.header_decrypt_aux_post a (B.as_seq m0 k) (U32.v cid_len) (B.as_seq m0 dst);
    if None? (ParseImpl.putative_pn_offset cid_len dst dst_len)
    then H_Failure
    else begin
      Spec.header_decrypt_aux_post_parse a (B.as_seq m0 k) (U32.v cid_len) (Secret.v last) (B.as_seq m0 dst);
      Parse.lemma_header_parsing_post (U32.v cid_len) (Secret.v last) (B.as_seq m1 dst);
      let (h, pn) = ParseImpl.read_header dst dst_len cid_len last in
      let m2 = HST.get () in
      ParseImpl.header_len_correct h m2 pn;
      H_Success h pn (Secret.to_u32 0ul)
    end

#restart-solver

inline_for_extraction
let header_decrypt_not_retry
  (a: ea)
  (s: CTR.state (SAEAD.cipher_alg_of_supported_alg a))
  (k: B.buffer Secret.uint8)
  (cid_len: short_dcid_len_t)
  (last: PN.last_packet_number_t)
  (dst:B.buffer U8.t)
  (dst_len: U32.t)
  (m0: HS.mem)
: HST.Stack h_result
  (requires (fun m ->
    header_decrypt_pre a s k cid_len last dst dst_len m0 /\
    header_decrypt_aux_post a s k cid_len dst dst_len m0 HD_Success_NotRetry m
  ))
  (ensures (fun _ rs m' ->
    header_decrypt_post a s k cid_len last dst dst_len m0 rs m'
  ))
= 
    let m1 = HST.get () in
    Classical.move_requires (Parse.parse_header_exists (U32.v cid_len) (Secret.v last)) (B.as_seq m1 dst);
    Classical.move_requires (Parse.parse_header_exists_recip (U32.v cid_len) (Secret.v last)) (B.as_seq m1 dst);
    (* In other cases, header_decrypt_aux already checked
       that the header can be parsed. *)
    Spec.header_decrypt_aux_post a (B.as_seq m0 k) (U32.v cid_len) (B.as_seq m0 dst);
    Spec.header_decrypt_aux_post_parse a (B.as_seq m0 k) (U32.v cid_len) (Secret.v last) (B.as_seq m0 dst);
    Parse.lemma_header_parsing_post (U32.v cid_len) (Secret.v last) (B.as_seq m1 dst);
    let (h, pn) = ParseImpl.read_header dst dst_len cid_len last in
    let m2 = HST.get () in
    ParseImpl.header_len_correct h m2 pn;
    let hlen = header_len h in
    assert (Seq.length (Parse.format_header (g_header h m2 pn)) == Secret.v hlen);
    assert (Secret.v hlen <= B.length dst);
    let rlen = Secret.hide dst_len `Secret.usub` hlen in
    let hlen64 = Secret.cast_up Secret.U64 hlen in
    let rlen64 = Secret.cast_up Secret.U64 rlen in
    let clen64 = if has_payload_length h then payload_length h else rlen64 in
    let clen64_checked : Secret.uint64 =
      Secret.max64 (Secret.min64 (Secret.min64 clen64 rlen64) (max_cipher_length64 `Secret.sub` Secret.hide 1uL)) (Secret.hide 16uL)
    in
    assert_norm (16 < max_cipher_length);
    assert (Secret.v clen64_checked < max_cipher_length);
    assert (Secret.v clen64_checked <= Secret.v rlen);
    assert_norm (max_cipher_length < pow2 32);
    let clen32 = Secret.cast_down Secret.U32 clen64_checked in
    let bh = Ghost.hide (B.gsub dst 0ul (Secret.reveal hlen)) in
    let brem = Ghost.hide (B.gsub dst (Secret.reveal hlen) (Secret.reveal rlen)) in
    let bc = Ghost.hide (B.gsub brem 0ul (Secret.reveal clen32)) in
    let b3 = Ghost.hide (B.gsub brem (Secret.reveal clen32) (Secret.reveal rlen `U32.sub` Secret.reveal clen32)) in
    assert (B.as_seq m2 bh == B.as_seq m1 bh);
    assert (B.as_seq m1 bh == Parse.format_header (g_header h m2 pn));
    assert (B.disjoint bh brem);
    assert (B.as_seq m2 brem == B.as_seq m1 brem);
    assert (B.as_seq m1 brem == B.as_seq m0 brem);
    assert (B.as_seq m2 bc == B.as_seq m1 bc);
    assert (B.as_seq m1 bc == B.as_seq m0 bc);
    assert (B.as_seq m2 b3 == B.as_seq m1 b3);
    assert (B.as_seq m1 b3 == B.as_seq m0 b3);
    assert (B.as_seq m2 dst `Seq.equal` (B.as_seq m2 bh `Seq.append` B.as_seq m2 bc `Seq.append` B.as_seq m2 b3));
    H_Success h pn clen32

#restart-solver

let header_decrypt
  a s k cid_len last dst dst_len
=
  let m = HST.get () in
  assert (B.length dst == 0 ==> None? (Spec.header_decrypt_aux a (B.as_seq m k) (U32.v cid_len) (B.as_seq m dst)));
  let aux = header_decrypt_aux a s k cid_len dst dst_len in
  let m1 = HST.get () in
  Classical.move_requires (Parse.parse_header_exists (U32.v cid_len) (Secret.v last)) (B.as_seq m1 dst);
  Classical.move_requires (Parse.parse_header_exists_recip (U32.v cid_len) (Secret.v last)) (B.as_seq m1 dst);
  match aux with
  | HD_Failure -> H_Failure
  | HD_Success_Retry ->
    header_decrypt_retry a s k cid_len last dst dst_len m
  | _ ->
    header_decrypt_not_retry a s k cid_len last dst dst_len m

#pop-options
