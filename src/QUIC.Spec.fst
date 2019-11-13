module QUIC.Spec
open QUIC.Spec.Lemmas
open QUIC.Spec.Header

module S = FStar.Seq
module U32 = FStar.UInt32
module U8 = FStar.UInt8
module H = Spec.Agile.Hash
module HD = Spec.Hash.Definitions
module Cipher = Spec.Agile.Cipher
module AEAD = Spec.Agile.AEAD
module HKDF = Spec.Agile.HKDF

#set-options "--max_fuel 0 --max_ifuel 0"

// two lines to break the abstraction of UInt8 used for
// side-channel protection (useless here). Copied from mitls-fstar
// src/tls/declassify.fst (branch dev)
friend Lib.IntTypes
let declassify : squash (Lib.IntTypes.uint8 == UInt8.t)= ()

inline_for_extraction
let prefix_l: List.Tot.llist U8.t 11 =
  // JP: "tls13 quic "
  [@inline_let]
  let l = [0x74uy; 0x6cuy; 0x73uy; 0x31uy; 0x33uy;
           0x20uy; 0x71uy; 0x75uy; 0x69uy; 0x63uy; 0x20uy] in
  assert_norm (List.Tot.length l == 11);
  l

let prefix: lbytes 11 =
  S.seq_of_list prefix_l

#push-options "--z3rlimit 10"
let lemma_hash_lengths (a:ha)
  : Lemma (HD.hash_length a <= 64 /\ HD.word_length a <= 8 /\
    HD.block_length a <= 128 /\ HD.max_input_length a >= pow2 61 - 1)
  =
  assert_norm(pow2 61 < pow2 125)
#pop-options

inline_for_extraction
let label_key_l: List.Tot.llist U8.t 3 =
  [@inline_let]
  let l = [ 0x6buy; 0x65uy; 0x79uy ] in
  assert_norm (List.Tot.length l = 3);
  l

let label_key =
  Seq.seq_of_list label_key_l

inline_for_extraction
let label_iv_l: List.Tot.llist U8.t 2 =
  [@inline_let]
  let l = [ 0x69uy; 0x76uy ] in
  assert_norm (List.Tot.length l = 2);
  l

let label_iv =
  Seq.seq_of_list label_iv_l

inline_for_extraction
let label_hp_l: List.Tot.llist U8.t 2 =
  [@inline_let]
  let l = [ 0x68uy; 0x70uy ] in
  assert_norm (List.Tot.length l = 2);
  l

let label_hp =
  Seq.seq_of_list label_hp_l

let derive_secret a prk label len =
  let open S in
  let z = S.create 1 0uy in
  let lb = S.create 1 (U8.uint_to_t len) in // len <= 255
  let llen = S.create 1 (U8.uint_to_t (11 + Seq.length label)) in
  let info = z @| lb @| llen @| prefix @| label @| z in
  lemma_hash_lengths a;
  assert_norm(452 < pow2 61);
  HKDF.expand a prk info len

(*
Constant time decryption of packet number (without branching on pn_len)
packet[pn_offset..pn_offset+4] ^= pn_mask &
  match pn_len with
  | 0 -> mask & 0xFF000000
  | 1 -> mask & 0xFFFF0000
  | 2 -> mask & 0xFFFFFF00
  | 3 -> mask & 0xFFFFFFFF
*)
inline_for_extraction
let pn_sizemask_ct (pn_len:nat2) : lbytes 4 =
  let open FStar.Endianness in
  FStar.Math.Lemmas.pow2_lt_compat 32 (24 - (8 `op_Multiply` pn_len));
  FStar.Endianness.n_to_be 4 (pow2 32 - pow2 (24 - (8 `op_Multiply` pn_len)))

let index_pn_sizemask_ct_right
  (pn_len: nat2)
  (i: nat {i > pn_len /\ i < 4})
: Lemma
  (S.index (pn_sizemask_ct pn_len) i == 0uy)
= let open FStar.Endianness in
  let open FStar.Math.Lemmas in
  let open FStar.Mul in
  pow2_lt_compat 32 (24 - (8 `op_Multiply` pn_len));
  pow2_plus (24 - (8 * pn_len)) (8 * (pn_len + 1));
  index_n_to_be_zero_right 4 (pow2 32 - pow2 (24 - (8 * pn_len))) i

inline_for_extraction
let pn_sizemask_naive (pn_len:nat2) : lbytes (pn_len + 1) =
  S.slice (pn_sizemask_ct pn_len) 0 (pn_len + 1)

let block_of_sample a (k: Cipher.key a) (sample: lbytes 16): lbytes 16 =
  let open FStar.Mul in
  let ctr, iv = match a with
    | Cipher.CHACHA20 ->
        let ctr_bytes, iv = S.split sample 4 in
        FStar.Endianness.lemma_le_to_n_is_bounded ctr_bytes;
        assert_norm (pow2 (8 * 4) = pow2 32);
        FStar.Endianness.le_to_n ctr_bytes, iv
    | _ ->
        let iv, ctr_bytes = S.split sample 12 in
        FStar.Endianness.lemma_be_to_n_is_bounded ctr_bytes;
        assert_norm (pow2 (8 * 4) = pow2 32);
        FStar.Endianness.be_to_n ctr_bytes, iv
  in
  S.slice (Cipher.ctr_block a k iv ctr) 0 16

(* See https://tools.ietf.org/html/draft-ietf-quic-tls-19#section-5.4 *)

module BF = LowParse.BitFields

let header_encrypt a hpk h c =
  assert_norm(max_cipher_length < pow2 62);
  let r = S.(format_header h `append` c) in
  if is_retry h
  then
    r
  else
    let pn_offset = pn_offset h in
    let pn_len = U32.v (pn_length h) - 1 in
    let sample = S.slice c (3-pn_len) (19-pn_len) in
    let mask = block_of_sample (AEAD.cipher_alg_of_supported_alg a) hpk sample in
    let pnmask = and_inplace (S.slice mask 1 (pn_len + 2)) (pn_sizemask_naive pn_len) 0 in
    let f = S.index r 0 in
    let protected_bits = if MShort? h then 5 else 4 in
    let f' = BF.set_bitfield (U8.v f) 0 protected_bits (BF.get_bitfield (U8.v f `FStar.UInt.logxor` U8.v (S.index mask 0)) 0 protected_bits) in
    let r = xor_inplace r pnmask pn_offset in
    let r = S.cons (U8.uint_to_t f') (S.slice r 1 (S.length r)) in
    r

(* A constant-time specification of header_encrypt which does not test or truncate on pn_len *)

let header_encrypt_ct
  (a:ea)
  (hpk: lbytes (ae_keysize a))
  (h: header)
  (c: cbytes' (is_retry h))
: GTot packet
= 
  assert_norm(max_cipher_length < pow2 62);
  let r = S.(format_header h `append` c) in
  if is_retry h
  then
    r
  else
    let pn_offset = pn_offset h in
    let pn_len = U32.v (pn_length h) - 1 in
    let sample = S.slice c (3-pn_len) (19-pn_len) in
    let mask = block_of_sample (AEAD.cipher_alg_of_supported_alg a) hpk sample in
    let pnmask = and_inplace (S.slice mask 1 5) (pn_sizemask_ct pn_len) 0 in
    let f = S.index r 0 in
    let protected_bits = if MShort? h then 5 else 4 in
    let f' = BF.set_bitfield (U8.v f) 0 protected_bits (BF.get_bitfield (U8.v f `FStar.UInt.logxor` U8.v (S.index mask 0)) 0 protected_bits) in
    let r = xor_inplace r pnmask pn_offset in
    let r = S.cons (U8.uint_to_t f') (S.slice r 1 (S.length r)) in
    r

#push-options "--z3rlimit 16"

let header_encrypt_ct_correct
  (a:ea)
  (hpk: lbytes (ae_keysize a))
  (h: header)
  (c: cbytes' (is_retry h))
: Lemma
  (header_encrypt_ct a hpk h c `S.equal` header_encrypt a hpk h c)
=
  assert_norm(max_cipher_length < pow2 62);
  let r = S.(format_header h `append` c) in
  if is_retry h
  then ()
  else begin
    let pn_offset = pn_offset h in
    let pn_len = U32.v (pn_length h) - 1 in
    let sample = S.slice c (3-pn_len) (19-pn_len) in
    let mask = block_of_sample (AEAD.cipher_alg_of_supported_alg a) hpk sample in
    let pnmask_ct = and_inplace (S.slice mask 1 5) (pn_sizemask_ct pn_len) 0 in
    let pnmask_naive = and_inplace (S.slice mask 1 (pn_len + 2)) (pn_sizemask_naive pn_len) 0 in
    pointwise_op_split U8.logand (S.slice mask 1 5) (pn_sizemask_ct pn_len) 0 (pn_len + 1);
    assert (pnmask_naive `S.equal` S.slice pnmask_ct 0 (pn_len + 1));
    S.lemma_split r (pn_offset + pn_len + 1);
    pointwise_op_split U8.logxor r pnmask_ct pn_offset (pn_offset + pn_len + 1);
    pointwise_op_split U8.logxor r pnmask_naive pn_offset (pn_offset + pn_len + 1);
    pointwise_op_empty U8.logxor (S.slice r (pn_offset + pn_len + 1) (S.length r)) (S.slice pnmask_naive (pn_len + 1) (S.length pnmask_naive)) 0;
    xor_inplace_zero (S.slice r (pn_offset + pn_len + 1) (S.length r)) (S.slice pnmask_ct (pn_len + 1) 4)
      (fun i ->
        and_inplace_zero
          (S.slice mask (pn_len + 2) 5)
          (S.slice (pn_sizemask_ct pn_len) (pn_len + 1) 4)
          (fun j -> index_pn_sizemask_ct_right pn_len (j + (pn_len + 1)))
          i
      )
      0
  end

#pop-options

module U64 = FStar.UInt64

#push-options "--z3rlimit 32"

let header_encrypt_post
  (a:ea)
  (hpk: lbytes (ae_keysize a))
  (h: header)
  (c: cbytes' (is_retry h))
  (cid_len: nat { MShort? h ==> cid_len == dcid_len h })
: Lemma (
    let x = format_header h in
    let y = x `S.append` c in
    let z = header_encrypt a hpk h c in
    header_len h + S.length c == S.length z /\
    S.slice z (header_len h) (S.length z) `S.equal` c /\
    MShort? h == (BF.get_bitfield (U8.v (S.index z 0)) 7 8 = 0) /\
    is_retry h == (not (MShort? h) && BF.get_bitfield (U8.v (S.index z 0)) 4 6 = 3) /\ (
    if is_retry h
    then z == y
    else putative_pn_offset cid_len z == Some (pn_offset h)
  ))
= format_header_is_short h;
  format_header_is_retry h;
  if is_retry h
  then ()
  else begin
    format_header_pn_length h;
    let x = format_header h in
    let y = x `S.append` c in
    let pn_offset = pn_offset h in
    let pn_len = U32.v (pn_length h) - 1 in
    let sample = S.slice c (3-pn_len) (19-pn_len) in
    let mask = block_of_sample (AEAD.cipher_alg_of_supported_alg a) hpk sample in
    let pnmask = and_inplace (S.slice mask 1 (pn_len + 2)) (pn_sizemask_naive pn_len) 0 in
    let f = S.index y 0 in
    let protected_bits = if MShort? h then 5 else 4 in
    let bf = BF.get_bitfield (U8.v f `FStar.UInt.logxor` U8.v (S.index mask 0)) 0 protected_bits in
    let f' = BF.set_bitfield (U8.v f) 0 protected_bits bf in
    let r = xor_inplace y pnmask pn_offset in
    let z = header_encrypt a hpk h c in
    assert (z == S.cons (U8.uint_to_t f') (S.slice r 1 (S.length r)));
    pointwise_op_slice_other U8.logxor y pnmask pn_offset 0 1;
    pointwise_op_slice_other U8.logxor y pnmask pn_offset 1 pn_offset;
    assert (pn_offset > 0);
    pointwise_op_slice_other U8.logxor y pnmask pn_offset (header_len h) (S.length y);
    assert (S.slice z (header_len h) (S.length z) `S.equal` S.slice y (header_len h) (S.length y));
    assert (U8.uint_to_t f' == S.index (S.slice z 0 1) 0);
    BF.get_bitfield_set_bitfield_other (U8.v f) 0 protected_bits bf 7 8;
    BF.get_bitfield_set_bitfield_other (U8.v f) 0 protected_bits bf protected_bits 8;
    if MLong? h
    then BF.get_bitfield_set_bitfield_other (U8.v f) 0 protected_bits bf 4 6;
    putative_pn_offset_correct h cid_len;
    putative_pn_offset_frame cid_len x y;
    putative_pn_offset_frame cid_len y z;
    ()
  end

#pop-options

noextract
type header_decrypt_aux_t = {
  is_short: bool;
  is_retry: (is_retry: bool { is_retry ==> ~ (is_short) });
  packet: packet;
  pn_offset: (if is_retry then unit else nat);
  pn_len: (if is_retry then unit else (pn_len: nat2 {pn_offset + pn_len + 1 <= S.length packet}));
}

let header_decrypt_aux
  (a:ea)
  (hpk: lbytes (ae_keysize a))
  (cid_len: nat { cid_len < 20 })
  (packet: packet)
: GTot (option header_decrypt_aux_t)
= let open FStar.Math.Lemmas in
  if S.length packet = 0
  then None
  else
    let f = S.index packet 0 in
    let is_short = (BF.get_bitfield (U8.v f) 7 8 = 0) in
    let is_retry = not is_short && BF.get_bitfield (U8.v f) 4 6 = 3 in
    if is_retry
    then
      Some ({
        is_short = is_short;
        is_retry = is_retry;
        packet = packet;
        pn_offset = ();
        pn_len = ();
      })
    else
      match putative_pn_offset cid_len packet with
      | None -> None
      | Some pn_offset ->
        let sample_offset = pn_offset + 4 in
        if sample_offset + 16 > S.length packet
        then None
        else begin
          let sample = S.slice packet sample_offset (sample_offset+16) in
          let mask = block_of_sample (AEAD.cipher_alg_of_supported_alg a) hpk sample in
          (* mask the least significant bits of the first byte *)
          let protected_bits = if is_short then 5 else 4 in
          let f' = BF.set_bitfield (U8.v f) 0 protected_bits (BF.get_bitfield (U8.v f `FStar.UInt.logxor` U8.v (S.index mask 0)) 0 protected_bits) in
          let packet' = S.cons (U8.uint_to_t f') (S.slice packet 1 (S.length packet)) in
          (* now the packet number length is available, so mask the packet number *)
          let pn_len = BF.get_bitfield f' 0 2 in
          let pnmask = and_inplace (S.slice mask 1 (pn_len + 2)) (pn_sizemask_naive pn_len) 0 in
          let packet'' = xor_inplace packet' pnmask pn_offset in
          Some ({
            is_short = is_short;
            is_retry = is_retry;
            packet = packet'';
            pn_offset = pn_offset;
            pn_len = pn_len;
          })
        end

#push-options "--max_ifuel 1"

#push-options "--z3rlimit 32"

let header_decrypt_aux_post
  (a:ea)
  (hpk: lbytes (ae_keysize a))
  (cid_len: nat { cid_len < 20 })
  (packet: packet)
: Lemma
  (requires (Some? (header_decrypt_aux a hpk cid_len packet)))
  (ensures (
    let Some r = header_decrypt_aux a hpk cid_len packet in
    S.length r.packet == S.length packet /\
    S.length packet > 0 /\ (
    let f' = S.index r.packet 0 in
    r.is_short == (BF.get_bitfield (U8.v f') 7 8 = 0) /\
    r.is_retry == (not r.is_short && (BF.get_bitfield (U8.v f') 4 6 = 3)) /\ (
    if r.is_retry
    then r.packet == packet
    else
      Some? (putative_pn_offset cid_len packet) /\
      putative_pn_offset cid_len r.packet == putative_pn_offset cid_len packet /\ (
      let Some pn_offset = putative_pn_offset cid_len packet in
      r.pn_len == BF.get_bitfield (U8.v f') 0 2 /\
      S.slice r.packet (r.pn_offset + r.pn_len + 1) (S.length r.packet) `S.equal` S.slice packet (r.pn_offset + r.pn_len + 1) (S.length packet) /\
      True
  )))))
= let Some r = header_decrypt_aux a hpk cid_len packet in
  let f = S.index packet 0 in
  let is_short = (BF.get_bitfield (U8.v f) 7 8 = 0) in
  let is_retry = not is_short && BF.get_bitfield (U8.v f) 4 6 = 3 in
  if is_retry
  then ()
  else begin
    let Some pn_offset = putative_pn_offset cid_len packet in
    let sample_offset = pn_offset + 4 in
    let sample = S.slice packet sample_offset (sample_offset+16) in
    let mask = block_of_sample (AEAD.cipher_alg_of_supported_alg a) hpk sample in
    (* mask the least significant bits of the first byte *)
    let protected_bits = if is_short then 5 else 4 in
    let bf = BF.get_bitfield (U8.v f `FStar.UInt.logxor` U8.v (S.index mask 0)) 0 protected_bits in
    let f' = BF.set_bitfield (U8.v f) 0 protected_bits bf in
    let packet' = S.cons (U8.uint_to_t f') (S.slice packet 1 (S.length packet)) in
    (* now the packet number length is available, so mask the packet number *)
    let pn_len = BF.get_bitfield f' 0 2 in
    let pnmask = and_inplace (S.slice mask 1 (pn_len + 2)) (pn_sizemask_naive pn_len) 0 in
    assert (r.packet == xor_inplace packet' pnmask pn_offset);
    pointwise_op_slice_other U8.logxor packet' pnmask pn_offset 0 1;
    pointwise_op_slice_other U8.logxor packet' pnmask pn_offset 1 pn_offset;
    pointwise_op_slice_other U8.logxor packet' pnmask pn_offset (pn_offset + pn_len + 1) (S.length packet);
    BF.get_bitfield_set_bitfield_other (U8.v f) 0 protected_bits bf protected_bits 8;
    BF.get_bitfield_set_bitfield_other (U8.v f) 0 protected_bits bf 7 8;
    assert (S.index r.packet 0 == S.index (S.slice packet' 0 1) 0);
    putative_pn_offset_frame cid_len packet r.packet;
    if not is_short
    then BF.get_bitfield_set_bitfield_other (U8.v f) 0 protected_bits bf 4 6;
    assert (putative_pn_offset cid_len r.packet == putative_pn_offset cid_len packet);
    ()
  end

#pop-options

#push-options "--z3rlimit 64"

module Header = QUIC.Spec.Header

let header_decrypt_aux_post_parse
  (a:ea)
  (hpk: lbytes (ae_keysize a))
  (cid_len: nat { cid_len < 20 })
  (last: nat { last + 1 < pow2 62 })
  (packet: packet)
: Lemma
  (requires (match header_decrypt_aux a hpk cid_len packet with
    | Some r ->
      Header.H_Success? (parse_header cid_len last r.packet)
    | _ -> False
  ))
  (ensures (
    let Some r = header_decrypt_aux a hpk cid_len packet in
    let Header.H_Success h rem' = parse_header cid_len last r.packet in
    header_len h <= S.length packet /\
    S.length r.packet == S.length packet /\
    S.length packet > 0 /\ (
    r.is_short == MShort? h /\
    r.is_retry == is_retry h /\
    rem' `S.equal` S.slice packet (header_len h) (S.length packet) /\ (
    if r.is_retry
    then r.packet == packet
    else
      Some? (putative_pn_offset cid_len packet) /\ (
      let Some pn_offset = putative_pn_offset cid_len packet in
      pn_offset == Header.pn_offset h /\
      r.pn_len == U32.v (pn_length h) - 1 /\
      r.pn_offset + r.pn_len + 1 == header_len h /\
      True
  )))))
= header_decrypt_aux_post a hpk cid_len packet;
  let Some r = header_decrypt_aux a hpk cid_len packet in
  let Header.H_Success h rem' = parse_header cid_len last r.packet in
  lemma_header_parsing_post cid_len last r.packet;
  format_header_is_short h;
  format_header_is_retry h;
  assert (r.is_short == MShort? h);
  assert (r.is_retry == is_retry h);
  if r.is_retry
  then
    ()
  else begin
    format_header_pn_length h;
    let Some pn_offset = putative_pn_offset cid_len packet in
    putative_pn_offset_correct h cid_len;
    putative_pn_offset_frame cid_len (format_header h) r.packet
  end

#pop-options

#push-options "--z3rlimit 16"

let header_decrypt a hpk cid_len last packet =
  let open FStar.Math.Lemmas in
  if S.length packet = 0
  then H_Failure
  else
    match header_decrypt_aux a hpk cid_len packet with
    | None -> H_Failure
    | Some r ->
      let packet'' = r.packet in
      begin match parse_header cid_len last packet'' with
      | Header.H_Failure -> H_Failure
      | Header.H_Success h rem' ->
        header_decrypt_aux_post_parse a hpk cid_len last packet;
        if is_retry h
        then
          H_Success h S.empty rem'
        else if has_payload_length h && S.length rem' < U64.v (payload_length h)
        then H_Failure
        else
          let clen = if has_payload_length h then U64.v (payload_length h) else S.length rem' in
          if 19 <= clen && clen < max_cipher_length
          then
            let c : cbytes = S.slice rem' 0 clen in
            let rem = S.slice rem' clen (S.length rem') in
            H_Success h c rem
          else
            H_Failure
      end

#pop-options

#push-options "--z3rlimit 128"

let lemma_header_encryption_correct_aux
  (a:ea)
  (k:lbytes (ae_keysize a))
  (h:header)
  (cid_len: nat { cid_len < 20 /\ (MShort? h ==> cid_len == dcid_len h) })
  (c: cbytes' (is_retry h)) // { has_payload_length h ==> U64.v (payload_length h) == S.length c } ->
: Lemma
  (let r' = header_decrypt_aux a k cid_len (header_encrypt a k h c) in
   Some? r' /\ (
   let Some r = r' in
   r.packet `S.equal` (format_header h `S.append` c) /\
   r.is_short == MShort? h /\
   r.is_retry == is_retry h /\
   ((~ (is_retry h)) ==> ((r.pn_offset <: nat) == pn_offset h /\ r.pn_len == U32.v (pn_length h) - 1))
  ))
= header_encrypt_post a k h c cid_len;
  header_decrypt_aux_post a k cid_len (header_encrypt a k h c);
  if is_retry h
  then
    ()
  else begin
    let format = format_header h `S.append` c in
    let packet = header_encrypt a k h c in
    let Some r = header_decrypt_aux a k cid_len packet in
    putative_pn_offset_correct h cid_len;
    let pn_offset = pn_offset h in
    let pn_len = U32.v (pn_length h) - 1 in
    let sample = S.slice c (3-pn_len) (19-pn_len) in
    assert (sample `S.equal` S.slice packet (pn_offset + 4) (pn_offset + 20));
    assert ((r.pn_offset <: nat) == pn_offset);
    let mask = block_of_sample (AEAD.cipher_alg_of_supported_alg a) k sample in
    let protected_bits = if MShort? h then 5 else 4 in
    assert (protected_bits == (if r.is_short then 5 else 4));
    let f = S.index format 0 in
    let pb_value = BF.get_bitfield (U8.v f `FStar.UInt.logxor` U8.v (S.index mask 0)) 0 protected_bits in
    let f0 = BF.set_bitfield (U8.v f) 0 protected_bits pb_value in
    assert (U8.uint_to_t f0 == S.index packet 0);
    let pb_value' = BF.get_bitfield (f0 `FStar.UInt.logxor` U8.v (S.index mask 0)) 0 protected_bits in
    let f1 = BF.set_bitfield f0 0 protected_bits pb_value' in
    let packet1 = S.cons (U8.uint_to_t f1) (S.slice packet 1 (S.length packet)) in
    let pnmask' = and_inplace (S.slice mask 1 (r.pn_len + 2)) (pn_sizemask_naive r.pn_len) 0 in
    assert (r.packet == xor_inplace packet1 pnmask' pn_offset);
    pointwise_op_slice_other U8.logxor packet1 pnmask' pn_offset 0 1;
    assert (S.index r.packet 0 == S.index (S.slice r.packet 0 1) 0);
    assert (S.index r.packet 0 == U8.uint_to_t f1);
    BF.get_bitfield_logxor (U8.v f) (U8.v (S.index mask 0)) 0 protected_bits;
    BF.get_bitfield_set_bitfield_same (U8.v f) 0 protected_bits pb_value;
    BF.get_bitfield_logxor (f0) (U8.v (S.index mask 0)) 0 protected_bits;
    BF.get_bitfield_set_bitfield_same (f0) 0 protected_bits pb_value';
    FStar.UInt.logxor_inv (BF.get_bitfield (U8.v f) 0 protected_bits) (BF.get_bitfield (U8.v (S.index mask 0)) 0 protected_bits);
    assert (BF.get_bitfield (U8.v f) 0 protected_bits == BF.get_bitfield f1 0 protected_bits);
    BF.get_bitfield_set_bitfield_other (U8.v f) 0 protected_bits pb_value protected_bits 8;
    BF.get_bitfield_set_bitfield_other (f0) 0 protected_bits pb_value' protected_bits 8;
    BF.get_bitfield_partition_2 protected_bits (U8.v f) f1;
    assert (f == U8.uint_to_t f1);
    format_header_pn_length h;
    assert ((r.pn_len <: nat) == pn_len);
    assert (pnmask' == and_inplace (S.slice mask 1 (pn_len + 2)) (pn_sizemask_naive pn_len) 0);
    xor_inplace_involutive format pnmask' pn_offset;
    let packet0 = xor_inplace format pnmask' pn_offset in
    pointwise_op_slice_other U8.logxor format pnmask' pn_offset 0 1;
    assert (S.index packet0 0 == S.index (S.slice format 0 1) 0);
    assert (packet == S.cons (U8.uint_to_t f0) (S.slice packet0 1 (S.length packet0)));
    assert (packet1 `S.equal` S.cons (U8.uint_to_t f1) (S.slice packet0 1 (S.length packet0)));
    assert (packet1 `S.equal` packet0);
    assert (r.packet `S.equal` format);
    ()
  end

#pop-options

let lemma_header_encryption_correct a k h cid_len last c =
  lemma_header_encryption_correct_aux a k h cid_len c;
  lemma_header_parsing_correct h c cid_len last

(* not useful anymore by using declassify above

let coerce (#a:Type) (x:a) (b:Type) : Pure b
  (requires a == b) (ensures fun y -> y == x) = x

inline_for_extraction private
let hide (x:bytes) : Pure (S.seq Lib.IntTypes.uint8)
  (requires True) (ensures fun r -> S.length x == S.length r)
  = S.init (S.length x) (fun i -> Lib.IntTypes.secret #Lib.IntTypes.U8 (S.index x i))

inline_for_extraction private
let reveal (x:S.seq Lib.IntTypes.uint8) : Pure bytes
  (requires True) (ensures fun r -> S.length x == S.length r)
  = S.init (S.length x) (fun i -> U8.uint_to_t (Lib.IntTypes.uint_v (S.index x i)))
*)

#pop-options

/// encryption of a packet

let encrypt a k siv hpk h plain =
  let open FStar.Endianness in
  let aad = format_header h in
  let iv =
    if is_retry h
    then siv
    else 
      // packet number bytes
      let pn_len = U32.v (pn_length h) - 1 in
      let seqn = packet_number h in
      let _ = assert_norm(pow2 62 < pow2 (8 `op_Multiply` 12)) in
      let pnb = FStar.Endianness.n_to_be 12 (U64.v seqn) in
      // network packet number: truncated lower bytes
      let npn : lbytes (1+pn_len) = S.slice pnb (11 - pn_len) 12 in
      xor_inplace pnb siv 0
  in
  let cipher = if is_retry h then plain else AEAD.encrypt #a k iv aad plain in
  header_encrypt a hpk h cipher

#push-options "--max_ifuel 1"

let decrypt a k siv hpk last cid_len packet =
  let open FStar.Math.Lemmas in
  let open FStar.Endianness in
  match header_decrypt a hpk cid_len last packet with
  | H_Failure -> Failure
  | H_Success h c rem ->
    if is_retry h
    then Success h c rem
    else
      let aad = format_header h in
      let pn = packet_number h in
      let _ = assert_norm(pow2 62 < pow2 (8 `op_Multiply` 12)) in
      let pnb =
        pow2_lt_compat (8 `op_Multiply` 12) 62;
        n_to_be 12 (U64.v pn)
      in
      let iv = xor_inplace pnb siv 0 in
      match AEAD.decrypt #a k iv aad c with
      | None -> Failure
      | Some plain -> Success h plain rem

/// proving correctness of decryption (link between modulo, and be_to_n
/// + slice last bytes

#push-options "--z3rlimit 16"

let lemma_encrypt_correct a k siv hpk h cid_len last plain =
  let packet = encrypt a k siv hpk h plain in
  let aad = format_header h in
  let iv =
    if is_retry h
    then siv
    else
      // packet number bytes
      let pn_len = U32.v (pn_length h) - 1 in
      let seqn = packet_number h in
      let _ = assert_norm(pow2 62 < pow2 (8 `op_Multiply` 12)) in
      let pnb = FStar.Endianness.n_to_be 12 (U64.v seqn) in
      // network packet number: truncated lower bytes
      let npn : lbytes (1+pn_len) = S.slice pnb (11 - pn_len) 12 in
      xor_inplace pnb siv 0
  in
  let cipher = if is_retry h then plain else AEAD.encrypt #a k iv aad plain in
  assert (packet == header_encrypt a hpk h cipher);
  lemma_header_encryption_correct a hpk h cid_len last cipher;
  if is_retry h
  then ()
  else begin
    let dc = header_decrypt a hpk cid_len last packet in
    assert (H_Success? dc);
    let H_Success h' c' rem' = dc in
    assert (h == h' /\ cipher == c');
    let clen = S.length cipher in
    assert (19 <= clen && clen < max_cipher_length);
    AEAD.correctness #a k iv aad plain
  end

#pop-options

#pop-options
