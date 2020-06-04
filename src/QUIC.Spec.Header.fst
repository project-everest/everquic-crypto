module QUIC.Spec.Header

module PN = QUIC.Spec.PacketNumber
module Secret = QUIC.Secret.Int
module BF = LowParse.BitFields
module U8 = FStar.UInt8
module Seq = QUIC.Secret.Seq
module U64 = FStar.UInt64
module Parse = QUIC.Spec.Header.Parse

module AEAD = Spec.Agile.AEAD
module Cipher = Spec.Agile.Cipher
module Lemmas = QUIC.Spec.Lemmas

let block_of_sample
  (a: Cipher.cipher_alg)
  (k: Cipher.key a)
  (sample: Seq.lseq Secret.uint8 16)
: GTot (Seq.lseq Secret.uint8 16) =
  let open FStar.Mul in
  let ctr, iv = match a with
    | Cipher.CHACHA20 ->
        let ctr_bytes, iv = Seq.split sample 4 in
        FStar.Endianness.lemma_le_to_n_is_bounded (Seq.seq_reveal ctr_bytes);
        assert_norm (pow2 (8 * 4) = pow2 32);
        FStar.Endianness.le_to_n (Seq.seq_reveal ctr_bytes), iv
    | _ ->
        let iv, ctr_bytes = Seq.split sample 12 in
        FStar.Endianness.lemma_be_to_n_is_bounded (Seq.seq_reveal ctr_bytes);
        assert_norm (pow2 (8 * 4) = pow2 32);
        FStar.Endianness.be_to_n (Seq.seq_reveal ctr_bytes), iv
  in
  (Seq.slice (Cipher.ctr_block a k iv ctr) 0 16)

(*
Decryption of packet number
packet[pn_offset..pn_offset+4] ^= pn_mask &
  match pn_len with
  | 0 -> mask & 0xFF000000
  | 1 -> mask & 0xFFFF0000
  | 2 -> mask & 0xFFFFFF00
  | 3 -> mask & 0xFFFFFFFF
*)
let pn_sizemask' (pn_len: nat { pn_len < 4 }) : Tot (lbytes 4) =
  let open FStar.Endianness in
  FStar.Math.Lemmas.pow2_lt_compat 32 (24 - (8 `op_Multiply` pn_len));
  FStar.Endianness.n_to_be 4 (pow2 32 - pow2 (24 - (8 `op_Multiply` pn_len)))

let pn_sizemask (pn_len: nat { pn_len < 4 }) : Tot (lbytes (pn_len + 1)) =
  Seq.slice (pn_sizemask' pn_len) 0 (pn_len + 1)

let header_encrypt
  a hpk h c
=
  assert_norm(max_cipher_length < pow2 62);
  let r = Parse.format_header h `Seq.append` c in
  if is_retry h
  then
    r
  else
    let pn_offset = Parse.pn_offset h in
    let pn_len = Secret.v (pn_length h) - 1 in
    let sample = Seq.seq_hide (Seq.slice c (3-pn_len) (19-pn_len)) in
    let mask = Seq.seq_reveal (block_of_sample (AEAD.cipher_alg_of_supported_alg a) hpk sample) in
    let pnmask = Lemmas.and_inplace (Seq.slice mask 1 (pn_len + 2)) (pn_sizemask pn_len) 0 in
    let f = Seq.index r 0 in
    let protected_bits = if MShort? h then 5 else 4 in
    let f' = BF.set_bitfield (U8.v f) 0 protected_bits (BF.get_bitfield (U8.v f `FStar.UInt.logxor` U8.v (Seq.index mask 0)) 0 protected_bits) in
    let r = Lemmas.xor_inplace r pnmask pn_offset in
    let r = Seq.cons (U8.uint_to_t f') (Seq.slice r 1 (Seq.length r)) in
    r

#push-options "--z3rlimit 256 --query_stats --z3cliopt smt.arith.nl=false"

#restart-solver

let header_encrypt_post
  (a:ea)
  (hpk: Cipher.key (AEAD.cipher_alg_of_supported_alg a))
  (h: header)
  (c: cbytes' (is_retry h))
  (cid_len: nat { cid_len <= 20 /\ (MShort? h ==> cid_len == dcid_len h) })
: Lemma (
    let x = Parse.format_header h in
    let y = x `Seq.append` c in
    let z = header_encrypt a hpk h c in
    Parse.header_len h + Seq.length c == Seq.length z /\
    Seq.slice z (Parse.header_len h) (Seq.length z) `Seq.equal` c /\
    MShort? h == (BF.get_bitfield (U8.v (Seq.index z 0)) 7 8 = 0) /\
    is_retry h == (not (MShort? h) && BF.get_bitfield (U8.v (Seq.index z 0)) 4 6 = 3) /\ (
    if is_retry h
    then z == y
    else Parse.putative_pn_offset cid_len z == Some (Parse.pn_offset h)
  ))
= Parse.format_header_is_short h;
  Parse.format_header_is_retry h;
  if is_retry h
  then ()
  else begin
    Parse.format_header_pn_length h;
    let x = Parse.format_header h in
    let y = x `Seq.append` c in
    let pn_offset = Parse.pn_offset h in
    let pn_len = Secret.v (pn_length h) - 1 in
    let sample = Seq.seq_hide (Seq.slice c (3-pn_len) (19-pn_len)) in
    let mask = Seq.seq_reveal (block_of_sample (AEAD.cipher_alg_of_supported_alg a) hpk sample) in
    let pnmask = Lemmas.and_inplace (Seq.slice mask 1 (pn_len + 2)) (pn_sizemask pn_len) 0 in
    let f = Seq.index y 0 in
    let protected_bits = if MShort? h then 5 else 4 in
    let bf = BF.get_bitfield (U8.v f `FStar.UInt.logxor` U8.v (Seq.index mask 0)) 0 protected_bits in
    let f' = BF.set_bitfield (U8.v f) 0 protected_bits bf in
    let r = Lemmas.xor_inplace y pnmask pn_offset in
    let z = header_encrypt a hpk h c in
    assert (z == Seq.cons (U8.uint_to_t f') (Seq.slice r 1 (Seq.length r)));
    Lemmas.pointwise_op_slice_other U8.logxor y pnmask pn_offset 0 1;
    Lemmas.pointwise_op_slice_other U8.logxor y pnmask pn_offset 1 pn_offset;
    assert (pn_offset > 0);
    Lemmas.pointwise_op_slice_other U8.logxor y pnmask pn_offset (Parse.header_len h) (Seq.length y);
    assert (Seq.slice z (Parse.header_len h) (Seq.length z) `Seq.equal` Seq.slice y (Parse.header_len h) (Seq.length y));
    assert (U8.uint_to_t f' == Seq.index (Seq.slice z 0 1) 0);
    BF.get_bitfield_set_bitfield_other (U8.v f) 0 protected_bits bf 7 8;
    BF.get_bitfield_set_bitfield_other (U8.v f) 0 protected_bits bf protected_bits 8;
    if MLong? h
    then BF.get_bitfield_set_bitfield_other (U8.v f) 0 protected_bits bf 4 6;
    Parse.putative_pn_offset_correct h cid_len;
    Parse.putative_pn_offset_frame cid_len x y;
    Parse.putative_pn_offset_frame cid_len y z;
    ()
  end

#pop-options

let header_encrypt_length
  a hpk h c
=
  header_encrypt_post a hpk h c (dcid_len h)

noextract
type header_decrypt_aux_t = {
  is_short: bool;
  is_retry: (is_retry: bool { is_retry ==> ~ (is_short) });
  packet: packet;
  pn_offset: (if is_retry then unit else nat);
  pn_len: (if is_retry then unit else (pn_len: nat {pn_len < 4 /\ pn_offset + pn_len + 1 <= Seq.length packet}));
}

let header_decrypt_aux
  (a:ea)
  (hpk: Cipher.key (AEAD.cipher_alg_of_supported_alg a))
  (cid_len: nat { cid_len <= 20 })
  (packet: packet)
: GTot (option header_decrypt_aux_t)
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
        is_short = is_short;
        is_retry = is_retry;
        packet = packet;
        pn_offset = ();
        pn_len = ();
      })
    else
      match Parse.putative_pn_offset cid_len packet with
      | None -> None
      | Some pn_offset ->
        let sample_offset = pn_offset + 4 in
        if sample_offset + 16 > Seq.length packet
        then None
        else begin
          let sample = Seq.seq_hide (Seq.slice packet sample_offset (sample_offset+16)) in
          let mask = Seq.seq_reveal (block_of_sample (AEAD.cipher_alg_of_supported_alg a) hpk sample) in
          (* mask the least significant bits of the first byte *)
          let protected_bits = if is_short then 5 else 4 in
          let f' = BF.set_bitfield (U8.v f) 0 protected_bits (BF.get_bitfield (U8.v f `FStar.UInt.logxor` U8.v (Seq.index mask 0)) 0 protected_bits) in
          let packet' = Seq.cons (U8.uint_to_t f') (Seq.slice packet 1 (Seq.length packet)) in
          (* now the packet number length is available, so mask the packet number *)
          let pn_len = BF.get_bitfield f' 0 2 in
          let pnmask = Lemmas.and_inplace (Seq.slice mask 1 (pn_len + 2)) (pn_sizemask pn_len) 0 in
          let packet'' = Lemmas.xor_inplace packet' pnmask pn_offset in
          Some ({
            is_short = is_short;
            is_retry = is_retry;
            packet = packet'';
            pn_offset = pn_offset;
            pn_len = pn_len;
          })
        end

#push-options "--z3rlimit 64 --max_fuel 1"

#restart-solver

let header_decrypt_aux_post
  (a:ea)
  (hpk: Cipher.key (AEAD.cipher_alg_of_supported_alg a))
  (cid_len: nat { cid_len <= 20 })
  (packet: packet)
: Lemma
  (requires (Some? (header_decrypt_aux a hpk cid_len packet)))
  (ensures (
    Some? (header_decrypt_aux a hpk cid_len packet) /\ (
    let Some r = header_decrypt_aux a hpk cid_len packet in
    Seq.length r.packet == Seq.length packet /\
    Seq.length packet > 0 /\ (
    let f' = Seq.index r.packet 0 in
    r.is_short == (BF.get_bitfield (U8.v f') 7 8 = 0) /\
    r.is_retry == (not r.is_short && (BF.get_bitfield (U8.v f') 4 6 = 3)) /\ (
    if r.is_retry
    then r.packet == packet
    else
      Some? (Parse.putative_pn_offset cid_len packet) /\
      Parse.putative_pn_offset cid_len r.packet == Parse.putative_pn_offset cid_len packet /\ (
      let Some pn_offset = Parse.putative_pn_offset cid_len packet in
      r.pn_offset == pn_offset /\
      r.pn_offset + 20 <= Seq.length r.packet /\
      r.pn_len == BF.get_bitfield (U8.v f') 0 2 /\
      r.pn_offset + r.pn_len + 1 <= Seq.length r.packet /\
      Seq.slice r.packet (r.pn_offset + r.pn_len + 1) (Seq.length r.packet) `Seq.equal` Seq.slice packet (r.pn_offset + r.pn_len + 1) (Seq.length packet) /\
      True
  ))))))
=let Some r = header_decrypt_aux a hpk cid_len packet in
  let f = Seq.index packet 0 in
  let is_short = (BF.get_bitfield (U8.v f) 7 8 = 0) in
  let is_retry = not is_short && BF.get_bitfield (U8.v f) 4 6 = 3 in
  if is_retry
  then ()
  else begin
    let Some pn_offset = Parse.putative_pn_offset cid_len packet in
    let sample_offset = pn_offset + 4 in
    let sample = Seq.seq_hide (Seq.slice packet sample_offset (sample_offset+16)) in
    let mask = Seq.seq_reveal (block_of_sample (AEAD.cipher_alg_of_supported_alg a) hpk sample) in
    (* mask the least significant bits of the first byte *)
    let protected_bits = if is_short then 5 else 4 in
    let bf = BF.get_bitfield (U8.v f `FStar.UInt.logxor` U8.v (Seq.index mask 0)) 0 protected_bits in
    let f' = BF.set_bitfield (U8.v f) 0 protected_bits bf in
    let packet' = Seq.cons (U8.uint_to_t f') (Seq.slice packet 1 (Seq.length packet)) in
    (* now the packet number length is available, so mask the packet number *)
    let pn_len = BF.get_bitfield f' 0 2 in
    let pnmask = Lemmas.and_inplace (Seq.slice mask 1 (pn_len + 2)) (pn_sizemask pn_len) 0 in
    assert (r.packet == Lemmas.xor_inplace packet' pnmask pn_offset);
    Lemmas.pointwise_op_slice_other U8.logxor packet' pnmask pn_offset 0 1;
    Lemmas.pointwise_op_slice_other U8.logxor packet' pnmask pn_offset 1 pn_offset;
    Lemmas.pointwise_op_slice_other U8.logxor packet' pnmask pn_offset (pn_offset + pn_len + 1) (Seq.length packet);
    BF.get_bitfield_set_bitfield_other (U8.v f) 0 protected_bits bf protected_bits 8;
    BF.get_bitfield_set_bitfield_other (U8.v f) 0 protected_bits bf 7 8;
    assert (Seq.index r.packet 0 == Seq.index (Seq.slice packet' 0 1) 0);
    Parse.putative_pn_offset_frame cid_len packet r.packet;
    if not is_short
    then BF.get_bitfield_set_bitfield_other (U8.v f) 0 protected_bits bf 4 6;
    assert (Parse.putative_pn_offset cid_len r.packet == Parse.putative_pn_offset cid_len packet);
    ()
  end

#pop-options

#push-options "--z3rlimit 64 --max_fuel 1"

let header_decrypt_aux_post_parse
  (a:ea)
  (hpk: Cipher.key (AEAD.cipher_alg_of_supported_alg a))
  (cid_len: nat { cid_len <= 20 })
  (last: nat { last + 1 < pow2 62 })
  (packet: packet)
: Lemma
  (requires (match header_decrypt_aux a hpk cid_len packet with
    | Some r ->
      Parse.H_Success? (Parse.parse_header cid_len last r.packet)
    | _ -> False
  ))
  (ensures (
    let Some r = header_decrypt_aux a hpk cid_len packet in
    let Parse.H_Success h rem' = Parse.parse_header cid_len last r.packet in
    Parse.header_len h <= Seq.length packet /\
    Seq.length r.packet == Seq.length packet /\
    Seq.length packet > 0 /\ (
    r.is_short == MShort? h /\
    r.is_retry == is_retry h /\
    rem' `Seq.equal` Seq.slice packet (Parse.header_len h) (Seq.length packet) /\ (
    if r.is_retry
    then r.packet == packet
    else
      Some? (Parse.putative_pn_offset cid_len packet) /\ (
      let Some pn_offset = Parse.putative_pn_offset cid_len packet in
      pn_offset == Parse.pn_offset h /\
      r.pn_offset == pn_offset /\
      r.pn_len == Secret.v (pn_length h) - 1 /\
      r.pn_offset + r.pn_len + 1 == Parse.header_len h /\
      Seq.length rem' >= 16
  )))))
= header_decrypt_aux_post a hpk cid_len packet;
  let Some r = header_decrypt_aux a hpk cid_len packet in
  let Parse.H_Success h rem' = Parse.parse_header cid_len last r.packet in
  Parse.lemma_header_parsing_post cid_len last r.packet;
  Parse.format_header_is_short h;
  Parse.format_header_is_retry h;
  assert (r.is_short == MShort? h);
  assert (r.is_retry == is_retry h);
  if r.is_retry
  then
    ()
  else begin
    Parse.format_header_pn_length h;
    let Some pn_offset = Parse.putative_pn_offset cid_len packet in
    Parse.putative_pn_offset_correct h cid_len;
    Parse.putative_pn_offset_frame cid_len (Parse.format_header h) r.packet
  end

#pop-options

let max (a: nat) (b: nat) : Tot (c: nat { c >= a /\ c >= b /\ (c <= a \/ c <= b) }) = if a <= b then b else a
let min (a: nat) (b: nat) : Tot (c: nat { c <= a /\ c <= b /\ (c >= a \/ c >= b) }) = if b <= a then b else a

#push-options "--z3rlimit 256"

#restart-solver

let header_decrypt
  a hpk cid_len last packet
=
  let open FStar.Math.Lemmas in
  if Seq.length packet = 0
  then H_Failure
  else
    match header_decrypt_aux a hpk cid_len packet with
    | None -> H_Failure
    | Some r ->
      let packet'' = r.packet in
      begin match Parse.parse_header cid_len last packet'' with
      | Parse.H_Failure -> H_Failure
      | Parse.H_Success h rem' ->
        header_decrypt_aux_post_parse a hpk cid_len last packet;
        if is_retry h
        then
          H_Success h Seq.empty rem'
        else
          let clen = if has_payload_length h then Secret.v (payload_length h) else Seq.length rem' in
          assert_norm (16 < max_cipher_length - 1);
          (* payload_length is secret, so, to stay constant-time, we
          must not check for failure. Instead, we compute some length
          that might be garbage if bounds on payload_length do not hold. *)
          let clen = max (min (min clen (Seq.length rem')) (max_cipher_length - 1)) 16 in
          assert (clen < max_cipher_length);
          assert (clen <= Seq.length rem');
          assert (16 <= clen);
          let c = Seq.slice rem' 0 clen in
          let rem = Seq.slice rem' clen (Seq.length rem') in
          H_Success h c rem
      end

let lemma_header_encryption_correct_aux
  (a:ea)
  (k: Cipher.key (AEAD.cipher_alg_of_supported_alg a))
  (h:header)
  (cid_len: nat { cid_len <= 20 /\ (MShort? h ==> cid_len == dcid_len h) })
  (c: cbytes' (is_retry h))
: Lemma
  (let r' = header_decrypt_aux a k cid_len (header_encrypt a k h c) in
   Some? r' /\ (
   let Some r = r' in
   r.packet `Seq.equal` (Parse.format_header h `Seq.append` c) /\
   r.is_short == MShort? h /\
   r.is_retry == is_retry h /\
   ((~ (is_retry h)) ==> ((r.pn_offset <: nat) == Parse.pn_offset h /\ r.pn_len == Secret.v (pn_length h) - 1))
  ))
= header_encrypt_post a k h c cid_len;
  header_decrypt_aux_post a k cid_len (header_encrypt a k h c);
  if is_retry h
  then
    ()
  else begin
    let format = Parse.format_header h `Seq.append` c in
    let packet = header_encrypt a k h c in
    let Some r = header_decrypt_aux a k cid_len packet in
    Parse.putative_pn_offset_correct h cid_len;
    let pn_offset = Parse.pn_offset h in
    let pn_len = Secret.v (pn_length h) - 1 in
    let sample' = Seq.slice c (3-pn_len) (19-pn_len) in
    assert (sample' `Seq.equal` Seq.slice packet (pn_offset + 4) (pn_offset + 20));
    let sample = Seq.seq_hide sample' in
    assert ((r.pn_offset <: nat) == pn_offset);
    let mask = Seq.seq_reveal (block_of_sample (AEAD.cipher_alg_of_supported_alg a) k sample) in
    let protected_bits = if MShort? h then 5 else 4 in
    assert (protected_bits == (if r.is_short then 5 else 4));
    let f = Seq.index format 0 in
    let pb_value = BF.get_bitfield (U8.v f `FStar.UInt.logxor` U8.v (Seq.index mask 0)) 0 protected_bits in
    let f0 = BF.set_bitfield (U8.v f) 0 protected_bits pb_value in
    assert (U8.uint_to_t f0 == Seq.index packet 0);
    let pb_value' = BF.get_bitfield (f0 `FStar.UInt.logxor` U8.v (Seq.index mask 0)) 0 protected_bits in
    let f1 = BF.set_bitfield f0 0 protected_bits pb_value' in
    let packet1 = Seq.cons (U8.uint_to_t f1) (Seq.slice packet 1 (Seq.length packet)) in
    let pnmask' = Lemmas.and_inplace (Seq.slice mask 1 (r.pn_len + 2)) (pn_sizemask r.pn_len) 0 in
    assert (r.packet == Lemmas.xor_inplace packet1 pnmask' pn_offset);
    Lemmas.pointwise_op_slice_other U8.logxor packet1 pnmask' pn_offset 0 1;
    assert (Seq.index r.packet 0 == Seq.index (Seq.slice r.packet 0 1) 0);
    assert (Seq.index r.packet 0 == U8.uint_to_t f1);
    BF.get_bitfield_logxor (U8.v f) (U8.v (Seq.index mask 0)) 0 protected_bits;
    BF.get_bitfield_set_bitfield_same (U8.v f) 0 protected_bits pb_value;
    BF.get_bitfield_logxor (f0) (U8.v (Seq.index mask 0)) 0 protected_bits;
    BF.get_bitfield_set_bitfield_same (f0) 0 protected_bits pb_value';
    FStar.UInt.logxor_inv (BF.get_bitfield (U8.v f) 0 protected_bits) (BF.get_bitfield (U8.v (Seq.index mask 0)) 0 protected_bits);
    assert (BF.get_bitfield (U8.v f) 0 protected_bits == BF.get_bitfield f1 0 protected_bits);
    BF.get_bitfield_set_bitfield_other (U8.v f) 0 protected_bits pb_value protected_bits 8;
    BF.get_bitfield_set_bitfield_other (f0) 0 protected_bits pb_value' protected_bits 8;
    BF.get_bitfield_partition_2 protected_bits (U8.v f) f1;
    assert (f == U8.uint_to_t f1);
    Parse.format_header_pn_length h;
    assert ((r.pn_len <: nat) == pn_len);
    assert (pnmask' == Lemmas.and_inplace (Seq.slice mask 1 (pn_len + 2)) (pn_sizemask pn_len) 0);
    Lemmas.xor_inplace_involutive format pnmask' pn_offset;
    let packet0 = Lemmas.xor_inplace format pnmask' pn_offset in
    Lemmas.pointwise_op_slice_other U8.logxor format pnmask' pn_offset 0 1;
    assert (Seq.index packet0 0 == Seq.index (Seq.slice format 0 1) 0);
    assert (packet == Seq.cons (U8.uint_to_t f0) (Seq.slice packet0 1 (Seq.length packet0)));
    assert (packet1 `Seq.equal` Seq.cons (U8.uint_to_t f1) (Seq.slice packet0 1 (Seq.length packet0)));
    assert (packet1 `Seq.equal` packet0);
    assert (r.packet `Seq.equal` format);
    ()
  end

let lemma_header_encryption_correct
  a k h cid_len last c
=
 lemma_header_encryption_correct_aux a k h cid_len c;
 Parse.lemma_header_parsing_correct h c cid_len last

#pop-options
