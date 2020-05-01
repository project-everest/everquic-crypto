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

#push-options "--z3rlimit 128"

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

#push-options "--z3rlimit 32 --max_fuel 1"

let header_decrypt_aux_post
  (a:ea)
  (hpk: Cipher.key (AEAD.cipher_alg_of_supported_alg a))
  (cid_len: nat { cid_len <= 20 })
  (packet: packet)
: Lemma
  (requires (Some? (header_decrypt_aux a hpk cid_len packet)))
  (ensures (
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
      r.pn_len == BF.get_bitfield (U8.v f') 0 2 /\
      Seq.slice r.packet (r.pn_offset + r.pn_len + 1) (Seq.length r.packet) `Seq.equal` Seq.slice packet (r.pn_offset + r.pn_len + 1) (Seq.length packet) /\
      True
  )))))
= let Some r = header_decrypt_aux a hpk cid_len packet in
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
      r.pn_len == Secret.v (pn_length h) - 1 /\
      r.pn_offset + r.pn_len + 1 == Parse.header_len h /\
      True
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

#push-options "--z3rlimit 128"

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
        else if has_payload_length h && Seq.length rem' < Secret.v (payload_length h)
        then H_Failure
        else
          let clen = if has_payload_length h then Secret.v (payload_length h) else Seq.length rem' in
          if 19 <= clen && clen < max_cipher_length
          then
            let c : cbytes = Seq.slice rem' 0 clen in
            let rem = Seq.slice rem' clen (Seq.length rem') in
            H_Success h c rem
          else
            H_Failure
      end

let lemma_header_encryption_correct_aux
  (a:ea)
  (k: Cipher.key (AEAD.cipher_alg_of_supported_alg a))
  (h:header)
  (cid_len: nat { cid_len <= 20 /\ (MShort? h ==> cid_len == dcid_len h) })
  (c: cbytes' (is_retry h)) // { has_payload_length h ==> U64.v (payload_length h) == Seq.length c } ->
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

#pop-options

let lemma_header_encryption_correct
  a k h cid_len last c
=
  lemma_header_encryption_correct_aux a k h cid_len c;
  Parse.lemma_header_parsing_correct h c cid_len last



(*
let parse_header
  cid_len last b
= match LP.parse (lp_parse_header (U32.uint_to_t cid_len) (Secret.to_u64 (U64.uint_to_t last))) b with
  | None -> H_Failure
  | Some (h, consumed) -> H_Success h (Seq.slice b consumed (Seq.length b))

#push-options "--z3rlimit 16"

let parse_header_post
  cid_len last b
= ()

#pop-options

#push-options "--z3rlimit 16"

let format_header_bound
  (h: header)
: Lemma
  (let len = Seq.length (format_header h) in
  len > 0 /\
  len < header_len_bound)
= LP.serialize_length (serialize_header (U32.uint_to_t (dcid_len h)) (last_packet_number h)) h

let lemma_header_parsing_correct
  h c cid_len last
=
  let s = format_header h in
  in_window_last_packet_number h;
  FStar.Math.Lemmas.pow2_le_compat 64 62;
  let cid_len' = (U32.uint_to_t cid_len) in
  let last' = (Secret.to_u64 (U64.uint_to_t last)) in
  serialize_header_ext (U32.uint_to_t (dcid_len h)) cid_len' (last_packet_number h) last' h;
//  assert (s == LP.serialize (serialize_header cid_len' last') h);
  LP.parse_serialize (serialize_header cid_len' last') h;
  LP.parse_strong_prefix (lp_parse_header cid_len' last') s (s `Seq.append` c);
//  assert (LP.parse (lp_parse_header cid_len' last') (s `Seq.append` c) == Some (h, Seq.length s));
  assert (c `Seq.equal` Seq.slice (s `Seq.append` c) (Seq.length s) (Seq.length (s `Seq.append` c)))

let lemma_header_parsing_safe
  cid_len last b1 b2
=
  let cid_len' = (U32.uint_to_t cid_len) in
  let last' = (Secret.to_u64 (U64.uint_to_t last)) in
  match LP.parse (lp_parse_header cid_len' last') b1 with
  | None -> ()
  | Some (h, consumed) ->
    LP.parse_injective (lp_parse_header cid_len' last') b1 b2;
    Seq.lemma_split b1 consumed;
    Seq.lemma_split b2 consumed

#pop-options

#push-options "--z3rlimit 16"

let header_decrypt_only
  (a:ea)
  (hpk: Cipher.key (AEAD.cipher_alg_of_supported_alg a))
  (cid_len: nat { cid_len <= 20 })
  (last: nat { last + 1 < pow2 62 })
  (p: packet)
: GTot (option (lbytes (Seq.length p)))
=
  let cid_len' = (U32.uint_to_t cid_len) in
  let last' = (Secret.to_u64 (U64.uint_to_t last)) in
  match LP.parse (Public.parse_header cid_len') p with
  | None -> None
  | Some (ph, consumed) ->
    if Public.is_retry ph
    then Some p
    else
      let sample_offset = consumed + 4 in
      if sample_offset + 16 > Seq.length p
      then (* not enough space for sampling *) None
      else
        let sample = Seq.slice p sample_offset (sample_offset + 16) in
        let mask = block_of_sample (AEAD.cipher_alg_of_supported_alg a) hpk sample in
        let protected_bits = if Public.PShort? ph then 5 else 4 in
        let f = Seq.index p 0 in
        let f' = BF.set_bitfield (U8.v f) 0 protected_bits (BF.get_bitfield (U8.v (f `U8.logxor` Seq.index mask 0)) 0 protected_bits) in
        let packet1 = Seq.upd p 0 (U8.uint_to_t f') in
        (* now the packet number length is available, so mask the packet number *)
        let pn_len = BF.get_bitfield f' 0 2 in
        let pnmask = Lemmas.and_inplace (Seq.slice mask 1 (pn_len + 2)) (pn_sizemask pn_len) 0 in
        let packet2 = Lemmas.xor_inplace packet1 pnmask consumed in
        Some packet2

#pop-options

#push-options "--z3rlimit 16"

let header_decrypt
  a hpk cid_len last p
= match header_decrypt_only a hpk cid_len last p with
  | None -> HD_Failure
  | Some p' ->
    begin match parse_header cid_len last p' with
    | H_Failure -> HD_Failure
    | H_Success h c ->
      if is_retry h
      then HD_Success h Seq.empty c
      else
        let clen : nat = if has_payload_length h then Secret.v (payload_length h) else Seq.length c in
        if 19 <= clen && clen < max_cipher_length && clen <= Seq.length c
        then
          let c' : cbytes = Seq.slice c 0 clen in
          let rem = Seq.slice c clen (Seq.length c) in
          HD_Success h c' rem
        else
          HD_Failure
    end

let pn_offset
  (h: header)
: GTot nat
= let cid_len = U32.uint_to_t (dcid_len h) in
  let last = last_packet_number h in
  let (| ph, _ |) = synth_header_recip cid_len last h in
  Seq.length (LP.serialize (Public.serialize_header cid_len) ph)

let pn_offset_prop
  (h: header)
: Lemma
  (requires (~ (is_retry h)))
  (ensures (
    pn_offset h + Secret.v (pn_length h) == Seq.length (format_header h)
  ))
=
  let cid_len = U32.uint_to_t (dcid_len h) in
  let last = last_packet_number h in
  serialize_header_eq cid_len last h;
  let pn_len = pn_length h in
  PN.parse_packet_number_kind'_correct last pn_len;
  let (| _, pn |) = synth_header_recip cid_len last h in
  LP.serialize_length #(PN.parse_packet_number_kind' pn_len) #_ #(PN.parse_packet_number last pn_len <: LP.bare_parser (PN.packet_number_t' last pn_len)) (PN.serialize_packet_number last pn_len <: LP.bare_serializer (PN.packet_number_t' last pn_len)) pn

assume
val header_decrypt_only_correct
  (a:ea)
  (k: Cipher.key (AEAD.cipher_alg_of_supported_alg a))
  (h:header)
  (cid_len: nat { cid_len <= 20 /\ (MShort? h ==> cid_len == dcid_len h) })
  (last: nat { last + 1 < pow2 62 /\ ((~ (is_retry h)) ==> PN.in_window (Secret.v (pn_length h) - 1) last (Secret.v (packet_number h))) })
  (c: cbytes)
  (rem: bytes {
    Seq.length (format_header h) + Seq.length c + Seq.length rem < pow2 32
  })
: Lemma
  (
    let from = header_encrypt a k h c `Seq.append` rem in
    let to = format_header h `Seq.append` (c `Seq.append` rem) in
    Seq.length from == Seq.length to /\
    header_decrypt_only a k cid_len last from == Some to
  )

let seq_slice_append
  (#t: Type)
  (c rem: Seq.seq t)
: Lemma
  (Seq.slice (c `Seq.append` rem) 0 (Seq.length c) `Seq.equal` c /\
   Seq.slice (c `Seq.append` rem) (Seq.length c) (Seq.length c + Seq.length rem) `Seq.equal` rem
  )
= ()

let seq_slice_full
  (#t: Type)
  (c: Seq.seq t)
: Lemma
  (Seq.slice c 0 (Seq.length c) `Seq.equal` c)
= ()

#pop-options

#push-options "--z3rlimit 128"

#restart-solver

let lemma_header_encryption_correct
  a k h cid_len last c rem
= header_decrypt_only_correct a k h cid_len last c rem;
  lemma_header_parsing_correct h (c `Seq.append` rem) cid_len last;
  if is_retry h
  then ()
  else begin
    let lcrem = Seq.length c + Seq.length rem in
    let clen : nat = if has_payload_length h then Secret.v (payload_length h) else lcrem in
    assert (19 <= clen && clen < max_cipher_length && clen <= lcrem);
    let c' : cbytes = Seq.slice (c `Seq.append` rem) 0 clen in
    let rem' = Seq.slice (c `Seq.append` rem) clen (lcrem) in
    Seq.append_empty_l rem;
    if has_payload_length h
    then begin
      assert (Seq.length c == Secret.v (payload_length h));
      seq_slice_append c rem
    end else begin
      assert (rem == Seq.empty);
      Seq.append_empty_r c;
      seq_slice_full c;
      assert (c' == c);
      assert (rem' `Seq.equal` Seq.empty)
    end
  end

#pop-options

(*

(*
let header_decrypt
  a hpk cid_len last p
=


(*
let parse_header_ifthenelse_payload
  (has_pn: bool)
: Tot Type0
= if has_pn
  then PN.packet_number_t
  else unit

let parse_header_ifthenelse_payload_parser
  (last: PN.last_packet_number_t)
  (has_pn: bool)
: Tot (k: LP.parser_kind & LP.parser k (parse_header_ifthenelse_payload has_pn))
= if has_pn
  then (| _, PN.parse_packet_number last 


let parse_header_param
  (cid_len: short_dcid_len_t)
  (last: PN.last_packet_number_t)
: Tot LP.parse_ifthenelse_param
= {
  LP.parse_ifthenelse_tag_kind = Public.parse_header_kind' cid_len;
  LP.parse_ifthenelse_tag_t = Public.header' cid_len;
  LP.parse_ifthenelse_tag_parser = Public.parse_header cid_len;
  LP.parse_ifthenelse_tag_cond = public_header_has_pn cid_len;
  LP.parse_ifthenelse_payload_t = 
}


(*
open QUIC.Spec.PacketNumber

open LowParse.Spec.Int
open LowParse.Spec.BitSum

open LowParse.Spec.BoundedInt

module U64 = FStar.UInt64
module U32 = FStar.UInt32
module U16 = FStar.UInt16
module U8 = FStar.UInt8

(* From https://tools.ietf.org/html/draft-ietf-quic-transport-23#section-17 *)


inline_for_extraction
type header_form_t =
  | Long
  | Short

[@filter_bitsum'_t_attr]
inline_for_extraction
noextract
let header_form : enum header_form_t (bitfield uint8 1) = [
  Long, 1uy;
  Short, 0uy;
]

[@filter_bitsum'_t_attr]
inline_for_extraction
noextract
let fixed_bit : enum unit (bitfield uint8 1) = [
  (), 1uy;
]

inline_for_extraction
type long_packet_type_t =
  | Initial
  | ZeroRTT
  | Handshake
  | Retry

[@filter_bitsum'_t_attr]
inline_for_extraction
noextract
let long_packet_type : enum long_packet_type_t (bitfield uint8 2) = [
  Initial, 0uy;
  ZeroRTT, 1uy;
  Handshake, 2uy;
  Retry, 3uy;
]

[@filter_bitsum'_t_attr]
inline_for_extraction
noextract
let reserved_bits : enum unit (bitfield uint8 2) = [
  (), 0uy;
]

[@filter_bitsum'_t_attr]
inline_for_extraction
noextract
let packet_number_length : enum packet_number_length_t (bitfield uint8 2) = [
  1ul, 0uy;
  2ul, 1uy;
  3ul, 2uy;
  4ul, 3uy;
]

[@filter_bitsum'_t_attr]
inline_for_extraction
noextract
let rrpp : bitsum' uint8 4 =
  BitSum' _ _ reserved_bits (fun _ -> BitSum' _ _ packet_number_length (fun _ -> BitStop ()))

[@filter_bitsum'_t_attr]
inline_for_extraction
noextract
let first_byte : bitsum' uint8 8 =
  BitSum' _ _ header_form (function
    | Short ->
      BitSum' _ _ fixed_bit (fun _ ->
        BitField (* spin bit *) 1 (
          BitSum' _ _ reserved_bits (fun _ ->
            BitField (* key phase *) 1 (
              BitSum' _ _ packet_number_length (fun _ ->
                BitStop ()
              )
            )
          )
        )
      )
    | Long ->
      BitSum' _ _ fixed_bit (fun _ ->
        BitSum' _ _ long_packet_type (function
          | Retry -> BitField (* unused *) 4 (BitStop ())
          | _ -> rrpp
        )
      )
  )

(*
// How to test normalization:
module T = FStar.Tactics
let f (x: FStar.UInt8.t) : Tot unit =
  assert (filter_header_byte x == true) by (
    T.norm [primops; iota; zeta; delta_attr [`%filter_bitsum'_t_attr]];
    T.fail "abc"
  )
*)

module FB = FStar.Bytes
open LowParse.Spec.Bytes

inline_for_extraction
let short_dcid_len_t = (short_dcid_len: U32.t { U32.v short_dcid_len <= 20 })

let short_dcid_len_prop
  (short_dcid_len: short_dcid_len_t)
  (h: header)
: GTot Type0
= (MShort? h ==> dcid_len h == U32.v short_dcid_len)


#push-options "--z3rlimit 16"

inline_for_extraction
noextract
let first_byte_of_header'
  (short_dcid_len: short_dcid_len_t)
  (last: last_packet_number_t)
  (t: Type0)
  (f: (bitsum'_type first_byte -> Tot t))
  (m: header' short_dcid_len last)
: Tot t
= match m with
  | MShort spin key_phase dcid pn_length packet_number ->
    let spin : bitfield uint8 1 = if spin then 1uy else 0uy in
    let key_phase : bitfield uint8 1 = if key_phase then 1uy else 0uy in
    f (| Short, (| (), (spin, (| (), (key_phase, (| pn_length, () |) ) |) ) |) |)
  | MLong version dcid scid spec ->
    begin match spec with
    | MInitial _ payload_length pn_length _ ->
      f (| Long, (| (), (| Initial, (| (), (| pn_length, () |) |) |) |) |)
    | MZeroRTT payload_length pn_length _ ->
      f (| Long, (| (), (| ZeroRTT, (| (), (| pn_length, () |) |) |) |) |)
    | MHandshake payload_length pn_length _ ->
      f (| Long, (| (), (| Handshake, (| (), (| pn_length, () |) |) |) |) |)
    | MRetry unused _ ->
      f (| Long, (| (), (| Retry, (unused, ()) |) |) |)
    end

#pop-options

let first_byte_of_header
  (short_dcid_len: short_dcid_len_t)
  (last: last_packet_number_t)
  (m: header' short_dcid_len last)
: Tot (bitsum'_type first_byte)
= first_byte_of_header' short_dcid_len last (bitsum'_type first_byte) id m

[@filter_bitsum'_t_attr]
inline_for_extraction
noextract
let common_long_t
: Type0
= (U32.t & (parse_bounded_vlbytes_t 0 20 & parse_bounded_vlbytes_t 0 20))

module Cast = FStar.Int.Cast

inline_for_extraction
let payload_and_pn_length_prop
  (pn_length: packet_number_length_t)
  (payload_and_pn_len: uint62_t)
: Tot bool
= payload_and_pn_len `U64.gte` Cast.uint32_to_uint64 pn_length

[@filter_bitsum'_t_attr]
inline_for_extraction
noextract
let payload_length_pn
  (last: last_packet_number_t)
  (pn_length: packet_number_length_t)
: Tot Type0
= (parse_filter_refine (payload_and_pn_length_prop pn_length) & packet_number_t last pn_length)

#push-options "--z3rlimit 16 --max_fuel 8 --max_ifuel 8 --initial_fuel 8 --initial_ifuel 8"

[@filter_bitsum'_t_attr]
inline_for_extraction
noextract
let header_body_type
  (short_dcid_len: short_dcid_len_t)
  (last: last_packet_number_t)
  (k' : bitsum'_key_type first_byte)
: Tot Type0
= match k' with
  | (| Short, (| (), (| (), (| pn_length, () |) |) |) |) ->
    (FB.lbytes (U32.v short_dcid_len) & packet_number_t last pn_length)
  | (| Long, (| (), (| Initial, (| (), (| pn_length, () |) |) |) |) |) ->
    (common_long_t & (parse_bounded_vlbytes_t 0 token_max_len & payload_length_pn last pn_length))
  | (| Long, (| (), (| ZeroRTT, (| (), (| pn_length, () |) |) |) |) |) ->
    (common_long_t & payload_length_pn last pn_length)
  | (| Long, (| (), (| Handshake, (| (), (| pn_length, () |) |) |) |) |) ->
    (common_long_t & payload_length_pn last pn_length)
  | (| Long, (| (), (| Retry, () |) |) |) ->
    (common_long_t & parse_bounded_vlbytes_t 0 20)

open LowParse.Spec.BitSum // again, for coerce

#pop-options

#push-options "--z3rlimit 64 --max_fuel 8 --max_ifuel 8 --initial_fuel 8 --initial_ifuel 8"

[@filter_bitsum'_t_attr]
inline_for_extraction
noextract
let mk_header
  (short_dcid_len: short_dcid_len_t)
  (last: last_packet_number_t)
  (k' : bitsum'_type first_byte)
  (pl: header_body_type short_dcid_len last (bitsum'_key_of_t first_byte k'))
: Tot (refine_with_tag (first_byte_of_header short_dcid_len last) k')
= match k' with
  | (| Short, (| (), (spin, (| (), (key_phase, (| pn_length, () |) ) |) ) |) |) ->
    let spin = (spin = 1uy) in
    let key_phase = (key_phase = 1uy) in
    begin match coerce (FB.lbytes (U32.v short_dcid_len) & packet_number_t last pn_length) pl with
    | (dcid, packet_number) ->
      MShort spin key_phase dcid pn_length packet_number
    end
  | (| Long, (| (), (| Initial, (| (), (| pn_length, () |) |) |) |) |) ->
    begin match coerce (common_long_t & (parse_bounded_vlbytes_t 0 token_max_len & payload_length_pn last pn_length)) pl with
    | ((version, (dcid, scid)), (token, (payload_and_pn_length, packet_number))) ->
      MLong version dcid scid (MInitial token (payload_and_pn_length `U64.sub` Cast.uint32_to_uint64 pn_length) pn_length packet_number)
    end
  | (| Long, (| (), (| ZeroRTT, (| (), (| pn_length, () |) |) |) |) |) ->
    begin match coerce (common_long_t & payload_length_pn last pn_length) pl with
    | ((version, (dcid, scid)), (payload_and_pn_length, packet_number)) ->
      MLong version dcid scid (MZeroRTT (payload_and_pn_length `U64.sub` Cast.uint32_to_uint64 pn_length) pn_length packet_number)
    end
  | (| Long, (| (), (| Handshake, (| (), (| pn_length, () |) |) |) |) |) ->
    begin match coerce (common_long_t & payload_length_pn last pn_length) pl with
    | ((version, (dcid, scid)), (payload_and_pn_length, packet_number)) ->
      MLong version dcid scid (MHandshake (payload_and_pn_length `U64.sub` Cast.uint32_to_uint64 pn_length) pn_length packet_number)
    end
  | (| Long, (| (), (| Retry, (unused, ()) |) |) |) ->
    begin match coerce (common_long_t & parse_bounded_vlbytes_t 0 20) pl with
    | ((version, (dcid, scid)), odcid) ->
      MLong version dcid scid (MRetry unused odcid)
    end

[@filter_bitsum'_t_attr]
inline_for_extraction
noextract
let mk_header_body
  (short_dcid_len: short_dcid_len_t)
  (last: last_packet_number_t)
  (k' : bitsum'_type first_byte)
  (pl: refine_with_tag (first_byte_of_header short_dcid_len last) k')
: Tot (header_body_type short_dcid_len last (bitsum'_key_of_t first_byte k'))
= match k' with
  | (| Short, (| (), (spin, (| (), (key_phase, (| pn_length, () |) ) |) ) |) |) ->
    begin match pl with
    | MShort _ _ dcid _ pn -> coerce (header_body_type short_dcid_len last (bitsum'_key_of_t first_byte k')) ((dcid, pn) <: (FB.lbytes (U32.v short_dcid_len) & packet_number_t last pn_length ))
    end
  | (| Long, (| (), (| Initial, (| (), (| pn_length, () |) |) |) |) |) ->
    begin match pl with
    | MLong version dcid scid (MInitial token payload_length _ packet_number) ->
      coerce (header_body_type short_dcid_len last (bitsum'_key_of_t first_byte k')) (((version, (dcid, scid)), (token, (payload_length `U64.add` Cast.uint32_to_uint64 pn_length, packet_number))) <: (common_long_t & (parse_bounded_vlbytes_t 0 token_max_len & payload_length_pn last pn_length)))
    end
  | (| Long, (| (), (| ZeroRTT, (| (), (| pn_length, () |) |) |) |) |) ->
    begin match pl with
    | MLong version dcid scid (MZeroRTT payload_length _ packet_number) ->
      coerce (header_body_type short_dcid_len last (bitsum'_key_of_t first_byte k')) (((version, (dcid, scid)), (payload_length `U64.add` Cast.uint32_to_uint64 pn_length, packet_number)) <: (common_long_t & payload_length_pn last pn_length))
    end
  | (| Long, (| (), (| Handshake, (| (), (| pn_length, () |) |) |) |) |) ->
    begin match pl with
    | MLong version dcid scid (MHandshake payload_length _ packet_number) ->
      coerce (header_body_type short_dcid_len last (bitsum'_key_of_t first_byte k')) (((version, (dcid, scid)), (payload_length `U64.add` Cast.uint32_to_uint64 pn_length, packet_number)) <: (common_long_t & payload_length_pn last pn_length))
    end
  | (| Long, (| (), (| Retry, (unused, ()) |) |) |) ->
    begin match pl with
    | MLong version dcid scid (MRetry unused odcid) ->
      coerce (header_body_type short_dcid_len last (bitsum'_key_of_t first_byte k')) (((version, (dcid, scid)), odcid) <: (common_long_t & parse_bounded_vlbytes_t 0 20))
    end

#pop-options

#push-options "--z3rlimit 128 --max_fuel 8 --max_ifuel 8 --initial_fuel 8 --initial_ifuel 8"

[@filter_bitsum'_t_attr]
inline_for_extraction
noextract
let header_synth
  (short_dcid_len: short_dcid_len_t)
  (last: last_packet_number_t)
: Tot (synth_case_t first_byte (header' short_dcid_len last) (first_byte_of_header short_dcid_len last) (header_body_type short_dcid_len last))
= 
  (SynthCase
    #_ #_ #_ #first_byte #_ #(first_byte_of_header short_dcid_len last) #(header_body_type short_dcid_len last)
    (mk_header short_dcid_len last)
    (fun k x y -> ())
    (mk_header_body short_dcid_len last)
    (fun k x -> ())
  )

#pop-options

let parse_common_long : parser _ common_long_t =
  parse_u32 `nondep_then` (parse_bounded_vlbytes 0 20 `nondep_then` parse_bounded_vlbytes 0 20)

open QUIC.Spec.VarInt

let parse_payload_length_pn
  (last: last_packet_number_t)
  (pn_length: packet_number_length_t)
: Tot (parser _ (payload_length_pn last pn_length))
= (parse_varint `parse_filter` payload_and_pn_length_prop pn_length) `nondep_then` parse_packet_number last pn_length

#push-options "--z3rlimit 64 --max_fuel 8 --max_ifuel 8 --initial_fuel 8 --initial_ifuel 8"

[@filter_bitsum'_t_attr]
inline_for_extraction
noextract
let parse_header_body
  (short_dcid_len: short_dcid_len_t)
  (last: last_packet_number_t)
  (k' : bitsum'_key_type first_byte)
: Tot (k: parser_kind & parser k (header_body_type short_dcid_len last k'))
= match coerce (bitsum'_key_type first_byte) k' with
  | (| Short, (| (), (| (), (| pn_length, () |) |) |) |) ->
    (| _, weaken (strong_parser_kind 0 20 None) (parse_flbytes (U32.v short_dcid_len)) `nondep_then` parse_packet_number last pn_length |)
  | (| Long, (| (), (| Initial, (| (), (| pn_length, () |) |) |) |) |) ->
    (| _, parse_common_long `nondep_then` (parse_bounded_vlgenbytes 0 token_max_len (parse_bounded_varint 0 token_max_len) `nondep_then` parse_payload_length_pn last pn_length) |)
  | (| Long, (| (), (| ZeroRTT, (| (), (| pn_length, () |) |) |) |) |) ->
    (| _, parse_common_long `nondep_then` parse_payload_length_pn last pn_length |)
  | (| Long, (| (), (| Handshake, (| (), (| pn_length, () |) |) |) |) |) ->
    (| _, parse_common_long `nondep_then` parse_payload_length_pn last pn_length |)
  | (| Long, (| (), (| Retry, () |) |) |) ->
    (| _, parse_common_long `nondep_then` parse_bounded_vlbytes 0 20 |)

#pop-options

[@filter_bitsum'_t_attr]
inline_for_extraction
noextract
let parse_header_kind'
  (short_dcid_len: short_dcid_len_t)
  (last: last_packet_number_t)
: Tot parser_kind
= parse_bitsum_kind parse_u8_kind first_byte (header_body_type short_dcid_len last) (parse_header_body short_dcid_len last)

let lp_parse_header
  (short_dcid_len: short_dcid_len_t)
  (last: last_packet_number_t)
: Tot (parser (parse_header_kind' short_dcid_len last) (header' short_dcid_len last))
= parse_bitsum
    first_byte
    (first_byte_of_header short_dcid_len last)
    (header_body_type short_dcid_len last)
    (header_synth short_dcid_len last)
    parse_u8
    (parse_header_body short_dcid_len last)

let serialize_common_long : serializer parse_common_long =
  serialize_u32 `serialize_nondep_then` (serialize_bounded_vlbytes 0 20 `serialize_nondep_then` serialize_bounded_vlbytes 0 20)

let serialize_payload_length_pn
  (last: last_packet_number_t)
  (pn_length: packet_number_length_t)
: Tot (serializer (parse_payload_length_pn last pn_length))
= (serialize_varint `serialize_filter` payload_and_pn_length_prop pn_length) `serialize_nondep_then` serialize_packet_number last pn_length

#push-options "--z3rlimit 64 --max_fuel 8 --max_ifuel 8 --initial_fuel 8 --initial_ifuel 8"

let serialize_header_body
  (short_dcid_len: short_dcid_len_t)
  (last: last_packet_number_t)
  (k' : bitsum'_key_type first_byte)
: Tot (serializer (dsnd (parse_header_body short_dcid_len last k')))
= match coerce (bitsum'_key_type first_byte) k' with
  | (| Short, (| (), (| (), (| pn_length, () |) |) |) |) ->
    serialize_weaken (strong_parser_kind 0 20 None) (serialize_flbytes (U32.v short_dcid_len)) `serialize_nondep_then` serialize_packet_number last pn_length
  | (| Long, (| (), (| Initial, (| (), (| pn_length, () |) |) |) |) |) ->
    serialize_common_long `serialize_nondep_then` (serialize_bounded_vlgenbytes 0 token_max_len (serialize_bounded_varint 0 token_max_len) `serialize_nondep_then` serialize_payload_length_pn last pn_length)
  | (| Long, (| (), (| ZeroRTT, (| (), (| pn_length, () |) |) |) |) |) ->
    serialize_common_long `serialize_nondep_then` serialize_payload_length_pn last pn_length
  | (| Long, (| (), (| Handshake, (| (), (| pn_length, () |) |) |) |) |) ->
    serialize_common_long `serialize_nondep_then` serialize_payload_length_pn last pn_length
  | (| Long, (| (), (| Retry, () |) |) |) ->
    serialize_common_long `serialize_nondep_then` serialize_bounded_vlbytes 0 20

#pop-options

let serialize_header
  (short_dcid_len: short_dcid_len_t)
  (last: last_packet_number_t)
: Tot (serializer (lp_parse_header short_dcid_len last))
= serialize_bitsum
    #parse_u8_kind
    #8
    #U8.t
    first_byte
    #(header' short_dcid_len last)
    (first_byte_of_header short_dcid_len last)
    (header_body_type short_dcid_len last)
    (header_synth short_dcid_len last)
    #parse_u8
    serialize_u8
    #(parse_header_body short_dcid_len last)
    (serialize_header_body short_dcid_len last)

let serialize_header_alt
  (short_dcid_len: short_dcid_len_t)
  (last: last_packet_number_t)
  (x: header' short_dcid_len last)
: GTot bytes
= serialize_bitsum_alt
    #parse_u8_kind
    #8
    #U8.t
    first_byte
    #(header' short_dcid_len last)
    (first_byte_of_header short_dcid_len last)
    (header_body_type short_dcid_len last)
    (header_synth short_dcid_len last)
    #parse_u8
    serialize_u8
    #(parse_header_body short_dcid_len last)
    (serialize_header_body short_dcid_len last)
    x

let serialize_header_eq
  (short_dcid_len: short_dcid_len_t)
  (last: last_packet_number_t)
  (x: header' short_dcid_len last)
: Lemma
  (serialize (serialize_header short_dcid_len last) x == serialize_header_alt short_dcid_len last x)
= serialize_bitsum_eq'
    #parse_u8_kind
    #8
    #U8.t
    first_byte
    #(header' short_dcid_len last)
    (first_byte_of_header short_dcid_len last)
    (header_body_type short_dcid_len last)
    (header_synth short_dcid_len last)
    #parse_u8
    serialize_u8
    #(parse_header_body short_dcid_len last)
    (serialize_header_body short_dcid_len last)
    x

module LC = LowParse.Spec.Combinators
module LB = LowParse.Spec.Bytes
module LI = LowParse.Spec.BoundedInt
module LJ = LowParse.Spec.Int
module LL = LowParse.Spec.BitSum

(* Properties of the serializer *)

#push-options "--z3rlimit 128 --max_fuel 4 --initial_fuel 4"

let serialize_header_ext
  (cid_len1 cid_len2: short_dcid_len_t)
  (last1 last2: last_packet_number_t)
  (x: header)
: Lemma
  (requires (
    parse_header_prop cid_len1 last1 x /\
    parse_header_prop cid_len2 last2 x
  ))
  (ensures (
    serialize (serialize_header cid_len1 last1) x == serialize (serialize_header cid_len2 last2) x
  ))
= serialize_header_eq cid_len1 last1 x;
  serialize_header_eq cid_len2 last2 x;
  let tg = first_byte_of_header cid_len1 last1 x in
  assert (tg == first_byte_of_header cid_len2 last2 x);
  match x with
  | MShort spin key_phase dcid pn_length packet_number ->
    assert_norm (first_byte_of_header cid_len1 last1 (MShort spin key_phase dcid pn_length packet_number) == (| Short, (| (), ((if spin then 1uy else 0uy), (| (), ((if key_phase then 1uy else 0uy), (| pn_length, () |) ) |) ) |) |) );
    assert_norm (bitsum'_key_of_t first_byte (first_byte_of_header cid_len1 last1 (MShort spin key_phase dcid pn_length packet_number)) == (| Short, (| (), (| (), (| pn_length, () |) |) |) |) );
    assert (cid_len1 == cid_len2);
    serialize_nondep_then_eq (serialize_weaken (strong_parser_kind 0 20 None) (serialize_flbytes (U32.v cid_len1))) (serialize_packet_number last1 pn_length) (dcid, packet_number);
    serialize_nondep_then_eq (serialize_weaken (strong_parser_kind 0 20 None) (serialize_flbytes (U32.v cid_len2))) (serialize_packet_number last2 pn_length) (dcid, packet_number);
    serialize_packet_number_ext last1 last2 pn_length packet_number
  | MLong version dcid scid spec ->
    begin match spec with
    | MInitial token payload_length packet_number_length packet_number ->
      assert_norm (first_byte_of_header cid_len1 last1 (MLong version dcid scid (MInitial token payload_length packet_number_length packet_number)) == (| Long, (| (), (| Initial, (| (), (| packet_number_length, () |) |) |) |) |) );
      assert_norm (bitsum'_key_of_t first_byte (first_byte_of_header cid_len1 last1 (MLong version dcid scid (MInitial token payload_length packet_number_length packet_number))) == (| Long, (| (), (| Initial, (| (), (| packet_number_length, () |) |) |) |) |) );
      assert_norm (first_byte_of_header cid_len2 last2 (MLong version dcid scid (MInitial token payload_length packet_number_length packet_number)) == (| Long, (| (), (| Initial, (| (), (| packet_number_length, () |) |) |) |) |) );
      assert_norm (bitsum'_key_of_t first_byte (first_byte_of_header cid_len2 last2 (MLong version dcid scid (MInitial token payload_length packet_number_length packet_number))) == (| Long, (| (), (| Initial, (| (), (| packet_number_length, () |) |) |) |) |) );
      let plpnl : (plpnl : uint62_t { payload_and_pn_length_prop packet_number_length plpnl }) = payload_length `U64.add` Cast.uint32_to_uint64 packet_number_length in
      serialize_nondep_then_eq serialize_common_long (serialize_bounded_vlgenbytes 0 token_max_len (serialize_bounded_varint 0 token_max_len) `serialize_nondep_then` serialize_payload_length_pn last1 packet_number_length) ((version, (dcid, scid)), (token, (plpnl, packet_number)));
      serialize_nondep_then_eq (serialize_bounded_vlgenbytes 0 token_max_len (serialize_bounded_varint 0 token_max_len)) (serialize_payload_length_pn last1 packet_number_length) (token, (plpnl, packet_number));
      serialize_nondep_then_eq (serialize_varint `serialize_filter` payload_and_pn_length_prop packet_number_length) (serialize_packet_number last1 packet_number_length) (plpnl, packet_number);
      serialize_nondep_then_eq serialize_common_long (serialize_bounded_vlgenbytes 0 token_max_len (serialize_bounded_varint 0 token_max_len) `serialize_nondep_then` serialize_payload_length_pn last2 packet_number_length) ((version, (dcid, scid)), (token, (plpnl, packet_number)));
      serialize_nondep_then_eq (serialize_bounded_vlgenbytes 0 token_max_len (serialize_bounded_varint 0 token_max_len)) (serialize_payload_length_pn last2 packet_number_length) (token, (plpnl, packet_number));
      serialize_nondep_then_eq (serialize_varint `serialize_filter` payload_and_pn_length_prop packet_number_length) (serialize_packet_number last2 packet_number_length) (plpnl, packet_number);
      serialize_packet_number_ext last1 last2 packet_number_length packet_number
    | MHandshake payload_length packet_number_length packet_number ->
      assert_norm (first_byte_of_header cid_len1 last1 (MLong version dcid scid (MHandshake payload_length packet_number_length packet_number)) == (| Long, (| (), (| Handshake, (| (), (| packet_number_length, () |) |) |) |) |) );
      assert_norm (bitsum'_key_of_t first_byte (first_byte_of_header cid_len1 last1 (MLong version dcid scid (MHandshake payload_length packet_number_length packet_number))) == (| Long, (| (), (| Handshake, (| (), (| packet_number_length, () |) |) |) |) |) );
      assert_norm (first_byte_of_header cid_len2 last2 (MLong version dcid scid (MHandshake payload_length packet_number_length packet_number)) == (| Long, (| (), (| Handshake, (| (), (| packet_number_length, () |) |) |) |) |) );
      assert_norm (bitsum'_key_of_t first_byte (first_byte_of_header cid_len2 last2 (MLong version dcid scid (MHandshake payload_length packet_number_length packet_number))) == (| Long, (| (), (| Handshake, (| (), (| packet_number_length, () |) |) |) |) |) );
      let plpnl : (plpnl : uint62_t { payload_and_pn_length_prop packet_number_length plpnl }) = payload_length `U64.add` Cast.uint32_to_uint64 packet_number_length in
      serialize_nondep_then_eq serialize_common_long (serialize_payload_length_pn last1 packet_number_length) ((version, (dcid, scid)), (plpnl, packet_number));
      serialize_nondep_then_eq (serialize_varint `serialize_filter` payload_and_pn_length_prop packet_number_length) (serialize_packet_number last1 packet_number_length) (plpnl, packet_number);
      serialize_nondep_then_eq serialize_common_long (serialize_payload_length_pn last2 packet_number_length) ((version, (dcid, scid)), (plpnl, packet_number));
      serialize_nondep_then_eq (serialize_varint `serialize_filter` payload_and_pn_length_prop packet_number_length) (serialize_packet_number last2 packet_number_length) (plpnl, packet_number);
      serialize_packet_number_ext last1 last2 packet_number_length packet_number
    | MZeroRTT payload_length packet_number_length packet_number ->
      assert_norm (first_byte_of_header cid_len1 last1 (MLong version dcid scid (MZeroRTT payload_length packet_number_length packet_number)) == (| Long, (| (), (| ZeroRTT, (| (), (| packet_number_length, () |) |) |) |) |) );
      assert_norm (bitsum'_key_of_t first_byte (first_byte_of_header cid_len1 last1 (MLong version dcid scid (MZeroRTT payload_length packet_number_length packet_number))) == (| Long, (| (), (| ZeroRTT, (| (), (| packet_number_length, () |) |) |) |) |) );
      assert_norm (first_byte_of_header cid_len2 last2 (MLong version dcid scid (MZeroRTT payload_length packet_number_length packet_number)) == (| Long, (| (), (| ZeroRTT, (| (), (| packet_number_length, () |) |) |) |) |) );
      assert_norm (bitsum'_key_of_t first_byte (first_byte_of_header cid_len2 last2 (MLong version dcid scid (MZeroRTT payload_length packet_number_length packet_number))) == (| Long, (| (), (| ZeroRTT, (| (), (| packet_number_length, () |) |) |) |) |) );
      let plpnl : (plpnl : uint62_t { payload_and_pn_length_prop packet_number_length plpnl }) = payload_length `U64.add` Cast.uint32_to_uint64 packet_number_length in
      serialize_nondep_then_eq serialize_common_long (serialize_payload_length_pn last1 packet_number_length) ((version, (dcid, scid)), (plpnl, packet_number));
      serialize_nondep_then_eq (serialize_varint `serialize_filter` payload_and_pn_length_prop packet_number_length) (serialize_packet_number last1 packet_number_length) (plpnl, packet_number);
      serialize_nondep_then_eq serialize_common_long (serialize_payload_length_pn last2 packet_number_length) ((version, (dcid, scid)), (plpnl, packet_number));
      serialize_nondep_then_eq (serialize_varint `serialize_filter` payload_and_pn_length_prop packet_number_length) (serialize_packet_number last2 packet_number_length) (plpnl, packet_number);
      serialize_packet_number_ext last1 last2 packet_number_length packet_number
    | MRetry unused odcid ->
      assert_norm (first_byte_of_header cid_len1 last1 (MLong version dcid scid (MRetry unused odcid)) == (| Long, (| (), (| Retry, (unused, ()) |) |) |) );
      assert_norm (bitsum'_key_of_t first_byte (first_byte_of_header cid_len1 last1 (MLong version dcid scid (MRetry unused odcid))) == (| Long, (| (), (| Retry, () |) |) |) );
      assert_norm (first_byte_of_header cid_len2 last2 (MLong version dcid scid (MRetry unused odcid)) == (| Long, (| (), (| Retry, (unused, ()) |) |) |) );
      assert_norm (bitsum'_key_of_t first_byte (first_byte_of_header cid_len2 last2 (MLong version dcid scid (MRetry unused odcid))) == (| Long, (| (), (| Retry, () |) |) |) )
    end

#pop-options

(* Fulfill the interface *)

let last_packet_number
  (h: header)
: Tot last_packet_number_t
= if is_retry h then 0uL else let pn = packet_number h in if pn = 0uL then 0uL else pn `U64.sub` 1uL

#push-options "--z3rlimit 32"

let parse_header_prop_intro
  (h: header)
: Lemma
  (parse_header_prop (U32.uint_to_t (dcid_len h)) (last_packet_number h) h)
= ()

#pop-options

let format_header' (h: header) : GTot bytes =
  parse_header_prop_intro h;
  serialize (serialize_header (U32.uint_to_t (dcid_len h)) (last_packet_number h)) h

let header_len h =
  assert_norm (
    let k = parse_header_kind' (U32.uint_to_t (dcid_len h)) (last_packet_number h) in
    match k.parser_kind_high with
    | None -> False
    | Some hg -> hg < header_len_bound
  );
  parse_header_prop_intro h;
  Seq.length (format_header' h)

let format_header h = format_header' h

#push-options "--z3rlimit 32"

let format_header_is_short h =
  parse_header_prop_intro h;
  let dl = U32.uint_to_t (dcid_len h) in
  let last = last_packet_number h in
  serialize_header_eq dl last h;
  let tg = first_byte_of_header dl last h in
  let x = synth_bitsum'_recip first_byte tg in
  LI.serialize_u8_spec x;
  assert (Seq.index (format_header h) 0 == x);
  assert (MShort? h <==> uint8.get_bitfield (Seq.index (format_header h) 0) 7 8 == (LowParse.Spec.Enum.enum_repr_of_key header_form Short <: U8.t))

#pop-options

let first_byte_is_retry
  (k: bitsum'_type first_byte)
: GTot bool
= match k with
  | (| Long, (| (), (| Retry, (unused, ()) |) |) |) -> true
  | _ -> false

let first_byte_is_retry_correct
  (short_dcid_len: short_dcid_len_t)
  (last: last_packet_number_t)
  (h: header' short_dcid_len last)
: Lemma
  (is_retry h <==> first_byte_is_retry (first_byte_of_header short_dcid_len last h))
= ()

let repr_of_pn_length
  (x: packet_number_length_t)
: Tot (y: enum_repr packet_number_length {
    list_mem x (list_map fst packet_number_length) /\
    y == enum_repr_of_key packet_number_length x
  })
= assert_norm (pow2 8 == 256);
  Cast.uint32_to_uint8 (x `U32.sub` 1ul)

#push-options "--z3rlimit 512 --max_fuel 8 --initial_fuel 8 --max_ifuel 8 --initial_ifuel 8"

#restart-solver

let format_header_is_retry h =
  parse_header_prop_intro h;
  let dl = U32.uint_to_t (dcid_len h) in
  let last = last_packet_number h in
  serialize_header_eq dl last h;
  let tg = first_byte_of_header dl last h in
  let x = synth_bitsum'_recip first_byte tg in
  LI.serialize_u8_spec x;
  assert (Seq.index (format_header h) 0 == x);
  assert (is_retry h <==> (
    uint8.get_bitfield (Seq.index (format_header h) 0) 7 8 == (LowParse.Spec.Enum.enum_repr_of_key header_form Long <: U8.t) /\
    uint8.get_bitfield (Seq.index (format_header h) 0) 4 6 == (LowParse.Spec.Enum.enum_repr_of_key long_packet_type Retry <: U8.t)
  ))

#restart-solver

let format_header_pn_length h =
  parse_header_prop_intro h;
  let dl = U32.uint_to_t (dcid_len h) in
  let last = last_packet_number h in
  serialize_header_eq dl last h;
  let tg = first_byte_of_header dl last h in
  let x = synth_bitsum'_recip first_byte tg in
  LI.serialize_u8_spec x;
  assert (Seq.index (format_header h) 0 == x);
  let pnl_k = pn_length h in
  let pnl_r = repr_of_pn_length pnl_k in
  assert (list_mem pnl_k (list_map fst packet_number_length));
  assert (pnl_r == enum_repr_of_key packet_number_length pnl_k); 
  assert (
    uint8.get_bitfield (Seq.index (format_header h) 0) 0 2 ==
    (pnl_r <: U8.t)
  )

#pop-options

val pn_offset'
  (short_dcid_len: short_dcid_len_t)
  (last: last_packet_number_t)
  (h: header' short_dcid_len last )
: Ghost nat
  (requires (~ (is_retry h)))
  (ensures (fun n ->
    let s = serialize (serialize_header short_dcid_len last) h in
    0 < n /\
    n + U32.v (pn_length h) == Seq.length s /\
    Seq.slice s n (Seq.length s) `Seq.equal` serialize (serialize_packet_number last (pn_length h)) (packet_number h)
  ))

#push-options "--z3rlimit 1024 --query_stats --max_fuel 4 --initial_fuel 4"

#restart-solver

let pn_offset'
  short_dcid_len last h
= serialize_header_eq short_dcid_len last h;
  let tg = first_byte_of_header short_dcid_len last h in
  let x = synth_bitsum'_recip first_byte tg in
  LI.serialize_u8_spec x;
  match h with
  | MShort spin key_phase dcid packet_number_length packet_number ->
    assert_norm (first_byte_of_header short_dcid_len last (MShort spin key_phase dcid packet_number_length packet_number) == (| Short, (| (), ((if spin then 1uy else 0uy), (| (), ((if key_phase then 1uy else 0uy), (| packet_number_length, () |) ) |) ) |) |) );
    assert_norm (bitsum'_key_of_t first_byte (first_byte_of_header short_dcid_len last (MShort spin key_phase dcid packet_number_length packet_number)) == (| Short, (| (), (| (), (| packet_number_length, () |) |) |) |) ) ;
    serialize_nondep_then_eq (serialize_weaken (strong_parser_kind 0 20 None) (serialize_flbytes (U32.v short_dcid_len))) (serialize_packet_number last packet_number_length) (dcid, packet_number);
    serialize_length (serialize_packet_number last packet_number_length) packet_number;
    1 + Seq.length (serialize (serialize_weaken (strong_parser_kind 0 20 None) (serialize_flbytes (U32.v short_dcid_len))) dcid)
  | MLong version dcid scid spec ->
    begin match spec with
    | MInitial token payload_length packet_number_length packet_number ->
      assert_norm (first_byte_of_header short_dcid_len last (MLong version dcid scid (MInitial token payload_length packet_number_length packet_number)) == (| Long, (| (), (| Initial, (| (), (| packet_number_length, () |) |) |) |) |) );
      assert_norm (bitsum'_key_of_t first_byte (first_byte_of_header short_dcid_len last (MLong version dcid scid (MInitial token payload_length packet_number_length packet_number))) == (| Long, (| (), (| Initial, (| (), (| packet_number_length, () |) |) |) |) |) );
      let plpnl : (plpnl : uint62_t { payload_and_pn_length_prop packet_number_length plpnl }) = payload_length `U64.add` Cast.uint32_to_uint64 packet_number_length in
      serialize_nondep_then_eq serialize_common_long (serialize_bounded_vlgenbytes 0 token_max_len (serialize_bounded_varint 0 token_max_len) `serialize_nondep_then` serialize_payload_length_pn last packet_number_length) ((version, (dcid, scid)), (token, (plpnl, packet_number)));
      serialize_nondep_then_eq (serialize_bounded_vlgenbytes 0 token_max_len (serialize_bounded_varint 0 token_max_len)) (serialize_payload_length_pn last packet_number_length) (token, (plpnl, packet_number));
      serialize_nondep_then_eq (serialize_varint `serialize_filter` payload_and_pn_length_prop packet_number_length) (serialize_packet_number last packet_number_length) (plpnl, packet_number);
      serialize_length (serialize_packet_number last packet_number_length) packet_number;
      1 + Seq.length (serialize serialize_common_long (version, (dcid, scid))) + Seq.length (serialize (serialize_bounded_vlgenbytes 0 token_max_len (serialize_bounded_varint 0 token_max_len)) token) + Seq.length (serialize (serialize_varint `serialize_filter` payload_and_pn_length_prop packet_number_length) plpnl)
    | MHandshake payload_length packet_number_length packet_number ->
      assert_norm (first_byte_of_header short_dcid_len last (MLong version dcid scid (MHandshake payload_length packet_number_length packet_number)) == (| Long, (| (), (| Handshake, (| (), (| packet_number_length, () |) |) |) |) |) );
      assert_norm (bitsum'_key_of_t first_byte (first_byte_of_header short_dcid_len last (MLong version dcid scid (MHandshake payload_length packet_number_length packet_number))) == (| Long, (| (), (| Handshake, (| (), (| packet_number_length, () |) |) |) |) |) );
      let plpnl : (plpnl : uint62_t { payload_and_pn_length_prop packet_number_length plpnl }) = payload_length `U64.add` Cast.uint32_to_uint64 packet_number_length in
      serialize_nondep_then_eq serialize_common_long (serialize_payload_length_pn last packet_number_length) ((version, (dcid, scid)), (plpnl, packet_number));
      serialize_nondep_then_eq (serialize_varint `serialize_filter` payload_and_pn_length_prop packet_number_length) (serialize_packet_number last packet_number_length) (plpnl, packet_number);
      serialize_length (serialize_packet_number last packet_number_length) packet_number;
      1 + Seq.length (serialize serialize_common_long (version, (dcid, scid))) + Seq.length (serialize (serialize_varint `serialize_filter` payload_and_pn_length_prop packet_number_length) plpnl)
    | MZeroRTT payload_length packet_number_length packet_number ->
      assert_norm (first_byte_of_header short_dcid_len last (MLong version dcid scid (MZeroRTT payload_length packet_number_length packet_number)) == (| Long, (| (), (| ZeroRTT, (| (), (| packet_number_length, () |) |) |) |) |) );
      assert_norm (bitsum'_key_of_t first_byte (first_byte_of_header short_dcid_len last (MLong version dcid scid (MZeroRTT payload_length packet_number_length packet_number))) == (| Long, (| (), (| ZeroRTT, (| (), (| packet_number_length, () |) |) |) |) |) );
      let plpnl : (plpnl : uint62_t { payload_and_pn_length_prop packet_number_length plpnl }) = payload_length `U64.add` Cast.uint32_to_uint64 packet_number_length in
      serialize_nondep_then_eq serialize_common_long (serialize_payload_length_pn last packet_number_length) ((version, (dcid, scid)), (plpnl, packet_number));
      serialize_nondep_then_eq (serialize_varint `serialize_filter` payload_and_pn_length_prop packet_number_length) (serialize_packet_number last packet_number_length) (plpnl, packet_number);
      serialize_length (serialize_packet_number last packet_number_length) packet_number;
      1 + Seq.length (serialize serialize_common_long (version, (dcid, scid))) + Seq.length (serialize (serialize_varint `serialize_filter` payload_and_pn_length_prop packet_number_length) plpnl)
    end

#pop-options

let pn_offset h =
  pn_offset' (U32.uint_to_t (dcid_len h)) (last_packet_number h) h

(* From https://tools.ietf.org/html/draft-ietf-quic-tls-23#section-5.4.2 *)

let putative_pn_offset cid_len x =
  match parse parse_u8 x with
  | None -> None
  | Some (hd, consumed1) ->
    let _ =
      parser_kind_prop_equiv parse_u8_kind parse_u8;
      assert (consumed1 == 1) 
    in
    let x1 = Seq.slice x consumed1 (Seq.length x) in
    if uint8.get_bitfield hd 7 8 = 0uy // test packet kind
    then // short
      if not (cid_len <= 20)
      then None
      else
      match parse (parse_flbytes cid_len) x1 with
      | None -> None
      | Some (_, consumed2) ->
        Some (consumed1 + consumed2)
    else // long
      let packet_type = uint8.get_bitfield hd 4 6 in
      if packet_type = 3uy // is retry?
      then None
      else
        match parse parse_common_long x1 with
        | None -> None
        | Some (_, consumed2) ->
          let x2 = Seq.slice x1 consumed2 (Seq.length x1) in
          let mconsumed3 : option (consumed_length x2) =
            if packet_type = 0uy // is initial?
            then
              match parse (parse_bounded_vlgenbytes 0 token_max_len (parse_bounded_varint 0 token_max_len)) x2 with
              | None -> None
              | Some (_, x3) -> Some x3
            else Some 0
          in
          match mconsumed3 with
          | None -> None
          | Some consumed3 ->
            match parse parse_varint (Seq.slice x2 consumed3 (Seq.length x2)) with
            | None -> None
            | Some (_, consumed4) -> Some (consumed1 + consumed2 + consumed3 + consumed4)

#push-options "--z3rlimit 512"

#restart-solver

let putative_pn_offset_frame
  cid_len x1 x2
= let Some off = putative_pn_offset cid_len x1 in
  parse_u8_spec' x1;
  parse_u8_spec' x2;
  parser_kind_prop_equiv parse_u8_kind parse_u8;
  let hd1 = Seq.index x1 0 in
  let is_short = uint8.get_bitfield hd1 7 8 = 0uy in
  let number_of_protected_bits = if is_short then 5 else 4 in
  let hd2 = Seq.index x2 0 in
  BF.get_bitfield_get_bitfield (U8.v hd1) number_of_protected_bits 8 (7 - number_of_protected_bits) (8 - number_of_protected_bits);
  BF.get_bitfield_get_bitfield (U8.v hd2) number_of_protected_bits 8 (7 - number_of_protected_bits) (8 - number_of_protected_bits);
  assert (uint8.get_bitfield hd1 7 8 == uint8.get_bitfield hd2 7 8);
  let x1_1 = Seq.slice x1 1 (Seq.length x1) in
  let x2_1 = Seq.slice x2 1 (Seq.length x2) in
  let x'1 = Seq.slice x1_1 0 (off - 1) in
  if is_short
  then begin
    parse_strong_prefix (parse_flbytes cid_len) x1_1 x'1;
    parse_strong_prefix (parse_flbytes cid_len) x'1 x2_1
  end else begin
    let packet_type = uint8.get_bitfield hd1 4 6 in
    BF.get_bitfield_get_bitfield (U8.v hd1) 4 8 0 2;
    BF.get_bitfield_get_bitfield (U8.v hd2) 4 8 0 2;
    assert (packet_type == uint8.get_bitfield hd2 4 6);
    parse_strong_prefix parse_common_long x1_1 (Seq.slice x1_1 0 (off - 1));
    parse_strong_prefix parse_common_long (Seq.slice x2_1 0 (off - 1)) x2_1;
    let Some (_, consumed2) = parse parse_common_long x1_1 in
    let x1_2 = Seq.slice x1_1 consumed2 (Seq.length x1_1) in
    let x2_2 = Seq.slice x2_1 consumed2 (Seq.length x2_1) in
    assert (Seq.slice (Seq.slice x1_1 0 (off - 1)) consumed2 (off - 1) == Seq.slice (Seq.slice x2_1 0 (off - 1)) consumed2 (off - 1));
    if packet_type = 0uy
    then begin
      let x'2 = Seq.slice x1_2 0 (off - 1 - consumed2) in
      parse_strong_prefix
        (parse_bounded_vlgenbytes 0 token_max_len (parse_bounded_varint 0 token_max_len))
        x1_2 x'2;
      parse_strong_prefix
        (parse_bounded_vlgenbytes 0 token_max_len (parse_bounded_varint 0 token_max_len))
        x'2 x2_2          
    end;
    let consumed3 =
      if packet_type = 0uy
      then let Some (_, consumed3) = parse (parse_bounded_vlgenbytes 0 token_max_len (parse_bounded_varint 0 token_max_len)) x1_2 in consumed3
      else 0
    in
    let x1_3 = Seq.slice x1_2 consumed3 (Seq.length x1_2) in
    let x2_3 = Seq.slice x2_2 consumed3 (Seq.length x2_2) in
    assert (Seq.slice (Seq.slice x1_2 0 (off - 1 - consumed2)) consumed3 (off - 1 - consumed2) == Seq.slice (Seq.slice x2_2 0 (off - 1 - consumed2)) consumed3 (off - 1 - consumed2));
    let x'3 = Seq.slice x1_3 0 (off - 1 - consumed2 - consumed3) in
    parse_strong_prefix parse_varint x1_3 x'3;
    parse_strong_prefix parse_varint x'3 x2_3
  end

#pop-options

val format_header_is_initial: h: header -> Lemma
  ((MLong? h /\ MInitial? (MLong?.spec h))  <==> (
    BF.get_bitfield (U8.v (Seq.index (format_header h) 0)) 7 8 == 1 /\
    BF.get_bitfield (U8.v (Seq.index (format_header h) 0)) 4 6 == 0
  ))

#push-options "--z3rlimit 256 --max_fuel 8 --initial_fuel 8 --max_ifuel 8 --initial_ifuel 8"

#restart-solver

let format_header_is_initial h =
  parse_header_prop_intro h;
  let dl = U32.uint_to_t (dcid_len h) in
  let last = last_packet_number h in
  serialize_header_eq dl last h;
  let tg = first_byte_of_header dl last h in
  let x = synth_bitsum'_recip first_byte tg in
  LI.serialize_u8_spec x;
  assert (Seq.index (format_header h) 0 == x);
  assert ((MLong? h /\ MInitial? (MLong?.spec h)) <==> (
    uint8.get_bitfield (Seq.index (format_header h) 0) 7 8 == (LowParse.Spec.Enum.enum_repr_of_key header_form Long <: U8.t) /\
    uint8.get_bitfield (Seq.index (format_header h) 0) 4 6 == (LowParse.Spec.Enum.enum_repr_of_key long_packet_type Initial <: U8.t)
  ))

#pop-options

#push-options "--z3rlimit 1024 --max_fuel 4 --initial_fuel 4 --query_stats"

#restart-solver

let putative_pn_offset_correct h cid_len =
  let x = format_header h in
  let short_dcid_len : short_dcid_len_t = U32.uint_to_t (dcid_len h) in
  let last : last_packet_number_t = last_packet_number h in
  parse_header_prop_intro h;
  serialize_header_eq short_dcid_len last h;
  let tg = first_byte_of_header short_dcid_len last h in
  let kt = bitsum'_key_of_t first_byte tg in
  let hd = synth_bitsum'_recip first_byte tg in
  LI.serialize_u8_spec hd;
  parse_serialize serialize_u8 hd;
  parse_strong_prefix parse_u8 (serialize serialize_u8 hd) (serialize serialize_u8 hd `Seq.append` serialize (serialize_header_body short_dcid_len last kt) (mk_header_body short_dcid_len last tg h));
  assert (parse parse_u8 x == Some (hd, 1));
  let x1 = Seq.slice x 1 (Seq.length x) in
  assert (x1 `Seq.equal` serialize (serialize_header_body short_dcid_len last kt) (mk_header_body short_dcid_len last tg h));
  format_header_is_short h;
  assert (MShort? h <==> uint8.get_bitfield hd 7 8 = 0uy);
  if uint8.get_bitfield hd 7 8 = 0uy
  then begin
    assert (MShort? h);
    assert (cid_len == dcid_len h);
    assert (cid_len <= 20);
    let MShort spin key_phase dcid packet_number_length packet_number = h in
    assert_norm (first_byte_of_header short_dcid_len last (MShort spin key_phase dcid packet_number_length packet_number) == (| Short, (| (), ((if spin then 1uy else 0uy), (| (), ((if key_phase then 1uy else 0uy), (| packet_number_length, () |) ) |) ) |) |) );
    assert_norm (bitsum'_key_of_t first_byte (first_byte_of_header short_dcid_len last (MShort spin key_phase dcid packet_number_length packet_number)) == (| Short, (| (), (| (), (| packet_number_length, () |) |) |) |) );
//    assert (x1 == serialize (serialize_weaken (strong_parser_kind 0 20 None) (serialize_flbytes cid_len) `serialize_nondep_then` serialize_packet_number last (MShort?.packet_number_length h)) (MShort?.dcid h, MShort?.packet_number h));
    serialize_nondep_then_eq (serialize_weaken (strong_parser_kind 0 20 None) (serialize_flbytes cid_len)) (serialize_packet_number last (MShort?.packet_number_length h)) (MShort?.dcid h, MShort?.packet_number h);
    assert (serialize (serialize_weaken (strong_parser_kind 0 20 None) (serialize_flbytes cid_len)) (MShort?.dcid h) == serialize (serialize_flbytes cid_len) (MShort?.dcid h));
    parse_serialize (serialize_flbytes cid_len) (MShort?.dcid h);
    parse_strong_prefix (parse_flbytes cid_len) (serialize (serialize_flbytes cid_len) (MShort?.dcid h)) x1;
    assert (parse (parse_flbytes cid_len) x1 == Some (MShort?.dcid h, Seq.length (serialize (serialize_weaken (strong_parser_kind 0 20 None) (serialize_flbytes cid_len)) (MShort?.dcid h))));
    assert (putative_pn_offset cid_len x = Some (1 + Seq.length (serialize (serialize_weaken (strong_parser_kind 0 20 None) (serialize_flbytes cid_len)) (MShort?.dcid h))));
    assert_norm (pn_offset' short_dcid_len last (MShort spin key_phase dcid packet_number_length packet_number) == 1 + Seq.length (serialize (serialize_weaken (strong_parser_kind 0 20 None) (serialize_flbytes (U32.v short_dcid_len))) dcid));
    ()
  end else begin
    assert (MLong? h);
    let MLong version dcid scid spec = h in
    format_header_is_retry h;
    assert (is_retry h <==> uint8.get_bitfield hd 4 6 == 3uy);
    assert (~ (MRetry? spec));
    format_header_is_initial h;
    assert (MInitial? spec <==> uint8.get_bitfield hd 4 6 == 0uy);
    if uint8.get_bitfield hd 4 6 = 0uy
    then begin
      assert (MInitial? spec);
      let MInitial token payload_length packet_number_length packet_number = spec in
      assert_norm (first_byte_of_header short_dcid_len last (MLong version dcid scid (MInitial token payload_length packet_number_length packet_number)) == (| Long, (| (), (| Initial, (| (), (| packet_number_length, () |) |) |) |) |) );
      assert_norm (bitsum'_key_of_t first_byte (first_byte_of_header short_dcid_len last (MLong version dcid scid (MInitial token payload_length packet_number_length packet_number))) == (| Long, (| (), (| Initial, (| (), (| packet_number_length, () |) |) |) |) |) );
      let plpnl : (plpnl : uint62_t { payload_and_pn_length_prop packet_number_length plpnl }) = payload_length `U64.add` Cast.uint32_to_uint64 packet_number_length in
      serialize_nondep_then_eq serialize_common_long (serialize_bounded_vlgenbytes 0 token_max_len (serialize_bounded_varint 0 token_max_len) `serialize_nondep_then` serialize_payload_length_pn last packet_number_length) ((version, (dcid, scid)), (token, (plpnl, packet_number)));
      parse_serialize serialize_common_long (version, (dcid, scid));
      parse_strong_prefix parse_common_long (serialize serialize_common_long (version, (dcid, scid))) x1;
      let consumed2 = Seq.length (serialize serialize_common_long (version, (dcid, scid))) in
      assert (parse parse_common_long x1 == Some ((version, (dcid, scid)), consumed2));
      let x2 = Seq.slice x1 consumed2 (Seq.length x1) in
      assert (x2 `Seq.equal` serialize (serialize_bounded_vlgenbytes 0 token_max_len (serialize_bounded_varint 0 token_max_len) `serialize_nondep_then` serialize_payload_length_pn last packet_number_length) (token, (plpnl, packet_number)));
      serialize_nondep_then_eq (serialize_bounded_vlgenbytes 0 token_max_len (serialize_bounded_varint 0 token_max_len)) (serialize_payload_length_pn last packet_number_length) (token, (plpnl, packet_number));
      parse_serialize (serialize_bounded_vlgenbytes 0 token_max_len (serialize_bounded_varint 0 token_max_len)) token;
      parse_strong_prefix (parse_bounded_vlgenbytes 0 token_max_len (parse_bounded_varint 0 token_max_len)) (serialize (serialize_bounded_vlgenbytes 0 token_max_len (serialize_bounded_varint 0 token_max_len)) token) x2;
      let consumed3 = Seq.length (serialize (serialize_bounded_vlgenbytes 0 token_max_len (serialize_bounded_varint 0 token_max_len)) token) in
      assert (parse (parse_bounded_vlgenbytes 0 token_max_len (parse_bounded_varint 0 token_max_len)) x2 == Some (token, consumed3));
      let x3 = Seq.slice x2 consumed3 (Seq.length x2) in
      assert (x3 `Seq.equal` serialize (serialize_payload_length_pn last packet_number_length) (plpnl, packet_number));
      serialize_nondep_then_eq (serialize_varint `serialize_filter` payload_and_pn_length_prop packet_number_length) (serialize_packet_number last packet_number_length) (plpnl, packet_number);
      assert (serialize (serialize_varint `serialize_filter` payload_and_pn_length_prop packet_number_length) plpnl == serialize serialize_varint plpnl);
      parse_serialize serialize_varint plpnl;
      parse_strong_prefix parse_varint (serialize serialize_varint plpnl) x3;
      let consumed4 = Seq.length (serialize (serialize_varint `serialize_filter` payload_and_pn_length_prop packet_number_length) plpnl) in
      assert (consumed4 == Seq.length (serialize serialize_varint plpnl));
      assert (parse parse_varint x3 == Some (plpnl, consumed4));
      assert (putative_pn_offset cid_len x = Some (1 + consumed2 + consumed3 + consumed4));
      assert_norm (pn_offset' short_dcid_len last (MLong version dcid scid (MInitial token payload_length packet_number_length packet_number)) == 1 + consumed2 + consumed3 + consumed4)
    end else
      match spec with
      | MHandshake payload_length packet_number_length packet_number ->
        assert_norm (first_byte_of_header short_dcid_len last (MLong version dcid scid (MHandshake payload_length packet_number_length packet_number)) == (| Long, (| (), (| Handshake, (| (), (| packet_number_length, () |) |) |) |) |) );
        assert_norm (bitsum'_key_of_t first_byte (first_byte_of_header short_dcid_len last (MLong version dcid scid (MHandshake payload_length packet_number_length packet_number))) == (| Long, (| (), (| Handshake, (| (), (| packet_number_length, () |) |) |) |) |) );
        let plpnl : (plpnl : uint62_t { payload_and_pn_length_prop packet_number_length plpnl }) = payload_length `U64.add` Cast.uint32_to_uint64 packet_number_length in
        serialize_nondep_then_eq serialize_common_long (serialize_payload_length_pn last packet_number_length) ((version, (dcid, scid)), (plpnl, packet_number));
        parse_serialize serialize_common_long (version, (dcid, scid));
        parse_strong_prefix parse_common_long (serialize serialize_common_long (version, (dcid, scid))) x1;
        let consumed2 = Seq.length (serialize serialize_common_long (version, (dcid, scid))) in
        assert (parse parse_common_long x1 == Some ((version, (dcid, scid)), consumed2));
        let x2 = Seq.slice x1 consumed2 (Seq.length x1) in
        assert (x2 `Seq.equal` serialize (serialize_payload_length_pn last packet_number_length) (plpnl, packet_number));
        let x3 = Seq.slice x2 0 (Seq.length x2) in
        assert (x3 `Seq.equal` x2);
        serialize_nondep_then_eq (serialize_varint `serialize_filter` payload_and_pn_length_prop packet_number_length) (serialize_packet_number last packet_number_length) (plpnl, packet_number);
        assert (serialize (serialize_varint `serialize_filter` payload_and_pn_length_prop packet_number_length) plpnl == serialize serialize_varint plpnl);
        parse_serialize serialize_varint plpnl;
        parse_strong_prefix parse_varint (serialize serialize_varint plpnl) x3;
        let consumed4 = Seq.length (serialize (serialize_varint `serialize_filter` payload_and_pn_length_prop packet_number_length) plpnl) in
        assert (consumed4 == Seq.length (serialize serialize_varint plpnl));
        assert (parse parse_varint x3 == Some (plpnl, consumed4));
        assert (putative_pn_offset cid_len x = Some (1 + consumed2 + consumed4));
        assert_norm (pn_offset' short_dcid_len last (MLong version dcid scid (MHandshake payload_length packet_number_length packet_number)) == 1 + consumed2 + 0 + consumed4)
      | MZeroRTT payload_length packet_number_length packet_number ->
        assert_norm (first_byte_of_header short_dcid_len last (MLong version dcid scid (MZeroRTT payload_length packet_number_length packet_number)) == (| Long, (| (), (| ZeroRTT, (| (), (| packet_number_length, () |) |) |) |) |) );
        assert_norm (bitsum'_key_of_t first_byte (first_byte_of_header short_dcid_len last (MLong version dcid scid (MZeroRTT payload_length packet_number_length packet_number))) == (| Long, (| (), (| ZeroRTT, (| (), (| packet_number_length, () |) |) |) |) |) );
        let plpnl : (plpnl : uint62_t { payload_and_pn_length_prop packet_number_length plpnl }) = payload_length `U64.add` Cast.uint32_to_uint64 packet_number_length in
        serialize_nondep_then_eq serialize_common_long (serialize_payload_length_pn last packet_number_length) ((version, (dcid, scid)), (plpnl, packet_number));
        parse_serialize serialize_common_long (version, (dcid, scid));
        parse_strong_prefix parse_common_long (serialize serialize_common_long (version, (dcid, scid))) x1;
        let consumed2 = Seq.length (serialize serialize_common_long (version, (dcid, scid))) in
        assert (parse parse_common_long x1 == Some ((version, (dcid, scid)), consumed2));
        let x2 = Seq.slice x1 consumed2 (Seq.length x1) in
        assert (x2 `Seq.equal` serialize (serialize_payload_length_pn last packet_number_length) (plpnl, packet_number));
        let x3 = Seq.slice x2 0 (Seq.length x2) in
        assert (x3 `Seq.equal` x2);
        serialize_nondep_then_eq (serialize_varint `serialize_filter` payload_and_pn_length_prop packet_number_length) (serialize_packet_number last packet_number_length) (plpnl, packet_number);
        assert (serialize (serialize_varint `serialize_filter` payload_and_pn_length_prop packet_number_length) plpnl == serialize serialize_varint plpnl);
        parse_serialize serialize_varint plpnl;
        parse_strong_prefix parse_varint (serialize serialize_varint plpnl) x3;
        let consumed4 = Seq.length (serialize (serialize_varint `serialize_filter` payload_and_pn_length_prop packet_number_length) plpnl) in
        assert (consumed4 == Seq.length (serialize serialize_varint plpnl));
        assert (parse parse_varint x3 == Some (plpnl, consumed4));
        assert (putative_pn_offset cid_len x = Some (1 + consumed2 + consumed4));
        assert_norm (pn_offset' short_dcid_len last (MLong version dcid scid (MZeroRTT payload_length packet_number_length packet_number)) == 1 + consumed2 + 0 + consumed4)
  end

#pop-options

let parse_header cid_len last b =
  match parse (lp_parse_header (U32.uint_to_t cid_len) (U64.uint_to_t last)) b with
  | None -> H_Failure
  | Some (h, consumed) -> H_Success h (Seq.slice b consumed (Seq.length b))

module Seq = FStar.Seq

let lemma_header_parsing_correct
  h c cid_len last
=
  parse_header_prop_intro h;
  let cid_len32 : short_dcid_len_t = U32.uint_to_t cid_len in
  serialize_header_ext (U32.uint_to_t (dcid_len h)) cid_len32 (last_packet_number h) (U64.uint_to_t last) h;
  let s = format_header h in
  assert (s == serialize (serialize_header cid_len32 (U64.uint_to_t last)) h);
  parse_serialize (serialize_header cid_len32 (U64.uint_to_t last)) h;
  assert_norm ((parse_header_kind' cid_len32 (U64.uint_to_t last)).parser_kind_subkind == Some ParserStrong);
  parse_strong_prefix (lp_parse_header cid_len32 (U64.uint_to_t last)) s (s `Seq.append` c);
  Seq.lemma_split (s `Seq.append` c) (Seq.length s);
  assert (s `Seq.equal` Seq.slice s 0 (Seq.length s));
  match parse_header cid_len last Seq.(format_header h @| c) with
  | H_Failure -> ()
  | H_Success h' c' -> assert (h == h'); assert (c `Seq.equal` c')

#push-options "--z3rlimit 256"

let lemma_header_parsing_safe
  cid_len last b1 b2
= match parse_header cid_len last b1 with
  | H_Failure -> ()
  | H_Success h1 c1 ->
    let consumed = Seq.length b1 - Seq.length c1 in
    assert (Some? (parse (lp_parse_header (U32.uint_to_t cid_len) (U64.uint_to_t last)) b1)); //  == Some (h1, consumed));
    let Some (h1', consumed') = parse (lp_parse_header (U32.uint_to_t cid_len) (U64.uint_to_t last)) b1 in
    assert (h1 == h1');
    let consumed' : consumed_length b1 = consumed' in
    assert (consumed' <= Seq.length b1);
    assert (c1 == Seq.slice b1 consumed' (Seq.length b1));
    assert (consumed == consumed');
    parse_injective (lp_parse_header (U32.uint_to_t cid_len) (U64.uint_to_t last)) b1 b2;
    Seq.lemma_split b1 consumed;
    assert (parse_header cid_len last b2 == H_Success h1 c1);
    Seq.lemma_split b2 consumed;
    assert (b1 == b2)
    
#pop-options

let header_len'
  (h: header)
: GTot nat
= match h with
  | MShort spin phase cid packet_number_length pn ->
    1 + FB.length cid + U32.v packet_number_length
  | MLong version dcid scid spec ->
    7 + FB.length dcid + FB.length scid +
    begin match spec with
    | MInitial token payload_length packet_number_length pn ->
      Seq.length (serialize (serialize_bounded_varint 0 token_max_len) (FB.len token)) + FB.length token + Seq.length (serialize serialize_varint (payload_length `U64.add` Cast.uint32_to_uint64 packet_number_length)) + U32.v packet_number_length
    | MZeroRTT payload_length packet_number_length pn ->
      Seq.length (serialize serialize_varint (payload_length `U64.add` Cast.uint32_to_uint64 packet_number_length)) + U32.v packet_number_length
    | MHandshake payload_length packet_number_length pn ->
      Seq.length (serialize serialize_varint (payload_length `U64.add` Cast.uint32_to_uint64 packet_number_length)) + U32.v packet_number_length
    | MRetry unused odcid ->
      1 + FB.length odcid
    end

let length_serialize_common_long
  (version: U32.t)
  (dcid: vlbytes 0 20)
  (scid: vlbytes 0 20)
: Lemma
  (Seq.length (serialize serialize_common_long (version, (dcid, scid))) == 6 + FB.length dcid + FB.length scid)
= serialize_nondep_then_eq serialize_u32 (serialize_bounded_vlbytes 0 20 `serialize_nondep_then` serialize_bounded_vlbytes 0 20) (version, (dcid, scid));
  serialize_length serialize_u32 version;
  serialize_nondep_then_eq (serialize_bounded_vlbytes 0 20) (serialize_bounded_vlbytes 0 20) (dcid, scid);
  length_serialize_bounded_vlbytes 0 20 dcid;
  length_serialize_bounded_vlbytes 0 20 scid

let length_serialize_payload_length_pn
  (last: last_packet_number_t)
  (pn_length: packet_number_length_t)
  (payload_and_pn_length: parse_filter_refine (payload_and_pn_length_prop pn_length))
  (pn: packet_number_t last pn_length)
: Lemma
  (Seq.length (serialize (serialize_payload_length_pn last pn_length) (payload_and_pn_length, pn)) == Seq.length (serialize serialize_varint payload_and_pn_length) + U32.v pn_length)
= serialize_nondep_then_eq (serialize_varint `serialize_filter` payload_and_pn_length_prop pn_length) (serialize_packet_number last pn_length) (payload_and_pn_length, pn);
  serialize_length (serialize_packet_number last pn_length) pn

#push-options "--z3rlimit 1024 --query_stats --max_fuel 4 --initial_fuel 4"

#restart-solver

let header_len'_correct'_short
  (short_dcid_len: short_dcid_len_t)
  (last: last_packet_number_t)
  (spin: bool)
  (key_phase: bool)
  (dcid: vlbytes 0 20)
  (packet_number_length: packet_number_length_t)
  (packet_number: uint62_t)
: Lemma
  (requires (let h = MShort spin key_phase dcid packet_number_length packet_number in
    parse_header_prop short_dcid_len last h
  ))
  (ensures (
    let h = MShort spin key_phase dcid packet_number_length packet_number in
    header_len' h == Seq.length (serialize (serialize_header short_dcid_len last) h)
  ))
= 
  let h = MShort spin key_phase dcid packet_number_length packet_number in
  serialize_header_eq short_dcid_len last h;
  let tg = first_byte_of_header short_dcid_len last h in
  let x = synth_bitsum'_recip first_byte tg in
  serialize_length LI.serialize_u8 x;
  assert_norm (first_byte_of_header short_dcid_len last (MShort spin key_phase dcid packet_number_length packet_number) == (| Short, (| (), ((if spin then 1uy else 0uy), (| (), ((if key_phase then 1uy else 0uy), (| packet_number_length, () |) ) |) ) |) |) );
  assert_norm (bitsum'_key_of_t first_byte (first_byte_of_header short_dcid_len last (MShort spin key_phase dcid packet_number_length packet_number)) == (| Short, (| (), (| (), (| packet_number_length, () |) |) |) |) ) ;
  serialize_nondep_then_eq (serialize_weaken (strong_parser_kind 0 20 None) (serialize_flbytes (U32.v short_dcid_len))) (serialize_packet_number last packet_number_length) (dcid, packet_number);
  serialize_length (serialize_flbytes (U32.v short_dcid_len)) dcid;
  serialize_length (serialize_packet_number last packet_number_length) packet_number

#restart-solver

let header_len'_correct'_long_initial
  (short_dcid_len: short_dcid_len_t)
  (last: last_packet_number_t)
  (version: U32.t)
  (dcid: vlbytes 0 20)
  (scid: vlbytes 0 20)
  (token: vlbytes 0 token_max_len)
  (payload_length: uint62_t)
  (packet_number_length: packet_number_length_t { U64.v payload_length + U32.v packet_number_length < pow2 62 })
  (packet_number: uint62_t)
: Lemma
  (requires (
    let h = MLong version dcid scid (MInitial token payload_length packet_number_length packet_number) in
    parse_header_prop short_dcid_len last h
  ))
  (ensures (
    let h = MLong version dcid scid (MInitial token payload_length packet_number_length packet_number) in
    header_len' h == Seq.length (serialize (serialize_header short_dcid_len last) h)
  ))
=
  let h = MLong version dcid scid (MInitial token payload_length packet_number_length packet_number) in
  serialize_header_eq short_dcid_len last h;
  let tg = first_byte_of_header short_dcid_len last h in
  let x = synth_bitsum'_recip first_byte tg in
  serialize_length LI.serialize_u8 x;
  let kt : bitsum'_key_type first_byte = (| Long, (| (), (| Initial, (| (), (| packet_number_length, () |) |) |) |) |) in
  assert_norm (first_byte_of_header short_dcid_len last (MLong version dcid scid (MInitial token payload_length packet_number_length packet_number)) == (| Long, (| (), (| Initial, (| (), (| packet_number_length, () |) |) |) |) |) );
  assert_norm (bitsum'_key_of_t first_byte (first_byte_of_header short_dcid_len last (MLong version dcid scid (MInitial token payload_length packet_number_length packet_number))) == kt );
  let plpnl : parse_filter_refine (payload_and_pn_length_prop packet_number_length) = payload_length `U64.add` Cast.uint32_to_uint64 packet_number_length in
  let pn : packet_number_t last packet_number_length = packet_number in
  length_serialize_nondep_then serialize_common_long (serialize_bounded_vlgenbytes 0 token_max_len (serialize_bounded_varint 0 token_max_len) `serialize_nondep_then` serialize_payload_length_pn last packet_number_length) (version, (dcid, scid)) (token, (plpnl, pn));
  length_serialize_common_long version dcid scid;
  length_serialize_nondep_then (serialize_bounded_vlgenbytes 0 token_max_len (serialize_bounded_varint 0 token_max_len)) (serialize_payload_length_pn last packet_number_length) token (plpnl, pn);
  length_serialize_bounded_vlgenbytes 0 token_max_len (serialize_bounded_varint 0 token_max_len) token;
  length_serialize_payload_length_pn last packet_number_length plpnl pn

let header_len'_correct'_long_handshake
  (short_dcid_len: short_dcid_len_t)
  (last: last_packet_number_t)
  (version: U32.t)
  (dcid: vlbytes 0 20)
  (scid: vlbytes 0 20)
  (payload_length: uint62_t)
  (packet_number_length: packet_number_length_t { U64.v payload_length + U32.v packet_number_length < pow2 62 })
  (packet_number: uint62_t)
: Lemma
  (requires (
    let h = MLong version dcid scid (MHandshake payload_length packet_number_length packet_number) in
    parse_header_prop short_dcid_len last h
  ))
  (ensures (
    let h = MLong version dcid scid (MHandshake payload_length packet_number_length packet_number) in
    header_len' h == Seq.length (serialize (serialize_header short_dcid_len last) h)
  ))
=
  let h = MLong version dcid scid (MHandshake payload_length packet_number_length packet_number) in
  serialize_header_eq short_dcid_len last h;
  let tg = first_byte_of_header short_dcid_len last h in
  let x = synth_bitsum'_recip first_byte tg in
  serialize_length LI.serialize_u8 x;
  let kt : bitsum'_key_type first_byte = (| Long, (| (), (| Handshake, (| (), (| packet_number_length, () |) |) |) |) |) in
  assert_norm (first_byte_of_header short_dcid_len last (MLong version dcid scid (MHandshake payload_length packet_number_length packet_number)) == (| Long, (| (), (| Handshake, (| (), (| packet_number_length, () |) |) |) |) |) );
  assert_norm (bitsum'_key_of_t first_byte (first_byte_of_header short_dcid_len last (MLong version dcid scid (MHandshake payload_length packet_number_length packet_number))) == kt );
  let plpnl : parse_filter_refine (payload_and_pn_length_prop packet_number_length) = payload_length `U64.add` Cast.uint32_to_uint64 packet_number_length in
  let pn : packet_number_t last packet_number_length = packet_number in
  length_serialize_nondep_then serialize_common_long (serialize_payload_length_pn last packet_number_length) (version, (dcid, scid)) (plpnl, pn);
  length_serialize_common_long version dcid scid;
  length_serialize_payload_length_pn last packet_number_length plpnl pn

let header_len'_correct'_long_zeroRTT
  (short_dcid_len: short_dcid_len_t)
  (last: last_packet_number_t)
  (version: U32.t)
  (dcid: vlbytes 0 20)
  (scid: vlbytes 0 20)
  (payload_length: uint62_t)
  (packet_number_length: packet_number_length_t { U64.v payload_length + U32.v packet_number_length < pow2 62 })
  (packet_number: uint62_t)
: Lemma
  (requires (
    let h = MLong version dcid scid (MZeroRTT payload_length packet_number_length packet_number) in
    parse_header_prop short_dcid_len last h
  ))
  (ensures (
    let h = MLong version dcid scid (MZeroRTT payload_length packet_number_length packet_number) in
    header_len' h == Seq.length (serialize (serialize_header short_dcid_len last) h)
  ))
=
  let h = MLong version dcid scid (MZeroRTT payload_length packet_number_length packet_number) in
  serialize_header_eq short_dcid_len last h;
  let tg = first_byte_of_header short_dcid_len last h in
  let x = synth_bitsum'_recip first_byte tg in
  serialize_length LI.serialize_u8 x;
  let kt : bitsum'_key_type first_byte = (| Long, (| (), (| ZeroRTT, (| (), (| packet_number_length, () |) |) |) |) |) in
  assert_norm (first_byte_of_header short_dcid_len last (MLong version dcid scid (MZeroRTT payload_length packet_number_length packet_number)) == (| Long, (| (), (| ZeroRTT, (| (), (| packet_number_length, () |) |) |) |) |) );
  assert_norm (bitsum'_key_of_t first_byte (first_byte_of_header short_dcid_len last (MLong version dcid scid (MZeroRTT payload_length packet_number_length packet_number))) == kt );
  let plpnl : parse_filter_refine (payload_and_pn_length_prop packet_number_length) = payload_length `U64.add` Cast.uint32_to_uint64 packet_number_length in
  let pn : packet_number_t last packet_number_length = packet_number in
  length_serialize_nondep_then serialize_common_long (serialize_payload_length_pn last packet_number_length) (version, (dcid, scid)) (plpnl, pn);
  length_serialize_common_long version dcid scid;
  length_serialize_payload_length_pn last packet_number_length plpnl pn

let header_len'_correct'_long_retry
  (short_dcid_len: short_dcid_len_t)
  (last: last_packet_number_t)
  (version: U32.t)
  (dcid: vlbytes 0 20)
  (scid: vlbytes 0 20)
  (unused: bitfield 4)
  (odcid: vlbytes 0 20)
: Lemma
  (requires (
    let h = MLong version dcid scid (MRetry unused odcid) in
    parse_header_prop short_dcid_len last h
  ))
  (ensures (
    let h = MLong version dcid scid (MRetry unused odcid) in
    header_len' h == Seq.length (serialize (serialize_header short_dcid_len last) h)
  ))
=
  let h = MLong version dcid scid (MRetry unused odcid) in
  serialize_header_eq short_dcid_len last h;
  let tg = first_byte_of_header short_dcid_len last h in
  let x = synth_bitsum'_recip first_byte tg in
  serialize_length LI.serialize_u8 x;
  let kt : bitsum'_key_type first_byte = (| Long, (| (), (| Retry, () |) |) |) in
  assert_norm (first_byte_of_header short_dcid_len last (MLong version dcid scid (MRetry unused odcid)) == (| Long, (| (), (| Retry, (unused, ()) |) |) |) );
  assert_norm (bitsum'_key_of_t first_byte (first_byte_of_header short_dcid_len last (MLong version dcid scid (MRetry unused odcid))) == kt );
  length_serialize_nondep_then serialize_common_long (serialize_bounded_vlbytes 0 20) (version, (dcid, scid)) odcid;
  length_serialize_common_long version dcid scid;
  length_serialize_bounded_vlbytes 0 20 odcid

let header_len'_correct'
  (short_dcid_len: short_dcid_len_t)
  (last: last_packet_number_t)
  (h: header' short_dcid_len last)
: Lemma
  (header_len' h == Seq.length (serialize (serialize_header short_dcid_len last) h))
= match h with
  | MShort spin key_phase dcid packet_number_length packet_number ->
    header_len'_correct'_short short_dcid_len last spin key_phase dcid packet_number_length packet_number
  | MLong version dcid scid spec ->
    begin match spec with
    | MInitial token payload_length packet_number_length packet_number ->
      header_len'_correct'_long_initial short_dcid_len last version dcid scid token payload_length packet_number_length packet_number
    | MHandshake payload_length packet_number_length packet_number ->
      header_len'_correct'_long_handshake short_dcid_len last version dcid scid payload_length packet_number_length packet_number
    | MZeroRTT payload_length packet_number_length packet_number ->
      header_len'_correct'_long_zeroRTT short_dcid_len last version dcid scid payload_length packet_number_length packet_number
    | MRetry unused odcid ->
      header_len'_correct'_long_retry short_dcid_len last version dcid scid unused odcid
    end

#pop-options

let header_len'_correct
  (h: header)
: Lemma
  (header_len' h == header_len h)
= 
  let short_dcid_len = U32.uint_to_t (dcid_len h) in
  let last = last_packet_number h in
  header_len'_correct' short_dcid_len last h
