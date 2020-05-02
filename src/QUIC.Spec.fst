module QUIC.Spec

open QUIC.Spec.Lemmas
open QUIC.Spec.Header.Base

module Seq = QUIC.Secret.Seq
module U32 = FStar.UInt32
module U8 = FStar.UInt8
module H = Spec.Agile.Hash
module HD = Spec.Hash.Definitions
module Cipher = Spec.Agile.Cipher
module AEAD = Spec.Agile.AEAD
module HKDF = Spec.Agile.HKDF
module Parse = QUIC.Spec.Header.Parse
module H = QUIC.Spec.Header
module Secret = QUIC.Secret.Int

(*
// two lines to break the abstraction of UInt8 used for
// side-channel protection (useless here). Copied from mitls-fstar
// src/tls/declassify.fst (branch dev)
friend Lib.IntTypes
let declassify : squash (Lib.IntTypes.uint8 == UInt8.t)= ()
*)

/// encryption of a packet

let encrypt a k siv hpk h plain =
  let open FStar.Endianness in
  let aad = Parse.format_header h in
  let iv =
    if is_retry h
    then siv
    else 
      // packet number bytes
      let pn_len = Secret.v (pn_length h) - 1 in
      let seqn = packet_number h in
      let _ = assert_norm(pow2 62 < pow2 (8 `op_Multiply` 12)) in
      let pnb = FStar.Endianness.n_to_be 12 (Secret.v seqn) in
      Seq.seq_hide #Secret.U8 (xor_inplace pnb (Seq.seq_reveal siv) 0)
  in
  let cipher = if is_retry h then plain else Seq.seq_reveal (AEAD.encrypt #a k iv (Seq.seq_hide aad) (Seq.seq_hide plain)) in
  H.header_encrypt a hpk h cipher

#restart-solver

let decrypt
  a k static_iv hpk last cid_len packet
= Failure

(*

noextract
type header_decrypt_aux_t = {
  is_short: bool;
  is_retry: (is_retry: bool { is_retry ==> ~ (is_short) });
  packet: packet;
  pn_offset: (if is_retry then unit else nat);
  pn_len: (if is_retry then unit else (pn_len: nat2 {pn_offset + pn_len + 1 <= Seq.length packet}));
}

let header_decrypt_aux
  (a:ea)
  (hpk: lbytes (ae_keysize a))
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
      match putative_pn_offset cid_len packet with
      | None -> None
      | Some pn_offset ->
        let sample_offset = pn_offset + 4 in
        if sample_offset + 16 > Seq.length packet
        then None
        else begin
          let sample = Seq.slice packet sample_offset (sample_offset+16) in
          let mask = block_of_sample (AEAD.cipher_alg_of_supported_alg a) hpk sample in
          (* mask the least significant bits of the first byte *)
          let protected_bits = if is_short then 5 else 4 in
          let f' = BF.set_bitfield (U8.v f) 0 protected_bits (BF.get_bitfield (U8.v f `FStar.UInt.logxor` U8.v (Seq.index mask 0)) 0 protected_bits) in
          let packet' = Seq.cons (U8.uint_to_t f') (Seq.slice packet 1 (Seq.length packet)) in
          (* now the packet number length is available, so mask the packet number *)
          let pn_len = BF.get_bitfield f' 0 2 in
          let pnmask = and_inplace (Seq.slice mask 1 (pn_len + 2)) (pn_sizemask_naive pn_len) 0 in
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
      Some? (putative_pn_offset cid_len packet) /\
      putative_pn_offset cid_len r.packet == putative_pn_offset cid_len packet /\ (
      let Some pn_offset = putative_pn_offset cid_len packet in
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
    let Some pn_offset = putative_pn_offset cid_len packet in
    let sample_offset = pn_offset + 4 in
    let sample = Seq.slice packet sample_offset (sample_offset+16) in
    let mask = block_of_sample (AEAD.cipher_alg_of_supported_alg a) hpk sample in
    (* mask the least significant bits of the first byte *)
    let protected_bits = if is_short then 5 else 4 in
    let bf = BF.get_bitfield (U8.v f `FStar.UInt.logxor` U8.v (Seq.index mask 0)) 0 protected_bits in
    let f' = BF.set_bitfield (U8.v f) 0 protected_bits bf in
    let packet' = Seq.cons (U8.uint_to_t f') (Seq.slice packet 1 (Seq.length packet)) in
    (* now the packet number length is available, so mask the packet number *)
    let pn_len = BF.get_bitfield f' 0 2 in
    let pnmask = and_inplace (Seq.slice mask 1 (pn_len + 2)) (pn_sizemask_naive pn_len) 0 in
    assert (r.packet == xor_inplace packet' pnmask pn_offset);
    pointwise_op_slice_other U8.logxor packet' pnmask pn_offset 0 1;
    pointwise_op_slice_other U8.logxor packet' pnmask pn_offset 1 pn_offset;
    pointwise_op_slice_other U8.logxor packet' pnmask pn_offset (pn_offset + pn_len + 1) (Seq.length packet);
    BF.get_bitfield_set_bitfield_other (U8.v f) 0 protected_bits bf protected_bits 8;
    BF.get_bitfield_set_bitfield_other (U8.v f) 0 protected_bits bf 7 8;
    assert (Seq.index r.packet 0 == Seq.index (Seq.slice packet' 0 1) 0);
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
  (cid_len: nat { cid_len <= 20 })
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
    header_len h <= Seq.length packet /\
    Seq.length r.packet == Seq.length packet /\
    Seq.length packet > 0 /\ (
    r.is_short == MShort? h /\
    r.is_retry == is_retry h /\
    rem' `Seq.equal` Seq.slice packet (header_len h) (Seq.length packet) /\ (
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

(* A constant-time specification of header_decrypt_aux which does not test or truncate on pn_len *)

let header_decrypt_aux_ct
  (a:ea)
  (hpk: lbytes (ae_keysize a))
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
      match putative_pn_offset cid_len packet with
      | None -> None
      | Some pn_offset ->
        let sample_offset = pn_offset + 4 in
        if sample_offset + 16 > Seq.length packet
        then None
        else begin
          let sample = Seq.slice packet sample_offset (sample_offset+16) in
          let mask = block_of_sample (AEAD.cipher_alg_of_supported_alg a) hpk sample in
          (* mask the least significant bits of the first byte *)
          let protected_bits = if is_short then 5 else 4 in
          let f' = BF.set_bitfield (U8.v f) 0 protected_bits (BF.get_bitfield (U8.v f `FStar.UInt.logxor` U8.v (Seq.index mask 0)) 0 protected_bits) in
          let packet' = Seq.cons (U8.uint_to_t f') (Seq.slice packet 1 (Seq.length packet)) in
          (* now the packet number length is available, so mask the packet number *)
          let pn_len = BF.get_bitfield f' 0 2 in
          let pnmask = and_inplace (Seq.slice mask 1 5) (pn_sizemask_ct pn_len) 0 in
          let packet'' = xor_inplace packet' pnmask pn_offset in
          Some ({
            is_short = is_short;
            is_retry = is_retry;
            packet = packet'';
            pn_offset = pn_offset;
            pn_len = pn_len;
          })
        end

#push-options "--z3rlimit 16"

let header_decrypt_aux_ct_correct
  (a:ea)
  (hpk: lbytes (ae_keysize a))
  (cid_len: nat { cid_len <= 20 })
  (packet: packet)
: Lemma
  (header_decrypt_aux_ct a hpk cid_len packet == header_decrypt_aux a hpk cid_len packet)
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
      match putative_pn_offset cid_len packet with
      | None -> ()
      | Some pn_offset ->
        let sample_offset = pn_offset + 4 in
        if sample_offset + 16 > Seq.length packet
        then ()
        else begin
          let sample = Seq.slice packet sample_offset (sample_offset+16) in
          let mask = block_of_sample (AEAD.cipher_alg_of_supported_alg a) hpk sample in
          (* mask the least significant bits of the first byte *)
          let protected_bits = if is_short then 5 else 4 in
          let f' = BF.set_bitfield (U8.v f) 0 protected_bits (BF.get_bitfield (U8.v f `FStar.UInt.logxor` U8.v (Seq.index mask 0)) 0 protected_bits) in
          let packet' = Seq.cons (U8.uint_to_t f') (Seq.slice packet 1 (Seq.length packet)) in
          (* now the packet number length is available, so mask the packet number *)
          let pn_len = BF.get_bitfield f' 0 2 in
          let pnmask_ct = and_inplace (Seq.slice mask 1 5) (pn_sizemask_ct pn_len) 0 in
          let pnmask_naive = and_inplace (Seq.slice mask 1 (pn_len + 2)) (pn_sizemask_naive pn_len) 0 in
          pointwise_op_split U8.logand (Seq.slice mask 1 5) (pn_sizemask_ct pn_len) 0 (pn_len + 1);
          assert (pnmask_naive `Seq.equal` Seq.slice pnmask_ct 0 (pn_len + 1));
          let r = packet' in
          Seq.lemma_split r (pn_offset + pn_len + 1);
          pointwise_op_split U8.logxor r pnmask_ct pn_offset (pn_offset + pn_len + 1);
          pointwise_op_split U8.logxor r pnmask_naive pn_offset (pn_offset + pn_len + 1);
          pointwise_op_empty U8.logxor (Seq.slice r (pn_offset + pn_len + 1) (Seq.length r)) (Seq.slice pnmask_naive (pn_len + 1) (Seq.length pnmask_naive)) 0;
          xor_inplace_zero (Seq.slice r (pn_offset + pn_len + 1) (Seq.length r)) (Seq.slice pnmask_ct (pn_len + 1) 4)
            (fun i ->
              and_inplace_zero
                (Seq.slice mask (pn_len + 2) 5)
                (Seq.slice (pn_sizemask_ct pn_len) (pn_len + 1) 4)
                (fun j -> index_pn_sizemask_ct_right pn_len (j + (pn_len + 1)))
                i
            )
            0
        end

let header_decrypt a hpk cid_len last packet =
  let open FStar.Math.Lemmas in
  if Seq.length packet = 0
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
          H_Success h Seq.empty rem'
        else if has_payload_length h && Seq.length rem' < U64.v (payload_length h)
        then H_Failure
        else
          let clen = if has_payload_length h then U64.v (payload_length h) else Seq.length rem' in
          if 19 <= clen && clen < max_cipher_length
          then
            let c : cbytes = Seq.slice rem' 0 clen in
            let rem = Seq.slice rem' clen (Seq.length rem') in
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
  (cid_len: nat { cid_len <= 20 /\ (MShort? h ==> cid_len == dcid_len h) })
  (c: cbytes' (is_retry h)) // { has_payload_length h ==> U64.v (payload_length h) == Seq.length c } ->
: Lemma
  (let r' = header_decrypt_aux a k cid_len (header_encrypt a k h c) in
   Some? r' /\ (
   let Some r = r' in
   r.packet `Seq.equal` (format_header h `Seq.append` c) /\
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
    let format = format_header h `Seq.append` c in
    let packet = header_encrypt a k h c in
    let Some r = header_decrypt_aux a k cid_len packet in
    putative_pn_offset_correct h cid_len;
    let pn_offset = pn_offset h in
    let pn_len = U32.v (pn_length h) - 1 in
    let sample = Seq.slice c (3-pn_len) (19-pn_len) in
    assert (sample `Seq.equal` Seq.slice packet (pn_offset + 4) (pn_offset + 20));
    assert ((r.pn_offset <: nat) == pn_offset);
    let mask = block_of_sample (AEAD.cipher_alg_of_supported_alg a) k sample in
    let protected_bits = if MShort? h then 5 else 4 in
    assert (protected_bits == (if r.is_short then 5 else 4));
    let f = Seq.index format 0 in
    let pb_value = BF.get_bitfield (U8.v f `FStar.UInt.logxor` U8.v (Seq.index mask 0)) 0 protected_bits in
    let f0 = BF.set_bitfield (U8.v f) 0 protected_bits pb_value in
    assert (U8.uint_to_t f0 == Seq.index packet 0);
    let pb_value' = BF.get_bitfield (f0 `FStar.UInt.logxor` U8.v (Seq.index mask 0)) 0 protected_bits in
    let f1 = BF.set_bitfield f0 0 protected_bits pb_value' in
    let packet1 = Seq.cons (U8.uint_to_t f1) (Seq.slice packet 1 (Seq.length packet)) in
    let pnmask' = and_inplace (Seq.slice mask 1 (r.pn_len + 2)) (pn_sizemask_naive r.pn_len) 0 in
    assert (r.packet == xor_inplace packet1 pnmask' pn_offset);
    pointwise_op_slice_other U8.logxor packet1 pnmask' pn_offset 0 1;
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
    format_header_pn_length h;
    assert ((r.pn_len <: nat) == pn_len);
    assert (pnmask' == and_inplace (Seq.slice mask 1 (pn_len + 2)) (pn_sizemask_naive pn_len) 0);
    xor_inplace_involutive format pnmask' pn_offset;
    let packet0 = xor_inplace format pnmask' pn_offset in
    pointwise_op_slice_other U8.logxor format pnmask' pn_offset 0 1;
    assert (Seq.index packet0 0 == Seq.index (Seq.slice format 0 1) 0);
    assert (packet == Seq.cons (U8.uint_to_t f0) (Seq.slice packet0 1 (Seq.length packet0)));
    assert (packet1 `Seq.equal` Seq.cons (U8.uint_to_t f1) (Seq.slice packet0 1 (Seq.length packet0)));
    assert (packet1 `Seq.equal` packet0);
    assert (r.packet `Seq.equal` format);
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
let hide (x:bytes) : Pure (Seq.seq Lib.IntTypes.uint8)
  (requires True) (ensures fun r -> Seq.length x == Seq.length r)
  = Seq.init (Seq.length x) (fun i -> Lib.IntTypes.secret #Lib.IntTypes.U8 (Seq.index x i))

inline_for_extraction private
let reveal (x:Seq.seq Lib.IntTypes.uint8) : Pure bytes
  (requires True) (ensures fun r -> Seq.length x == Seq.length r)
  = Seq.init (Seq.length x) (fun i -> U8.uint_to_t (Lib.IntTypes.uint_v (Seq.index x i)))
*)

#pop-options

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
      let npn : lbytes (1+pn_len) = Seq.slice pnb (11 - pn_len) 12 in
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
    let clen = Seq.length cipher in
    assert (19 <= clen && clen < max_cipher_length);
    AEAD.correctness #a k iv aad plain
  end

#pop-options

#pop-options
