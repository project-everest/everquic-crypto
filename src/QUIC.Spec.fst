module QUIC.Spec
open QUIC.Spec.Lemmas
open QUIC.Parse

module S = FStar.Seq
module U32 = FStar.UInt32
module U8 = FStar.UInt8
module H = Spec.Agile.Hash
module HD = Spec.Hash.Definitions
module Cipher = Spec.Agile.Cipher
module AEAD = Spec.Agile.AEAD
module HKDF = Spec.Agile.HKDF

#set-options "--max_fuel 0 --max_ifuel 0"

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
let pn_sizemask' (pn_len:nat2) : lbytes 4 =
  let open FStar.Endianness in
  FStar.Math.Lemmas.pow2_lt_compat 32 (24 - (8 `op_Multiply` pn_len));
  n_to_be 4 (pow2 32 - pow2 (24 - (8 `op_Multiply` pn_len)))

inline_for_extraction
let pn_sizemask (pn_len:nat2) : lbytes (pn_len + 1) =
  S.slice (pn_sizemask' pn_len) 0 (pn_len + 1)

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
    let pnmask = and_inplace (S.slice mask 1 (pn_len + 2)) (pn_sizemask pn_len) 0 in
    let f = S.index r 0 in
    let protected_bits = if MShort? h then 5 else 4 in
    let f' = BF.set_bitfield (U8.v f) 0 protected_bits (BF.get_bitfield (U8.v f `FStar.UInt.logxor` U8.v (S.index mask 0)) 0 protected_bits) in
    let r = xor_inplace r pnmask pn_offset in
    let r = S.cons (U8.uint_to_t f') (S.slice r 1 (S.length r)) in
    r

module U64 = FStar.UInt64

#push-options "--max_ifuel 1 --z3rlimit 32"

let header_decrypt_aux
  

let header_decrypt a hpk cid_len last packet =
  let open FStar.Math.Lemmas in
  if S.length packet = 0
  then H_Failure
  else
    let f = S.index packet 0 in
    let is_short = (BF.get_bitfield (U8.v f) 7 8 = 0) in
    let is_retry = not is_short && BF.get_bitfield (U8.v f) 4 6 = 3 in
    if is_retry
    then
      (* retry: no header protection needed, and no payload *)
      match parse_header cid_len last packet with
      | QUIC.Parse.H_Failure -> H_Failure
      | QUIC.Parse.H_Success h rem ->
        format_header_is_short h;
        format_header_is_retry h;
        lemma_header_parsing_post cid_len last packet;
        H_Success h S.empty rem
    else
      match putative_pn_offset cid_len packet with
      | None -> H_Failure
      | Some pn_offset ->
        let sample_offset = pn_offset + 4 in
        if sample_offset + 16 > S.length packet
        then H_Failure
        else begin
          let sample = S.slice packet sample_offset (sample_offset+16) in
          let mask = block_of_sample (AEAD.cipher_alg_of_supported_alg a) hpk sample in
          (* mask the least significant bits of the first byte *)
          let protected_bits = if is_short then 5 else 4 in
          let f' = BF.set_bitfield (U8.v f) 0 protected_bits (BF.get_bitfield (U8.v f `FStar.UInt.logxor` U8.v (S.index mask 0)) 0 protected_bits) in
          let packet' = S.cons (U8.uint_to_t f') (S.slice packet 1 (S.length packet)) in
          (* now the packet number length is available, so mask the packet number *)
          let pn_len = BF.get_bitfield f' 0 2 in
          let pnmask = and_inplace (S.slice mask 1 (pn_len + 2)) (pn_sizemask pn_len) 0 in
          let packet'' = xor_inplace packet' pnmask pn_offset in
          match parse_header cid_len last packet'' with
          | QUIC.Parse.H_Failure -> H_Failure
          | QUIC.Parse.H_Success h rem' ->
            lemma_header_parsing_post cid_len last packet'';
            QUIC.Spec.Lemmas.pointwise_op_slice_other U8.logxor packet' pnmask pn_offset (pn_offset + pn_len + 1) (S.length packet'');
            QUIC.Spec.Lemmas.pointwise_op_slice_other U8.logxor packet' pnmask pn_offset 0 1;
            BF.get_bitfield_set_bitfield_other (U8.v f) 0 protected_bits 7 8;
            if is_short
            if QUIC.Spec.Base.is_retry h
            then H_Failure // should not happen, we can prove it just as above, but it is not worth it
            else if has_payload_length h && S.length rem' < U64.v (payload_length h)
            then H_Failure
            else
              let clen = if has_payload_length h then U64.v (payload_length h) else S.length rem' in
              if 19 <= clen && clen < max_cipher_length
              then
                let c : cbytes = S.slice rem' 0 clen in
                let rem = S.slice rem' clen (S.length rem') in
                if pn_offset = QUIC.Parse.pn_offset h && pn_len = U32.v (QUIC.Parse.pn_length h) && pn_offset + pn_len + 1 = header_len h
                then
                  H_Success h c rem
                else H_Failure // this should not happen, as above
              else
                H_Failure
        end

#pop-options

#push-options "--z3rlimit 128"

let lemma_header_encryption_correct a k h cid_len last c =
  format_header_is_short h;
  format_header_is_retry h;
  lemma_header_parsing_correct h c cid_len last;
  if is_retry h
  then begin
    let packet = format_header h in
    assert (S.length packet > 0)
  end else begin
    let format' = format_header h in
    let format = format' `S.append` c in
    let packet = header_encrypt a k h c in
    putative_pn_offset_correct h cid_len;
    putative_pn_offset_frame cid_len format' format;
    let pn_offset = pn_offset h in
    let pn_len = U32.v (pn_length h) - 1 in
    let sample = S.slice c (3-pn_len) (19-pn_len) in
    let mask = block_of_sample (AEAD.cipher_alg_of_supported_alg a) k sample in
    let pnmask = and_inplace (S.slice mask 1 5) (pn_sizemask pn_len) 0 in
    let f = S.index format 0 in
    let protected_bits = if MShort? h then 5 else 4 in
    let pb_value = BF.get_bitfield (U8.v f `FStar.UInt.logxor` U8.v (S.index mask 0)) 0 protected_bits in
    pointwise_op_slice_other U8.logxor format pnmask pn_offset 1 pn_offset;
    let f_ = S.index packet 0 in
    assert (U8.v f_ == BF.set_bitfield (U8.v f) 0 protected_bits pb_value);
    let packet1 = xor_inplace format pnmask pn_offset in
    assert (packet == S.cons f_ (S.slice packet1 1 (S.length packet1)));
    BF.get_bitfield_set_bitfield_other (U8.v f) 0 protected_bits pb_value 7 8;
    assert (MShort? h == (BF.get_bitfield (U8.v f_) 7 8 = 0));
    begin if not (MShort? h) then
      BF.get_bitfield_set_bitfield_other (U8.v f) 0 protected_bits pb_value 4 6
    end;
    assert (is_retry h == (not (MShort? h) && BF.get_bitfield (U8.v f) 4 6 = 3));
    BF.get_bitfield_set_bitfield_other (U8.v f) 0 protected_bits pb_value protected_bits 8;
    putative_pn_offset_frame cid_len format packet;
    assert (0 < pn_offset /\ pn_offset <= S.length packet);
    let put' = putative_pn_offset cid_len packet in
    assert (Some? put');
    assert ((Some?.v put' <: nat) == pn_offset);
    let sample_offset = pn_offset + 4 in
    assert (sample_offset + 16 <= S.length packet);
    pointwise_op_slice_other U8.logxor format pnmask pn_offset sample_offset (sample_offset + 16);
    assert (sample `S.equal` S.slice format sample_offset (sample_offset + 16));
    assert (sample `S.equal` S.slice packet sample_offset (sample_offset + 16));
    let pb_value_ = BF.get_bitfield (U8.v f_ `FStar.UInt.logxor` U8.v (S.index mask 0)) 0 protected_bits in
    let f'_ = BF.set_bitfield (U8.v f_) 0 protected_bits pb_value_ in
    let packet' = S.cons (U8.uint_to_t f'_) (S.slice packet 1 (S.length packet)) in
    BF.get_bitfield_logxor (U8.v f) (U8.v (S.index mask 0)) 0 protected_bits;
    BF.get_bitfield_logxor (U8.v f_) (U8.v (S.index mask 0)) 0 protected_bits;
    BF.get_bitfield_set_bitfield_same (U8.v f) 0 protected_bits pb_value;
    assert (BF.get_bitfield (U8.v f_) 0 protected_bits == pb_value);
    BF.get_bitfield_set_bitfield_same (U8.v f_) 0 protected_bits pb_value_;
    BF.get_bitfield_set_bitfield_other (U8.v f_) 0 protected_bits pb_value_ protected_bits 8;
    let bfmask = BF.get_bitfield (U8.v (S.index mask 0)) 0 protected_bits in
    FStar.UInt.logxor_inv (BF.get_bitfield (U8.v f) 0 protected_bits) bfmask;
    assert (pb_value_ == BF.get_bitfield (U8.v f) 0 protected_bits);
    BF.get_bitfield_partition_2 protected_bits (U8.v f) f'_;
    assert (f'_ == U8.v f);
    (* now the packet number length is available, so mask the packet number *)
    format_header_pn_length h;
    assert (pn_len == BF.get_bitfield f'_ 0 2);
    let packet'' = xor_inplace packet' pnmask pn_offset in
    pointwise_op_slice_other U8.logxor format pnmask pn_offset 0 1;
    assert (S.index packet1 0 == S.index (S.slice packet1 0 1) 0);
    assert (packet' `S.equal` packet1);
    xor_inplace_involutive format pnmask pn_offset;
    pointwise_op_slice_other U8.logxor packet1 pnmask pn_offset 0 1;
    assert (S.index packet'' 0 == S.index (S.slice packet'' 0 1) 0);
    assert (format `S.equal` packet'')
  end

#pop-options

(* not useful anymore by using declassify below

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

// two lines to break the abstraction of UInt8 used for
// side-channel protection (useless here). Copied from mitls-fstar
// src/tls/declassify.fst (branch dev)
friend Lib.IntTypes
let declassify : squash (Lib.IntTypes.uint8 == UInt8.t)= ()


/// encryption of a packet

#push-options "--z3rlimit 20"

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
  let cipher = AEAD.encrypt #a k iv aad plain in
  header_encrypt a hpk h cipher

#pop-options

#push-options "--max_ifuel 1 --initial_ifuel 1 --z3rlimit 16"

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

#pop-options

/// proving correctness of decryption (link between modulo, and be_to_n
/// + slice last bytes

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
  let cipher = AEAD.encrypt #a k iv aad plain in
  assert (packet == header_encrypt a hpk h cipher);
  lemma_header_encryption_correct a hpk h cid_len last cipher;
  let dc = header_decrypt a hpk cid_len last packet in
  assert (H_Success? dc);
  let H_Success h' c' = dc in
  assert (h == h' /\ cipher == c');
  let clen = S.length cipher in
  assert (19 <= clen && clen < max_cipher_length);
  AEAD.correctness #a k iv aad plain
