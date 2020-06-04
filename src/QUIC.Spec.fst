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

/// encryption of a packet

let iv_for_encrypt_decrypt
  (a: ea)
  (siv: iv_t a)
  (h: header { ~ (is_retry h) })
: GTot (iv_t a)
=
  let pn_len = Secret.v (pn_length h) - 1 in
  let seqn = packet_number h in
  let _ = assert_norm(pow2 62 < pow2 (8 `op_Multiply` 12)) in
  let pnb = FStar.Endianness.n_to_be 12 (Secret.v seqn) in
  Seq.seq_hide #Secret.U8 (xor_inplace pnb (Seq.seq_reveal siv) 0)

let payload_encrypt
  (a: ea)
  (k: AEAD.kv a)
  (siv: iv_t a)
  (h: header { ~ (is_retry h) })
  (plain: pbytes)
: GTot (cbytes)
=
  let aad = Parse.format_header h in
  let iv = iv_for_encrypt_decrypt a siv h in
  Seq.seq_reveal (AEAD.encrypt #a k iv (Seq.seq_hide aad) (Seq.seq_hide plain))

let encrypt
  a k siv hpk h plain
=
  let cipher =
    if is_retry h
    then plain
    else payload_encrypt a k siv h plain
  in
  H.header_encrypt a hpk h cipher

let encrypt_length
  a k siv hpk h plain
=
  let c =
    if is_retry h
    then plain
    else payload_encrypt a k siv h plain
  in
  H.header_encrypt_length a hpk h c

#restart-solver

let payload_decrypt
  (a: ea)
  (k: AEAD.kv a)
  (siv: iv_t a)
  (h: header { ~ (is_retry h) })
  (c: Seq.seq Secret.uint8 { 16 <= Seq.length c /\ Seq.length c < max_cipher_length })
: GTot (option (AEAD.decrypted c))
= 
  let iv = iv_for_encrypt_decrypt a siv h in
  let aad = Parse.format_header h in
  AEAD.decrypt #a k iv (Seq.seq_hide aad) c

let decrypt
  a k siv hpk last cid_len packet
=
  let open FStar.Math.Lemmas in
  let open FStar.Endianness in
  match H.header_decrypt a hpk cid_len last packet with
  | H.H_Failure -> Failure
  | H.H_Success h c rem ->
    if is_retry h
    then Success h c rem
    else
      match payload_decrypt a k siv h (Seq.seq_hide c) with
      | None -> Failure
      | Some plain -> Success h (Seq.seq_reveal plain) rem

let lemma_encrypt_correct
  a k siv hpk h cid_len last plain
=
  let packet = encrypt a k siv hpk h plain in
  let aad = Seq.seq_hide (Parse.format_header h) in
  let cipher = if is_retry h then plain else
    let iv = iv_for_encrypt_decrypt a siv h in
    Seq.seq_reveal (AEAD.encrypt #a k iv aad (Seq.seq_hide plain))
  in
  assert (packet == H.header_encrypt a hpk h cipher);
  H.lemma_header_encryption_correct a hpk h cid_len last cipher;
  if is_retry h
  then ()
  else begin
    let iv = iv_for_encrypt_decrypt a siv h in
    let dc = H.header_decrypt a hpk cid_len last packet in
    assert (H.H_Success? dc);
    let H.H_Success h' c' rem' = dc in
    assert (h == h' /\ cipher == c');
    let clen = Seq.length cipher in
    assert (19 <= clen && clen < max_cipher_length);
    AEAD.correctness #a k iv aad (Seq.seq_hide plain)
  end

