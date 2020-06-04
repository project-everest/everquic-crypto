module QUIC.Spec.Header
include QUIC.Spec.Crypto
include QUIC.Spec.Header.Base

module Seq = FStar.Seq
module HD = Spec.Hash.Definitions
module AEAD = Spec.Agile.AEAD
module U32 = FStar.UInt32
module U64 = FStar.UInt64
module PN = QUIC.Spec.PacketNumber.Base
module Secret = QUIC.Secret.Int
module AEAD = Spec.Agile.AEAD
module Cipher = Spec.Agile.Cipher

// Header serialization and protection

val block_of_sample
  (a: Cipher.cipher_alg)
  (k: Cipher.key a)
  (sample: Seq.lseq Secret.uint8 16)
: GTot (Seq.lseq Secret.uint8 16)

val pn_sizemask (pn_len: nat { pn_len < 4 }) : Tot (lbytes (pn_len + 1))

val header_encrypt:
  a:ea ->
  hpk: Cipher.key (AEAD.cipher_alg_of_supported_alg a) ->
  h: header ->
  c: cbytes' (is_retry h) ->
  GTot packet

val header_encrypt_length:
  a: ea ->
  hpk: Cipher.key (AEAD.cipher_alg_of_supported_alg a) ->
  h: header ->
  c: cbytes' (is_retry h) ->
  Lemma
  (
    Seq.length (header_encrypt a hpk h c) ==
    header_len h + Seq.length c
  )

noeq
type h_result =
| H_Success:
  h: header ->
  cipher: bytes {
    let len = Seq.length cipher in
    if is_retry h
    then len == 0
    else 16 <= len (* the true bound is 20-pn_len h *) /\ len < max_cipher_length
  } ->
  rem: bytes ->
  h_result
| H_Failure

// Header protection removal and parsing

val header_decrypt:
  a:ea ->
  hpk: Cipher.key (AEAD.cipher_alg_of_supported_alg a) ->
  cid_len: nat { cid_len <= 20 } ->
  last: nat { last + 1 < pow2 62 } ->
  p: packet ->
  GTot (r: h_result { match r with
  | H_Failure -> True
  | H_Success h c rem ->
    is_valid_header h cid_len last /\
    Seq.length rem <= Seq.length p /\
    rem `Seq.equal` Seq.slice p (Seq.length p - Seq.length rem) (Seq.length p)
  })

// This is just functional correctness, but does not guarantee security:
// decryption can succeed on an input that is not the encryption
// of the same arguments (see QUIC.Spec.Old.*_malleable)
val lemma_header_encryption_correct:
  a:ea ->
  k: Cipher.key (AEAD.cipher_alg_of_supported_alg a) ->
  h:header ->
  cid_len: nat { cid_len <= 20 /\ (MShort? h ==> cid_len == dcid_len h) } ->
  last: nat { last + 1 < pow2 62 /\ ((~ (is_retry h)) ==> PN.in_window (Secret.v (pn_length h) - 1) last (Secret.v (packet_number h))) } ->
  c: cbytes' (is_retry h) { has_payload_length h ==> Secret.v (payload_length h) == Seq.length c } ->
  Lemma (
    header_decrypt a k cid_len last (header_encrypt a k h c)
    == H_Success h c Seq.empty)
