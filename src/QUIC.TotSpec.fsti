module QUIC.TotSpec

include QUIC.Spec.Header.Base
include QUIC.Spec.Crypto

module Seq = FStar.Seq
module HD = Spec.Hash.Definitions
module AEAD = Spec.Agile.AEAD
module Cipher = Spec.Agile.Cipher
module PN = QUIC.Spec.PacketNumber.Base
module Secret = QUIC.Secret.Int
module Spec = QUIC.Spec

(* A total (non-ghost) specification of encryption and decryption, for idealization proof purposes, or for functional testing (extracting to OCaml) *)

val block_of_sample
  (a: Cipher.cipher_alg)
  (k: Cipher.key a)
  (sample: Seq.lseq Secret.uint8 16)
: Tot (y: Seq.lseq Secret.uint8 16 { y == QUIC.Spec.Header.block_of_sample a k sample })

val encrypt:
  a: ea ->
  k: AEAD.kv a ->
  static_iv: Spec.iv_t a ->
  hpk: Cipher.key (AEAD.cipher_alg_of_supported_alg a) ->
  h: header ->
  plain: pbytes' (is_retry h) ->
  Tot (p: packet { p == Spec.encrypt a k static_iv hpk h plain })

val decrypt:
  a: ea ->
  k: AEAD.kv a ->
  static_iv: Spec.iv_t a ->
  hpk: Cipher.key (AEAD.cipher_alg_of_supported_alg a) ->
  last: nat{last+1 < pow2 62} ->
  cid_len: nat { cid_len <= 20 } ->
  packet: packet ->
  Tot (r: Spec.result {
    r == Spec.decrypt a k static_iv hpk last cid_len packet
  })
