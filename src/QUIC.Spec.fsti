module QUIC.Spec

include QUIC.Spec.Header.Base
include QUIC.Spec.Crypto

module Seq = FStar.Seq
module HD = Spec.Hash.Definitions
module AEAD = Spec.Agile.AEAD
module Cipher = Spec.Agile.Cipher
module PN = QUIC.Spec.PacketNumber.Base
module Secret = QUIC.Secret.Int

noeq
type h_result =
| H_Success:
  h: header ->
  cipher: cbytes' (is_retry h) ->
  rem: bytes ->
  h_result
| H_Failure

// TODO: add a prefix lemma on header_decrypt, if ever useful

module U32 = FStar.UInt32
module U64 = FStar.UInt64


noeq
type result =
| Success: 
  h: header ->
  plain: bytes ->
  remainder: bytes ->
  result
| Failure

let iv_t (a: ea) = (x: AEAD.iv a { Seq.length x == 12 })

val encrypt:
  a: ea ->
  k: AEAD.kv a ->
  static_iv: iv_t a ->
  hpk: Cipher.key (AEAD.cipher_alg_of_supported_alg a) ->
  h: header ->
  plain: pbytes' (is_retry h) ->
  GTot packet

val encrypt_length_ext:
  a: ea ->
  k: AEAD.kv a ->
  static_iv: iv_t a ->
  hpk: Cipher.key (AEAD.cipher_alg_of_supported_alg a) ->
  h: header ->
  plain1: pbytes' (is_retry h) ->
  plain2: pbytes' (is_retry h) ->
  Lemma
  (requires (Seq.length plain1 == Seq.length plain2))
  (ensures (
    Seq.length (encrypt a k static_iv hpk h plain1) ==
    Seq.length (encrypt a k static_iv hpk h plain2)
  ))

/// decryption and correctness

val decrypt:
  a: ea ->
  k: AEAD.kv a ->
  static_iv: iv_t a ->
  hpk: Cipher.key (AEAD.cipher_alg_of_supported_alg a) ->
  last: nat{last+1 < pow2 62} ->
  cid_len: nat { cid_len <= 20 } ->
  packet: packet ->
  GTot (r: result {
    match r with
    | Failure -> True
    | Success h _ rem ->
      is_valid_header h cid_len last /\
      Seq.length rem <= Seq.length packet /\
      rem `Seq.equal` Seq.slice packet (Seq.length packet - Seq.length rem) (Seq.length packet)
  })

val lemma_encrypt_correct:
  a: ea ->
  k: AEAD.kv a ->
  siv: iv_t a ->
  hpk: Cipher.key (AEAD.cipher_alg_of_supported_alg a) ->
  h: header ->
  cid_len: nat { cid_len <= 20 /\ (MShort? h ==> cid_len == dcid_len h) } ->
  last: nat{last+1 < pow2 62 } ->
  p: pbytes' (is_retry h)  { has_payload_length h ==> Secret.v (payload_length h) == Seq.length p + AEAD.tag_length a } -> Lemma
  (requires (
    (~ (is_retry h)) ==> (
      PN.in_window (Secret.v (pn_length h) - 1) last (Secret.v (packet_number h))
  )))
  (ensures (
    decrypt a k siv hpk last cid_len
      (encrypt a k siv hpk h p)
    == Success h p Seq.empty
  ))
