module QUIC.Spec

include QUIC.Spec.Header.Base
include QUIC.Spec.Crypto

module Seq = FStar.Seq
module HD = Spec.Hash.Definitions
module AEAD = Spec.Agile.AEAD
module Cipher = Spec.Agile.Cipher
module PN = QUIC.Spec.PacketNumber.Base
module Secret = QUIC.Secret.Int

(*
type nat2 = n:nat{n < 4}
type nat4 = n:nat{n < 16}
type nat32 = n:nat{n < pow2 32}
type nat62 = n:nat{n < pow2 62}

let add3 (n:nat4) : n:nat{n=0 \/ (n >= 4 /\ n <= 18)} = if n = 0 then 0 else 3+n
let sub3 (n:nat{n = 0 \/ (n >= 4 /\ n <= 18)}) : nat4 = if n = 0 then 0 else n-3
type qbytes (n:nat4) = lbytes (add3 n)
*)

// JP: seems appropriate for this module...?
let _: squash (inversion header) = allow_inversion header

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
  plain: pbytes' (is_retry h) ->
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
