module QUIC.Crypto.Base
include QUIC.Spec.Header.Base

module Seq = FStar.Seq
module HD = Spec.Hash.Definitions
module AEAD = Spec.Agile.AEAD

let supported_hash = function
  | HD.SHA1 | HD.SHA2_256 | HD.SHA2_384 | HD.SHA2_512 -> true
  | _ -> false

let supported_aead = function
  | AEAD.AES128_GCM | AEAD.AES256_GCM | AEAD.CHACHA20_POLY1305 -> true
  | _ -> false

type ha = a:HD.hash_alg{supported_hash a}
type ea = a:AEAD.alg{supported_aead a}

// JP: this is Spec.Agile.Cipher.key_length
let ae_keysize (a:ea) =
  match a with
  | AEAD.AES128_GCM -> 16
  | _ -> 32

let max_cipher_length : n:nat {
  forall a. {:pattern AEAD.max_length a \/ AEAD.tag_length a }
    n <= AEAD.max_length a + AEAD.tag_length a
} =
  pow2 32 - header_len_bound

type cbytes = b:bytes{let l = Seq.length b in 19 <= l /\ l < max_cipher_length}
