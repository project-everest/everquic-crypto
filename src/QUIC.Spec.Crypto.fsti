module QUIC.Spec.Crypto
include QUIC.Spec.Base

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

// Move from Hashing.Spec to Spec.Hash?
let keysized (a:ha) (l:nat) =
  l <= HD.max_input_length a /\ l + HD.block_length a < pow2 32
let hashable (a:ha) (l:nat) = l <= HD.max_input_length a

// AEAD plain and ciphertext. We want to guarantee that regardless
// of the header size (max is 54), the neader + ciphertext + tag fits in a buffer
// JP: perhaps cleaner with a separate lemma; any reason for putting this in a refinement?
let max_plain_length: n:nat {
  forall a. {:pattern AEAD.max_length a} n <= AEAD.max_length a
} =
  pow2 32 - header_len_bound - 16

let max_cipher_length : n:nat {
  forall a. {:pattern AEAD.max_length a \/ AEAD.tag_length a }
    n <= AEAD.max_length a + AEAD.tag_length a
} =
  pow2 32 - header_len_bound

type packet = b:bytes{let l = Seq.length b in (* 21 <= l /\ *) l < pow2 32}
type pbytes = b:bytes{let l = Seq.length b in 3 <= l /\ l < max_plain_length}
type pbytes' (is_retry: bool) = b:bytes{let l = Seq.length b in if is_retry then l == 0 else (3 <= l /\ l < max_plain_length)}
type cbytes = b:bytes{let l = Seq.length b in 19 <= l /\ l < max_cipher_length}
type cbytes' (is_retry: bool) = b: bytes { let l = Seq.length b in if is_retry then l == 0 else (19 <= l /\ l < max_cipher_length) }

// Static byte sequences to be fed into secret derivation. Marked as inline, so
// that they can be used as arguments to gcmalloc_of_list for top-level arrays.
inline_for_extraction
val label_key: lbytes 3
inline_for_extraction
val label_iv: lbytes 2
inline_for_extraction
val label_hp: lbytes 2

val derive_secret:
  a: ha ->
  prk:Spec.Hash.Definitions.bytes_hash a ->
  label: bytes ->
  len: nat ->
  Ghost (* Pure *) (lbytes len)
  (requires len <= 255 /\
    Seq.length label <= 244 /\
    keysized a (Seq.length prk)
    )
  (ensures fun out -> True)
