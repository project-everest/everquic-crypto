module QUIC.Spec

include QUIC.Spec.Header.Base

module Seq = FStar.Seq
module HD = Spec.Hash.Definitions
module AEAD = Spec.Agile.AEAD

// JP: should we allow inversion on either hash algorithm or AEAD algorithm?
#set-options "--max_fuel 0 --max_ifuel 0"

// Move from Hashing.Spec to Spec.Hash?
let keysized (a:ha) (l:nat) =
  l <= HD.max_input_length a /\ l + HD.block_length a < pow2 32
let hashable (a:ha) (l:nat) = l <= HD.max_input_length a

let header_len_bound = 16500 // FIXME: this should be in line with the parser kind

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

type nat2 = n:nat{n < 4}
type nat4 = n:nat{n < 16}
type nat32 = n:nat{n < pow2 32}
type nat62 = n:nat{n < pow2 62}

let add3 (n:nat4) : n:nat{n=0 \/ (n >= 4 /\ n <= 18)} = if n = 0 then 0 else 3+n
let sub3 (n:nat{n = 0 \/ (n >= 4 /\ n <= 18)}) : nat4 = if n = 0 then 0 else n-3
type qbytes (n:nat4) = lbytes (add3 n)

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

val encrypt:
  a: ea ->
  k: lbytes (AEAD.key_length a) ->
  static_iv: lbytes 12 ->
  hpk: lbytes (ae_keysize a) ->
  h: header ->
  plain: pbytes' (is_retry h) ->
  GTot packet

/// decryption and correctness

#set-options "--max_fuel 0 --max_ifuel 1"

val decrypt:
  a: ea ->
  k: lbytes (AEAD.key_length a) ->
  static_iv: lbytes 12 ->
  hpk: lbytes (ae_keysize a) ->
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
