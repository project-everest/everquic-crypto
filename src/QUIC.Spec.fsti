module QUIC.Spec

include QUIC.Spec.Header.Base
include QUIC.Spec.Crypto

module Seq = FStar.Seq
module HD = Spec.Hash.Definitions
module AEAD = Spec.Agile.AEAD

// JP: should we allow inversion on either hash algorithm or AEAD algorithm?
#set-options "--max_fuel 0 --max_ifuel 0"

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
