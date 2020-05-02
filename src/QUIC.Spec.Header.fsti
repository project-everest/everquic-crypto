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

type cbytes' (is_retry: bool) = b: bytes { let l = Seq.length b in if is_retry then l == 0 else (19 <= l /\ l < max_cipher_length) }

// Header serialization and protection

val header_encrypt:
  a:ea ->
  hpk: Cipher.key (AEAD.cipher_alg_of_supported_alg a) ->
  h: header ->
  c: cbytes' (is_retry h) ->
  GTot packet

noeq
type h_result =
| H_Success:
  h: header ->
  cipher: cbytes' (is_retry h) ->
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


(*
module Secret = QUIC.Secret.Int
module U32 = FStar.UInt32
module PN = QUIC.Spec.PacketNumber.Base

noeq
type h_result =
| H_Success:
  h: header ->
  c: bytes ->
  h_result
| H_Failure

val parse_header: cid_len: nat { cid_len <= 20 } -> last: nat { last + 1 < pow2 62 } -> b:bytes -> GTot h_result

val parse_header_post:
  cid_len: nat { cid_len <= 20 } -> 
  last: nat { last + 1 < pow2 62 } -> 
  b:bytes -> 
  Lemma (
    match parse_header cid_len last b with
    | H_Failure -> True
    | H_Success h c ->
      is_valid_header h cid_len last /\
      Seq.length c <= Seq.length b /\
      c `Seq.equal` Seq.slice b (Seq.length b - Seq.length c) (Seq.length b)
  )

val format_header (h: header) : GTot bytes

val lemma_header_parsing_correct:
  h: header ->
  c: bytes ->
  cid_len: nat { cid_len <= 20 } ->
  last: nat { last + 1 < pow2 62 } ->
  Lemma
  (requires (
    is_valid_header h cid_len last
  ))
  (ensures (
    parse_header cid_len last (format_header h `Seq.append` c)
    == H_Success h c))

// N.B. this is only true for a given DCID len
val lemma_header_parsing_safe: cid_len: nat -> last: nat -> b1:bytes -> b2:bytes -> Lemma
  (requires (
    cid_len <= 20 /\
    last + 1 < pow2 62 /\
    parse_header cid_len last b1 == parse_header cid_len last b2
  ))
  (ensures parse_header cid_len last b1 == H_Failure \/ b1 = b2)

type cbytes' (is_retry: bool) = b: bytes { let l = Seq.length b in if is_retry then l == 0 else (19 <= l /\ l < max_cipher_length) }

noeq
type hd_result =
| HD_Success:
  h: header ->
  cipher: cbytes' (is_retry h) ->
  rem: bytes ->
  hd_result
| HD_Failure

val header_decrypt:
  a:ea ->
  hpk: Cipher.key (AEAD.cipher_alg_of_supported_alg a) ->
  cid_len: nat { cid_len <= 20 } ->
  last: nat { last + 1 < pow2 62 } ->
  p: packet ->
  GTot hd_result

val header_encrypt:
  a:ea ->
  hpk: Cipher.key (AEAD.cipher_alg_of_supported_alg a) ->
  h: header ->
  c: cbytes ->
  GTot packet

// This is just functional correctness, but does not guarantee security:
// decryption can succeed on an input that is not the encryption
// of the same arguments (see QUIC.Spec.Old.*_malleable)
val lemma_header_encryption_correct:
  a:ea ->
  k: Cipher.key (AEAD.cipher_alg_of_supported_alg a) ->
  h:header ->
  cid_len: nat { cid_len <= 20 /\ (MShort? h ==> cid_len == dcid_len h) } ->
  last: nat { last + 1 < pow2 62 /\ ((~ (is_retry h)) ==> PN.in_window (Secret.v (pn_length h) - 1) last (Secret.v (packet_number h))) } ->
  c: cbytes { has_payload_length h ==> Secret.v (payload_length h) == Seq.length c } ->
  rem: bytes {
    Seq.length (format_header h) + Seq.length c + Seq.length rem < pow2 32 /\
    ((~ (has_payload_length h)) ==> rem == Seq.empty)
  } ->
  Lemma (
    Seq.length (header_encrypt a k h c) + Seq.length rem < pow2 32 /\
    header_decrypt a k cid_len last (header_encrypt a k h c `Seq.append` rem)
    == HD_Success h (if is_retry h then Seq.empty else c) ((if is_retry h then c else Seq.empty) `Seq.append` rem)
  )

(*


(*
module U8 = FStar.UInt8
module U32 = FStar.UInt32
module S = FStar.Seq
module U64 = FStar.UInt64

module PN = QUIC.Spec.PacketNumber

let header_len_bound = 16500 // FIXME: this should be in line with the parser kind

val header_len (h:header) : GTot (n: pos { n <= header_len_bound })

val format_header: h:header -> GTot (lbytes (header_len h))

module BF = LowParse.BitFields

val format_header_is_short: h: header -> Lemma
  (MShort? h <==> BF.get_bitfield (U8.v (Seq.index (format_header h) 0)) 7 8 == 0)

val format_header_is_retry: h: header -> Lemma
  (is_retry h <==> (
    BF.get_bitfield (U8.v (Seq.index (format_header h) 0)) 7 8 == 1 /\
    BF.get_bitfield (U8.v (Seq.index (format_header h) 0)) 4 6 == 3
  ))

val format_header_pn_length: h: header -> Lemma
  (requires (~ (is_retry h)))
  (ensures (BF.get_bitfield (U8.v (Seq.index (format_header h) 0)) 0 2 == U32.v (pn_length h) - 1))

val pn_offset: (h: header { ~ (is_retry h) }) -> GTot (n: nat { 0 < n /\ n + U32.v (pn_length h) == header_len h }) // need to know that packet number is the last field of the format

val putative_pn_offset: (cid_len: nat) -> (x: bytes) -> GTot (option (y: nat {0 < y /\ y <= Seq.length x}))

val putative_pn_offset_frame
  (cid_len: nat)
  (x1 x2: bytes)
: Lemma
  (requires (match putative_pn_offset cid_len x1 with
  | None -> False
  | Some off ->
    off <= Seq.length x2 /\
    Seq.slice x1 1 off `Seq.equal` Seq.slice x2 1 off /\ (
    let f1 = Seq.index x1 0 in
    let f2 = Seq.index x2 0 in
    let is_short = BF.get_bitfield (U8.v f1) 7 8 = 0 in
    let number_of_protected_bits = if is_short then 5 else 4 in
    BF.get_bitfield (U8.v f1) number_of_protected_bits 8 == BF.get_bitfield (U8.v f2) number_of_protected_bits 8
  )))
  (ensures (match putative_pn_offset cid_len x1 with
  | None -> False
  | Some off -> putative_pn_offset cid_len x2 == Some (off <: nat)
  ))

val putative_pn_offset_correct
  (h: header {~ (is_retry h)})
  (cid_len: nat)
: Lemma
  (requires (MShort? h ==> cid_len == dcid_len h))
  (ensures (putative_pn_offset cid_len (format_header h) == Some (pn_offset h <: nat)))

noeq
type h_result =
| H_Success:
  h: header ->
  c: bytes ->
  h_result
| H_Failure

val parse_header: cid_len: nat { cid_len <= 20 } -> last: nat { last + 1 < pow2 62 } -> b:bytes -> GTot (r: h_result {
  match r with
  | H_Failure -> True
  | H_Success h c ->
    is_valid_header h cid_len last /\
    Seq.length c <= Seq.length b /\
    c `Seq.equal` Seq.slice b (Seq.length b - Seq.length c) (Seq.length b)
})

val lemma_header_parsing_correct:
  h: header ->
  c: bytes ->
  cid_len: nat { cid_len <= 20 } ->
  last: nat { last + 1 < pow2 62 } ->
  Lemma
  (requires (
    is_valid_header h cid_len last
  ))
  (ensures (
    parse_header cid_len last Seq.(format_header h @| c)
    == H_Success h c))

// N.B. this is only true for a given DCID len
val lemma_header_parsing_safe: cid_len: nat -> last: nat -> b1:bytes -> b2:bytes -> Lemma
  (requires (
    cid_len <= 20 /\
    last + 1 < pow2 62 /\
    parse_header cid_len last b1 == parse_header cid_len last b2
  ))
  (ensures parse_header cid_len last b1 == H_Failure \/ b1 = b2)

let lemma_header_parsing_post
  (cid_len: nat { cid_len <= 20 })
  (last: nat { last + 1 < pow2 62 })
  (b: bytes)
: Lemma
  (match parse_header cid_len last b with
  | H_Failure -> True
  | H_Success h c ->
    is_valid_header h cid_len last /\
    header_len h + Seq.length c == Seq.length b /\
    b == format_header h `Seq.append` c /\
    Seq.slice b 0 (header_len h) == format_header h /\
    c == Seq.slice b (header_len h) (Seq.length b)
  )
= match parse_header cid_len last b with
  | H_Failure -> ()
  | H_Success h c ->
    lemma_header_parsing_correct h c cid_len last ;
    lemma_header_parsing_safe cid_len last b (format_header h `Seq.append` c);
    assert (b `Seq.equal` (format_header h `Seq.append` c));
    assert (Seq.slice b 0 (header_len h) `Seq.equal` format_header h);
    assert (c `Seq.equal` Seq.slice b (header_len h) (Seq.length b))
