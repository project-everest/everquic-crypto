module QUIC.Spec.Header.Parse
include QUIC.Spec.Header.Base

module U8 = FStar.UInt8
module U32 = FStar.UInt32
module S = FStar.Seq
module U64 = FStar.UInt64
module Secret = QUIC.Secret.Int

val header_len (h:header) : GTot (n: pos { n <= header_len_bound })

val format_header: h:header -> GTot (lbytes (header_len h))

module BF = LowParse.BitFields

val format_header_is_short: h: header -> Lemma
  (MShort? h <==> BF.get_bitfield (U8.v (S.index (format_header h) 0)) 7 8 == 0)

val format_header_is_retry: h: header -> Lemma
  (is_retry h <==> (
    BF.get_bitfield (U8.v (S.index (format_header h) 0)) 7 8 == 1 /\
    BF.get_bitfield (U8.v (S.index (format_header h) 0)) 4 6 == 3
  ))

val format_header_pn_length: h: header -> Lemma
  (requires (~ (is_retry h)))
  (ensures (BF.get_bitfield (U8.v (S.index (format_header h) 0)) 0 2 == Secret.v (pn_length h) - 1))

val pn_offset: (h: header { ~ (is_retry h) }) -> GTot (n: nat { 0 < n /\ n + Secret.v (pn_length h) == header_len h }) // need to know that packet number is the last field of the format

val putative_pn_offset: (cid_len: nat) -> (x: bytes) -> GTot (option (y: nat {0 < y /\ y <= Seq.length x /\ y <= header_len_bound}))

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
  (cid_len: nat { cid_len <= 20 })
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
    parse_header cid_len last S.(format_header h @| c)
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
    lemma_header_parsing_safe cid_len last b (format_header h `S.append` c);
    assert (b `Seq.equal` (format_header h `Seq.append` c));
    assert (Seq.slice b 0 (header_len h) `Seq.equal` format_header h);
    assert (c `Seq.equal` Seq.slice b (header_len h) (Seq.length b))

let packet_is_retry
  (x: bytes)
: GTot bool
= if Seq.length x > 0
  then
    let f = S.index x 0 in
    BF.get_bitfield (U8.v f) 7 8 = 1 &&
    BF.get_bitfield (U8.v f) 4 6 = 3
  else false

val parse_header_exists
  (cid_len: nat { cid_len <= 20 })
  (last: nat { last + 1 < pow2 62 })
  (x:bytes)
: Lemma
  (requires (
    match putative_pn_offset cid_len x with
    | None -> False
    | Some off -> (~ (packet_is_retry x)) ==> off + 4 <= Seq.length x
  ))
  (ensures (
    H_Success? (parse_header cid_len last x)
  ))
