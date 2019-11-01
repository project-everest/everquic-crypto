module QUIC.Parse
include QUIC.Spec.Base

module B = LowStar.Buffer
module U8 = FStar.UInt8
module U32 = FStar.UInt32
module HST = FStar.HyperStack.ST
module S = FStar.Seq

let header_len_bound = 16500 // FIXME: this should be in line with the parser kind

val header_len (h:header) : GTot (n: pos { n <= header_len_bound })

(*
=
  match h with
  | MShort spin phase cid ->
    1 + S.length cid + 1 + pn_len
  | MLong is_hs version dcil scil dcid scid plen ->
    let _ = assert_norm(max_cipher_length < pow2 62) in
    6 + add3 dcil + add3 scil + vlen plen + 1 + pn_len
*)

(*
  | Short _ _ cid -> sub3 (S.length cid)
  | Long _ _ dcil _ _ _ _ -> dcil
*)

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
  (ensures (BF.get_bitfield (U8.v (S.index (format_header h) 0)) 0 2 == U32.v (pn_length h)))

val pn_offset: (h: header { ~ (is_retry h) }) -> GTot (n: nat { 0 < n /\ n + U32.v (pn_length h) <= header_len h })

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

val parse_header: cid_len: nat -> b:bytes -> GTot (r: h_result {
  match r with
  | H_Failure -> True
  | H_Success h c ->
    (MShort? h ==> dcid_len h == cid_len) /\
    Seq.length c <= Seq.length b /\
    c == Seq.slice b (Seq.length b - Seq.length c) (Seq.length b)
})

val lemma_header_parsing_correct:
  h: header ->
  c: bytes ->
  cid_len: nat ->
  Lemma
  (requires (MShort? h ==> cid_len == dcid_len h))
  (ensures (
    parse_header cid_len S.(format_header h @| c)
    == H_Success h c))

// N.B. this is only true for a given DCID len
val lemma_header_parsing_safe: cid_len: nat -> b1:packet -> b2:packet -> Lemma
  (requires parse_header cid_len b1 == parse_header cid_len b2)
  (ensures parse_header cid_len b1 == H_Failure \/ b1 = b2)

val test : B.buffer U8.t -> HST.Stack U32.t (requires (fun _ -> False)) (ensures (fun _ _ _ -> True))
