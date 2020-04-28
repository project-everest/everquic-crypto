module QUIC.Spec.Public

module LP = LowParse.Spec.Base
module U32 = FStar.UInt32
module U62 = QUIC.UInt62
module U64 = FStar.UInt64
module U8 = FStar.UInt8
module LPB = LowParse.BitFields
module FB = FStar.Bytes

inline_for_extraction
let short_dcid_len_t = (short_dcid_len: U32.t { U32.v short_dcid_len <= 20 })

inline_for_extraction
noextract
let token_max_len = 16383 // arbitrary bound

inline_for_extraction
let vlbytes (min: nat) (max: nat) =
  (x: FB.bytes { min <= FB.length x /\ FB.length x <= max })

inline_for_extraction
noextract
let bitfield
  (sz: nat { sz <= 8 })
: Tot eqtype
= (x: U8.t { U8.v x < pow2 sz })

inline_for_extraction
let payload_and_pn_length_t : Type0 =
  (payload_and_pn_length: U62.t { U64.v payload_and_pn_length >= 20 })

noeq
type long_header_specifics =
| PInitial:
  (token: vlbytes 0 token_max_len) -> // arbitrary bound
  (payload_and_pn_length: payload_and_pn_length_t) ->
  long_header_specifics
| PZeroRTT:
  (payload_and_pn_length: payload_and_pn_length_t) ->
  long_header_specifics
| PHandshake:
  (payload_and_pn_length: payload_and_pn_length_t) ->
  long_header_specifics
| PRetry:
  (odcid: vlbytes 0 20) -> // TODO: change bounds to drop instead of rejecting as invalid
  long_header_specifics

noeq
type header =
| PLong:
  (protected_bits: bitfield 4) ->
  (version: U32.t) ->
  (dcid: vlbytes 0 20) ->
  (scid: vlbytes 0 20) ->
  (spec: long_header_specifics) ->
  header
| PShort:
  (protected_bits: bitfield 5) ->
  (spin: bool) ->
  (dcid: vlbytes 0 20) ->
  header

let is_retry
  (h: header)
: Tot bool
= if PShort? h
  then false
  else
    let spec = PLong?.spec h in
    PRetry? spec

let dcid_len (h: header) : Tot nat =
  match h with
  | PLong _ _ dcid _ _ -> FB.length dcid
  | PShort _ _ dcid -> FB.length dcid

let short_dcid_len_prop
  (short_dcid_len: short_dcid_len_t)
  (h: header)
: GTot Type0
= (PShort? h ==> dcid_len h == U32.v short_dcid_len)

unfold
let parse_header_prop
  (short_dcid_len: short_dcid_len_t)
  (m: header)
: GTot Type0
= short_dcid_len_prop short_dcid_len m

inline_for_extraction
type header'
  (short_dcid_len: short_dcid_len_t)
= (m: header { parse_header_prop short_dcid_len m })

inline_for_extraction
noextract
val parse_header_kind
  (short_dcid_len: short_dcid_len_t)
: Tot (k: LP.parser_kind {
    k.LP.parser_kind_subkind == Some LP.ParserStrong /\
    k.LP.parser_kind_low > 0
  })

val parse_header
  (short_dcid_len: short_dcid_len_t)
: Tot (LP.parser (parse_header_kind short_dcid_len) (header' short_dcid_len))

val serialize_header
  (short_dcid_len: short_dcid_len_t)
: Tot (LP.serializer (parse_header short_dcid_len))


(* Mutating the protected bits *)

let get_protected_bits
  (h: header)
: Tot (bitfield (if PShort? h then 5 else 4))
= match h with
  | PShort pb spin dcid -> pb
  | PLong pb version dcid scid spec -> pb

let set_protected_bits
  (h: header)
  (new_pb: bitfield (if PShort? h then 5 else 4))
: Tot header
= match h with
  | PShort _ spin dcid -> PShort new_pb spin dcid
  | PLong _ version dcid scid spec -> PLong new_pb version dcid scid spec

val serialize_set_protected_bits
  (short_dcid_len: short_dcid_len_t)
  (h: header' short_dcid_len)
  (new_pb: bitfield (if PShort? h then 5 else 4))
: Lemma
  (let sq = LP.serialize (serialize_header short_dcid_len) h in
  Seq.length sq > 0 /\
  LP.serialize (serialize_header short_dcid_len) (set_protected_bits h new_pb) `Seq.equal`
    (LPB.uint8.LPB.set_bitfield (Seq.head sq) 0 (if PShort? h then 5 else 4) new_pb `Seq.cons` Seq.tail sq))
