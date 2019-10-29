module QUIC.Parse
include QUIC.Parse.VarInt

open FStar.HyperStack.ST

open LowParse.Spec.BitSum

(* From
https://tools.ietf.org/html/draft-ietf-quic-transport-23#section-16,
except that we make the format non-ambiguous. *)

open LowParse.Spec.BoundedInt

module Cast = FStar.Int.Cast
module U64 = FStar.UInt64
module U32 = FStar.UInt32
module U16 = FStar.UInt16
module U8 = FStar.UInt8

(* From https://tools.ietf.org/html/draft-ietf-quic-transport-23#section-17 *)

inline_for_extraction
noextract
type header_form_t =
  | Long
  | Short

[@filter_bitsum'_t_attr]
inline_for_extraction
noextract
let header_form : enum header_form_t (bitfield uint8 1) = [
  Long, 1uy;
  Short, 0uy;
]

[@filter_bitsum'_t_attr]
inline_for_extraction
noextract
let fixed_bit : enum unit (bitfield uint8 1) = [
  (), 1uy;
]

inline_for_extraction
noextract
type long_packet_type_t =
  | Initial
  | ZeroRTT
  | Handshake
  | Retry

[@filter_bitsum'_t_attr]
inline_for_extraction
noextract
let long_packet_type : enum long_packet_type_t (bitfield uint8 2) = [
  Initial, 0uy;
  ZeroRTT, 1uy;
  Handshake, 2uy;
  Retry, 3uy;
]

[@filter_bitsum'_t_attr]
inline_for_extraction
noextract
let reserved_bits : enum unit (bitfield uint8 2) = [
  (), 0uy;
]

inline_for_extraction
noextract
type packet_number_length_t = bounded_int32 1 4

[@filter_bitsum'_t_attr]
inline_for_extraction
noextract
let packet_number_length : enum packet_number_length_t (bitfield uint8 2) = [
  1ul, 0uy;
  2ul, 1uy;
  3ul, 2uy;
  4ul, 3uy;
]

[@filter_bitsum'_t_attr]
inline_for_extraction
noextract
let rrpp : bitsum' uint8 4 =
  BitSum' _ _ reserved_bits (fun _ -> BitSum' _ _ packet_number_length (fun _ -> BitStop ()))

[@filter_bitsum'_t_attr]
inline_for_extraction
noextract
let first_byte : bitsum' uint8 0 =
  BitSum' _ _ header_form (function
    | Short ->
      BitSum' _ _ fixed_bit (fun _ ->
        BitField (* spin bit *) 1 (
          BitSum' _ _ reserved_bits (fun _ ->
            BitField (* key phase *) 1 (
              BitSum' _ _ packet_number_length (fun _ ->
                BitStop ()
              )
            )
          )
        )
      )
    | Long ->
      BitSum' _ _ fixed_bit (fun _ ->
        BitSum' _ _ long_packet_type (function
          | Retry -> BitField (* unused *) 4 (BitStop ())
          | _ -> rrpp
        )
      )
  )

[@filter_bitsum'_t_attr]
let filter_first_byte
: (x: FStar.UInt8.t) ->
  Tot (b: bool { b == filter_bitsum' first_byte x })
= norm [primops; iota; zeta; delta_attr [`%filter_bitsum'_t_attr]]
  (mk_filter_bitsum'_t' first_byte)

(*
// How to test normalization:
module T = FStar.Tactics
let f (x: FStar.UInt8.t) : Tot unit =
  assert (filter_header_byte x == true) by (
    T.norm [primops; iota; zeta; delta_attr [`%filter_bitsum'_t_attr]];
    T.fail "abc"
  )
*)

open LowParse.Spec.Bytes

module FB = FStar.Bytes

inline_for_extraction
noextract
let token_max_len = 16383 // arbitrary bound

noeq
type long_header_specifics =
| MInitial:
  (token: parse_bounded_vlbytes_t 0 token_max_len) -> // arbitrary bound
  (payload_length: varint_t) ->
  (packet_number: parse_bounded_vlbytes_t 1 4) ->
  long_header_specifics
| MZeroRTT:
  (payload_length: varint_t) ->
  (packet_number: parse_bounded_vlbytes_t 1 4) ->
  long_header_specifics
| MHandshake:
  (payload_length: varint_t) ->
  (packet_number: parse_bounded_vlbytes_t 1 4) ->
  long_header_specifics
| MRetry:
  (unused: bitfield uint8 4) ->
  (odcid: parse_bounded_vlbytes_t 0 20) -> // TODO: change bounds to drop instead of rejecting as invalid
  long_header_specifics

noeq
type header_gen =
| MLong:
  (version: FB.lbytes 4) ->
  (dcid: parse_bounded_vlbytes_t 0 20) ->
  (scid: parse_bounded_vlbytes_t 0 20) ->
  (spec: long_header_specifics) ->
  header_gen
| MShort:
  (spin: bool) ->
  (key_phase: bool) ->
  (dcid: FB.bytes) ->
  (packet_number: parse_bounded_vlbytes_t 1 4) ->
  header_gen

inline_for_extraction
let short_dcid_len_t = (short_dcid_len: U32.t { U32.v short_dcid_len <= 20 })

let header_short_dcid_length_prop
  (m: header_gen)
  (short_dcid_len: short_dcid_len_t)
: GTot bool
= if MShort? m
  then FB.length (MShort?.dcid m) = U32.v short_dcid_len
  else true

inline_for_extraction
noextract
type header_t (short_dcid_len: short_dcid_len_t) = (m: header_gen { header_short_dcid_length_prop m short_dcid_len })

#push-options "--z3rlimit 16"

inline_for_extraction
noextract
let first_byte_of_header
  (short_dcid_len: short_dcid_len_t)
  (t: Type0)
  (f: (bitsum'_type first_byte -> Tot t))
  (m: header_t short_dcid_len)
: Tot t
= match m with
  | MShort spin key_phase dcid packet_number ->
    let spin : bitfield uint8 1 = if spin then 1uy else 0uy in
    let key_phase : bitfield uint8 1 = if key_phase then 1uy else 0uy in
    let pn_length : packet_number_length_t = FB.len packet_number in
    f (| Short, (| (), (spin, (| (), (key_phase, (| pn_length, () |) ) |) ) |) |)
  | MLong version dcid scid spec ->
    begin match spec with
    | MInitial _ payload_length packet_number ->
      let pn_length : packet_number_length_t = FB.len packet_number in
      f (| Long, (| (), (| Initial, (| (), (| pn_length, () |) |) |) |) |)
    | MZeroRTT payload_length packet_number ->
      let pn_length : packet_number_length_t = FB.len packet_number in
      f (| Long, (| (), (| ZeroRTT, (| (), (| pn_length, () |) |) |) |) |)
    | MHandshake payload_length packet_number ->
      let pn_length : packet_number_length_t = FB.len packet_number in
      f (| Long, (| (), (| Handshake, (| (), (| pn_length, () |) |) |) |) |)
    | MRetry unused _ ->
      f (| Long, (| (), (| Retry, (unused, ()) |) |) |)
    end

#pop-options

[@filter_bitsum'_t_attr]
inline_for_extraction
noextract
let common_long_t
: Type0
= (FB.lbytes 4 & (parse_bounded_vlbytes_t 0 20 & parse_bounded_vlbytes_t 0 20))

[@filter_bitsum'_t_attr]
inline_for_extraction
noextract
let payload_length_pn
  (pn_length: packet_number_length_t)
: Tot Type0
= (varint_t & FB.lbytes (U32.v pn_length))

#push-options "--z3rlimit 16 --max_fuel 8 --max_ifuel 8 --initial_fuel 8 --initial_ifuel 8"

[@filter_bitsum'_t_attr]
inline_for_extraction
noextract
let header_body_type
  (short_dcid_len: short_dcid_len_t)
  (k' : bitsum'_key_type first_byte)
: Tot Type0
= match k' with
  | (| Short, (| (), (| (), (| pn_length, () |) |) |) |) ->
    (FB.lbytes (U32.v short_dcid_len) & FB.lbytes (U32.v pn_length))
  | (| Long, (| (), (| Initial, (| (), (| pn_length, () |) |) |) |) |) ->
    (common_long_t & (parse_bounded_vlbytes_t 0 token_max_len & payload_length_pn pn_length))
  | (| Long, (| (), (| ZeroRTT, (| (), (| pn_length, () |) |) |) |) |) ->
    (common_long_t & payload_length_pn pn_length)
  | (| Long, (| (), (| Handshake, (| (), (| pn_length, () |) |) |) |) |) ->
    (common_long_t & payload_length_pn pn_length)
  | (| Long, (| (), (| Retry, () |) |) |) ->
    (common_long_t & parse_bounded_vlbytes_t 0 20)

open LowParse.Spec.BitSum // again, for coerce

#pop-options

#push-options "--z3rlimit 32 --max_fuel 8 --max_ifuel 8 --initial_fuel 8 --initial_ifuel 8"

[@filter_bitsum'_t_attr]
inline_for_extraction
noextract
let mk_header
  (short_dcid_len: short_dcid_len_t)
  (k' : bitsum'_type first_byte)
  (pl: header_body_type short_dcid_len (bitsum'_key_of_t first_byte k'))
: Tot (refine_with_tag (first_byte_of_header short_dcid_len (bitsum'_type first_byte) id) k')
= match k' with
  | (| Short, (| (), (spin, (| (), (key_phase, (| pn_length, () |) ) |) ) |) |) ->
    let spin = (spin = 1uy) in
    let key_phase = (key_phase = 1uy) in
    begin match coerce (FB.lbytes (U32.v short_dcid_len) & FB.lbytes (U32.v pn_length)) pl with
    | (dcid, packet_number) ->
      MShort spin key_phase dcid packet_number
    end
  | (| Long, (| (), (| Initial, (| (), (| pn_length, () |) |) |) |) |) ->
    begin match coerce (common_long_t & (parse_bounded_vlbytes_t 0 token_max_len & payload_length_pn pn_length)) pl with
    | ((version, (dcid, scid)), (token, (payload_length, packet_number))) ->
      MLong version dcid scid (MInitial token payload_length packet_number)
    end
  | (| Long, (| (), (| ZeroRTT, (| (), (| pn_length, () |) |) |) |) |) ->
    begin match coerce (common_long_t & payload_length_pn pn_length) pl with
    | ((version, (dcid, scid)), (payload_length, packet_number)) ->
      MLong version dcid scid (MZeroRTT payload_length packet_number)
    end
  | (| Long, (| (), (| Handshake, (| (), (| pn_length, () |) |) |) |) |) ->
    begin match coerce (common_long_t & payload_length_pn pn_length) pl with
    | ((version, (dcid, scid)), (payload_length, packet_number)) ->
      MLong version dcid scid (MHandshake payload_length packet_number)
    end
  | (| Long, (| (), (| Retry, (unused, ()) |) |) |) ->
    begin match coerce (common_long_t & parse_bounded_vlbytes_t 0 20) pl with
    | ((version, (dcid, scid)), odcid) ->
      MLong version dcid scid (MRetry unused odcid)
    end

[@filter_bitsum'_t_attr]
inline_for_extraction
noextract
let mk_header_body
  (short_dcid_len: short_dcid_len_t)
  (k' : bitsum'_type first_byte)
  (pl: refine_with_tag (first_byte_of_header short_dcid_len (bitsum'_type first_byte) id) k')
: Tot (header_body_type short_dcid_len (bitsum'_key_of_t first_byte k'))
= match k' with
  | (| Short, (| (), (spin, (| (), (key_phase, (| pn_length, () |) ) |) ) |) |) ->
    begin match pl with
    | MShort _ _ dcid pn -> coerce (header_body_type short_dcid_len (bitsum'_key_of_t first_byte k')) ((dcid, pn) <: (FB.lbytes (U32.v short_dcid_len) & FB.lbytes (U32.v pn_length)))
    end
  | (| Long, (| (), (| Initial, (| (), (| pn_length, () |) |) |) |) |) ->
    begin match pl with
    | MLong version dcid scid (MInitial token payload_length packet_number) ->
      coerce (header_body_type short_dcid_len (bitsum'_key_of_t first_byte k')) (((version, (dcid, scid)), (token, (payload_length, packet_number))) <: (common_long_t & (parse_bounded_vlbytes_t 0 token_max_len & payload_length_pn pn_length)))
    end
  | (| Long, (| (), (| ZeroRTT, (| (), (| pn_length, () |) |) |) |) |) ->
    begin match pl with
    | MLong version dcid scid (MZeroRTT payload_length packet_number) ->
      coerce (header_body_type short_dcid_len (bitsum'_key_of_t first_byte k')) (((version, (dcid, scid)), (payload_length, packet_number)) <: (common_long_t & payload_length_pn pn_length))
    end
  | (| Long, (| (), (| Handshake, (| (), (| pn_length, () |) |) |) |) |) ->
    begin match pl with
    | MLong version dcid scid (MHandshake payload_length packet_number) ->
      coerce (header_body_type short_dcid_len (bitsum'_key_of_t first_byte k')) (((version, (dcid, scid)), (payload_length, packet_number)) <: (common_long_t & payload_length_pn pn_length))
    end
  | (| Long, (| (), (| Retry, (unused, ()) |) |) |) ->
    begin match pl with
    | MLong version dcid scid (MRetry unused odcid) ->
      coerce (header_body_type short_dcid_len (bitsum'_key_of_t first_byte k')) (((version, (dcid, scid)), odcid) <: (common_long_t & parse_bounded_vlbytes_t 0 20))
    end

#pop-options

#push-options "--z3rlimit 64 --max_fuel 8 --max_ifuel 8 --initial_fuel 8 --initial_ifuel 8"

[@filter_bitsum'_t_attr]
inline_for_extraction
noextract
let header
  (short_dcid_len: short_dcid_len_t)
: Tot bitsum = BitSum
  _
  _
  _
  first_byte
  _
  (first_byte_of_header short_dcid_len)
  (fun _ _ _ -> ())
  (header_body_type short_dcid_len)
  (SynthCase
    #_ #_ #_ #first_byte #_ #(first_byte_of_header short_dcid_len) #(header_body_type short_dcid_len)
    (mk_header short_dcid_len)
    (fun k x y -> ())
    (mk_header_body short_dcid_len)
    (fun k x -> ())
  )

#pop-options

let parse_common_long : parser _ common_long_t =
  parse_flbytes 4 `nondep_then` (parse_bounded_vlbytes 0 20 `nondep_then` parse_bounded_vlbytes 0 20)

let parse_payload_length_pn
  (pn_length: packet_number_length_t)
: Tot (parser _ (payload_length_pn pn_length))
= parse_varint `nondep_then` parse_flbytes (U32.v pn_length)

#push-options "--z3rlimit 32 --max_fuel 8 --max_ifuel 8 --initial_fuel 8 --initial_ifuel 8"

[@filter_bitsum'_t_attr]
inline_for_extraction
noextract
let parse_header_body
  (short_dcid_len: short_dcid_len_t)
  (k' : bitsum'_key_type (header short_dcid_len).b)
: Tot (k: parser_kind & parser k (bitsum_type_of_tag (header short_dcid_len) k'))
= match coerce (bitsum'_key_type first_byte) k' with
  | (| Short, (| (), (| (), (| pn_length, () |) |) |) |) ->
    (| _, weaken (strong_parser_kind 0 20 None) (parse_flbytes (U32.v short_dcid_len)) `nondep_then` parse_flbytes (U32.v pn_length) |)
  | (| Long, (| (), (| Initial, (| (), (| pn_length, () |) |) |) |) |) ->
    (| _, parse_common_long `nondep_then` (parse_bounded_vlgenbytes 0 token_max_len (parse_bounded_varint 0 token_max_len) `nondep_then` parse_payload_length_pn pn_length) |)
  | (| Long, (| (), (| ZeroRTT, (| (), (| pn_length, () |) |) |) |) |) ->
    (| _, parse_common_long `nondep_then` parse_payload_length_pn pn_length |)
  | (| Long, (| (), (| Handshake, (| (), (| pn_length, () |) |) |) |) |) ->
    (| _, parse_common_long `nondep_then` parse_payload_length_pn pn_length |)
  | (| Long, (| (), (| Retry, () |) |) |) ->
    (| _, parse_common_long `nondep_then` parse_bounded_vlbytes 0 20 |)

[@filter_bitsum'_t_attr]
inline_for_extraction
noextract
let parse_header_kind'
  (short_dcid_len: short_dcid_len_t)
: Tot parser_kind
= parse_bitsum_kind parse_u8_kind (header short_dcid_len) (parse_header_body short_dcid_len)

inline_for_extraction
let parse_header_kind : parser_kind =
  normalize_term (parse_header_kind' 0ul)

let parse_header
  (short_dcid_len: short_dcid_len_t)
: Tot (parser parse_header_kind (header_t short_dcid_len))
= assert_norm (parse_header_kind' short_dcid_len == parse_header_kind);
  parse_bitsum
    (header short_dcid_len)
    parse_u8
    (parse_header_body short_dcid_len)

let serialize_common_long : serializer parse_common_long =
  serialize_flbytes 4 `serialize_nondep_then` (serialize_bounded_vlbytes 0 20 `serialize_nondep_then` serialize_bounded_vlbytes 0 20)

let serialize_payload_length_pn
  (pn_length: packet_number_length_t)
: Tot (serializer (parse_payload_length_pn pn_length))
= serialize_varint `serialize_nondep_then` serialize_flbytes (U32.v pn_length)

[@filter_bitsum'_t_attr]
inline_for_extraction
noextract
let serialize_header_body
  (short_dcid_len: short_dcid_len_t)
  (k' : bitsum'_key_type (header short_dcid_len).b)
: Tot (serializer (dsnd (parse_header_body short_dcid_len k')))
= match coerce (bitsum'_key_type first_byte) k' with
  | (| Short, (| (), (| (), (| pn_length, () |) |) |) |) ->
    serialize_weaken (strong_parser_kind 0 20 None) (serialize_flbytes (U32.v short_dcid_len)) `serialize_nondep_then` serialize_flbytes (U32.v pn_length)
  | (| Long, (| (), (| Initial, (| (), (| pn_length, () |) |) |) |) |) ->
    serialize_common_long `serialize_nondep_then` (serialize_bounded_vlgenbytes 0 token_max_len (serialize_bounded_varint 0 token_max_len) `serialize_nondep_then` serialize_payload_length_pn pn_length)
  | (| Long, (| (), (| ZeroRTT, (| (), (| pn_length, () |) |) |) |) |) ->
    serialize_common_long `serialize_nondep_then` serialize_payload_length_pn pn_length
  | (| Long, (| (), (| Handshake, (| (), (| pn_length, () |) |) |) |) |) ->
    serialize_common_long `serialize_nondep_then` serialize_payload_length_pn pn_length
  | (| Long, (| (), (| Retry, () |) |) |) ->
    serialize_common_long `serialize_nondep_then` serialize_bounded_vlbytes 0 20

let serialize_header
  (short_dcid_len: short_dcid_len_t)
: Tot (serializer (parse_header short_dcid_len))
= assert_norm (parse_header_kind' short_dcid_len == parse_header_kind);
  serialize_bitsum
    (header short_dcid_len)
    serialize_u8
    #(parse_header_body short_dcid_len)
    (serialize_header_body short_dcid_len)

#pop-options
