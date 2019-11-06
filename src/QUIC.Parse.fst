module QUIC.Parse
open QUIC.Spec.Base
open QUIC.Parse.PacketNumber

open FStar.HyperStack.ST

open LowParse.Spec.BitSum

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
let first_byte : bitsum' uint8 8 =
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

(*
// How to test normalization:
module T = FStar.Tactics
let f (x: FStar.UInt8.t) : Tot unit =
  assert (filter_header_byte x == true) by (
    T.norm [primops; iota; zeta; delta_attr [`%filter_bitsum'_t_attr]];
    T.fail "abc"
  )
*)

inline_for_extraction
let short_dcid_len_t = (short_dcid_len: U32.t { U32.v short_dcid_len <= 20 })

module FB = FStar.Bytes

let short_dcid_len_prop
  (short_dcid_len: short_dcid_len_t)
  (h: header)
: GTot Type0
= (MShort? h ==> dcid_len h == U32.v short_dcid_len)

let packet_number_prop
  (last: last_packet_number_t)
  (h: header)
: GTot Type0
= ((~ (is_retry h)) ==> in_window (U32.v (pn_length h) - 1) (U64.v last) (U64.v (packet_number h)))

unfold
let parse_header_prop
  (short_dcid_len: short_dcid_len_t)
  (last: last_packet_number_t)
  (m: header)
: GTot Type0
= short_dcid_len_prop short_dcid_len m /\
  packet_number_prop last m

inline_for_extraction
type header'
  (short_dcid_len: short_dcid_len_t)
  (last: last_packet_number_t)
= (m: header { parse_header_prop short_dcid_len last m })

open LowParse.Spec.Bytes

#push-options "--z3rlimit 16"

inline_for_extraction
noextract
let first_byte_of_header
  (short_dcid_len: short_dcid_len_t)
  (last: last_packet_number_t)
  (t: Type0)
  (f: (bitsum'_type first_byte -> Tot t))
  (m: header' short_dcid_len last)
: Tot t
= match m with
  | MShort spin key_phase dcid pn_length packet_number ->
    let spin : bitfield uint8 1 = if spin then 1uy else 0uy in
    let key_phase : bitfield uint8 1 = if key_phase then 1uy else 0uy in
    f (| Short, (| (), (spin, (| (), (key_phase, (| pn_length, () |) ) |) ) |) |)
  | MLong version dcid scid spec ->
    begin match spec with
    | MInitial _ payload_length pn_length _ ->
      f (| Long, (| (), (| Initial, (| (), (| pn_length, () |) |) |) |) |)
    | MZeroRTT payload_length pn_length _ ->
      f (| Long, (| (), (| ZeroRTT, (| (), (| pn_length, () |) |) |) |) |)
    | MHandshake payload_length pn_length _ ->
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
  (last: last_packet_number_t)
  (pn_length: packet_number_length_t)
: Tot Type0
= (uint62_t & packet_number_t last pn_length)

#push-options "--z3rlimit 16 --max_fuel 8 --max_ifuel 8 --initial_fuel 8 --initial_ifuel 8"

[@filter_bitsum'_t_attr]
inline_for_extraction
noextract
let header_body_type
  (short_dcid_len: short_dcid_len_t)
  (last: last_packet_number_t)
  (k' : bitsum'_key_type first_byte)
: Tot Type0
= match k' with
  | (| Short, (| (), (| (), (| pn_length, () |) |) |) |) ->
    (FB.lbytes (U32.v short_dcid_len) & packet_number_t last pn_length)
  | (| Long, (| (), (| Initial, (| (), (| pn_length, () |) |) |) |) |) ->
    (common_long_t & (parse_bounded_vlbytes_t 0 token_max_len & payload_length_pn last pn_length))
  | (| Long, (| (), (| ZeroRTT, (| (), (| pn_length, () |) |) |) |) |) ->
    (common_long_t & payload_length_pn last pn_length)
  | (| Long, (| (), (| Handshake, (| (), (| pn_length, () |) |) |) |) |) ->
    (common_long_t & payload_length_pn last pn_length)
  | (| Long, (| (), (| Retry, () |) |) |) ->
    (common_long_t & parse_bounded_vlbytes_t 0 20)

open LowParse.Spec.BitSum // again, for coerce

#pop-options

#push-options "--z3rlimit 64 --max_fuel 8 --max_ifuel 8 --initial_fuel 8 --initial_ifuel 8"

[@filter_bitsum'_t_attr]
inline_for_extraction
noextract
let mk_header
  (short_dcid_len: short_dcid_len_t)
  (last: last_packet_number_t)
  (k' : bitsum'_type first_byte)
  (pl: header_body_type short_dcid_len last (bitsum'_key_of_t first_byte k'))
: Tot (refine_with_tag (first_byte_of_header short_dcid_len last (bitsum'_type first_byte) id) k')
= match k' with
  | (| Short, (| (), (spin, (| (), (key_phase, (| pn_length, () |) ) |) ) |) |) ->
    let spin = (spin = 1uy) in
    let key_phase = (key_phase = 1uy) in
    begin match coerce (FB.lbytes (U32.v short_dcid_len) & packet_number_t last pn_length) pl with
    | (dcid, packet_number) ->
      MShort spin key_phase dcid pn_length packet_number
    end
  | (| Long, (| (), (| Initial, (| (), (| pn_length, () |) |) |) |) |) ->
    begin match coerce (common_long_t & (parse_bounded_vlbytes_t 0 token_max_len & payload_length_pn last pn_length)) pl with
    | ((version, (dcid, scid)), (token, (payload_length, packet_number))) ->
      MLong version dcid scid (MInitial token payload_length pn_length packet_number)
    end
  | (| Long, (| (), (| ZeroRTT, (| (), (| pn_length, () |) |) |) |) |) ->
    begin match coerce (common_long_t & payload_length_pn last pn_length) pl with
    | ((version, (dcid, scid)), (payload_length, packet_number)) ->
      MLong version dcid scid (MZeroRTT payload_length pn_length packet_number)
    end
  | (| Long, (| (), (| Handshake, (| (), (| pn_length, () |) |) |) |) |) ->
    begin match coerce (common_long_t & payload_length_pn last pn_length) pl with
    | ((version, (dcid, scid)), (payload_length, packet_number)) ->
      MLong version dcid scid (MHandshake payload_length pn_length packet_number)
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
  (last: last_packet_number_t)
  (k' : bitsum'_type first_byte)
  (pl: refine_with_tag (first_byte_of_header short_dcid_len last (bitsum'_type first_byte) id) k')
: Tot (header_body_type short_dcid_len last (bitsum'_key_of_t first_byte k'))
= match k' with
  | (| Short, (| (), (spin, (| (), (key_phase, (| pn_length, () |) ) |) ) |) |) ->
    begin match pl with
    | MShort _ _ dcid _ pn -> coerce (header_body_type short_dcid_len last (bitsum'_key_of_t first_byte k')) ((dcid, pn) <: (FB.lbytes (U32.v short_dcid_len) & packet_number_t last pn_length ))
    end
  | (| Long, (| (), (| Initial, (| (), (| pn_length, () |) |) |) |) |) ->
    begin match pl with
    | MLong version dcid scid (MInitial token payload_length _ packet_number) ->
      coerce (header_body_type short_dcid_len last (bitsum'_key_of_t first_byte k')) (((version, (dcid, scid)), (token, (payload_length, packet_number))) <: (common_long_t & (parse_bounded_vlbytes_t 0 token_max_len & payload_length_pn last pn_length)))
    end
  | (| Long, (| (), (| ZeroRTT, (| (), (| pn_length, () |) |) |) |) |) ->
    begin match pl with
    | MLong version dcid scid (MZeroRTT payload_length _ packet_number) ->
      coerce (header_body_type short_dcid_len last (bitsum'_key_of_t first_byte k')) (((version, (dcid, scid)), (payload_length, packet_number)) <: (common_long_t & payload_length_pn last pn_length))
    end
  | (| Long, (| (), (| Handshake, (| (), (| pn_length, () |) |) |) |) |) ->
    begin match pl with
    | MLong version dcid scid (MHandshake payload_length _ packet_number) ->
      coerce (header_body_type short_dcid_len last (bitsum'_key_of_t first_byte k')) (((version, (dcid, scid)), (payload_length, packet_number)) <: (common_long_t & payload_length_pn last pn_length))
    end
  | (| Long, (| (), (| Retry, (unused, ()) |) |) |) ->
    begin match pl with
    | MLong version dcid scid (MRetry unused odcid) ->
      coerce (header_body_type short_dcid_len last (bitsum'_key_of_t first_byte k')) (((version, (dcid, scid)), odcid) <: (common_long_t & parse_bounded_vlbytes_t 0 20))
    end

[@filter_bitsum'_t_attr]
inline_for_extraction
noextract
let header_sum
  (short_dcid_len: short_dcid_len_t)
  (last: last_packet_number_t)
: Tot bitsum = BitSum
  _
  _
  _
  first_byte
  _
  (first_byte_of_header short_dcid_len last)
  (fun _ _ _ -> ())
  (header_body_type short_dcid_len last)
  (SynthCase
    #_ #_ #_ #first_byte #_ #(first_byte_of_header short_dcid_len last) #(header_body_type short_dcid_len last)
    (mk_header short_dcid_len last)
    (fun k x y -> ())
    (mk_header_body short_dcid_len last)
    (fun k x -> ())
  )

#pop-options

let parse_common_long : parser _ common_long_t =
  parse_flbytes 4 `nondep_then` (parse_bounded_vlbytes 0 20 `nondep_then` parse_bounded_vlbytes 0 20)

open QUIC.Parse.VarInt

let parse_payload_length_pn
  (last: last_packet_number_t)
  (pn_length: packet_number_length_t)
: Tot (parser _ (payload_length_pn last pn_length))
= parse_varint `nondep_then` parse_packet_number last pn_length

#push-options "--z3rlimit 64 --max_fuel 8 --max_ifuel 8 --initial_fuel 8 --initial_ifuel 8"

[@filter_bitsum'_t_attr]
inline_for_extraction
noextract
let parse_header_body
  (short_dcid_len: short_dcid_len_t)
  (last: last_packet_number_t)
  (k' : bitsum'_key_type (header_sum short_dcid_len last).b)
: Tot (k: parser_kind & parser k (bitsum_type_of_tag (header_sum short_dcid_len last) k'))
= match coerce (bitsum'_key_type first_byte) k' with
  | (| Short, (| (), (| (), (| pn_length, () |) |) |) |) ->
    (| _, weaken (strong_parser_kind 0 20 None) (parse_flbytes (U32.v short_dcid_len)) `nondep_then` parse_packet_number last pn_length |)
  | (| Long, (| (), (| Initial, (| (), (| pn_length, () |) |) |) |) |) ->
    (| _, parse_common_long `nondep_then` (parse_bounded_vlgenbytes 0 token_max_len (parse_bounded_varint 0 token_max_len) `nondep_then` parse_payload_length_pn last pn_length) |)
  | (| Long, (| (), (| ZeroRTT, (| (), (| pn_length, () |) |) |) |) |) ->
    (| _, parse_common_long `nondep_then` parse_payload_length_pn last pn_length |)
  | (| Long, (| (), (| Handshake, (| (), (| pn_length, () |) |) |) |) |) ->
    (| _, parse_common_long `nondep_then` parse_payload_length_pn last pn_length |)
  | (| Long, (| (), (| Retry, () |) |) |) ->
    (| _, parse_common_long `nondep_then` parse_bounded_vlbytes 0 20 |)

[@filter_bitsum'_t_attr]
inline_for_extraction
noextract
let parse_header_kind'
  (short_dcid_len: short_dcid_len_t)
  (last: last_packet_number_t)
: Tot parser_kind
= parse_bitsum_kind parse_u8_kind (header_sum short_dcid_len last) (parse_header_body short_dcid_len last)

inline_for_extraction
noextract
let parse_header_kind : parser_kind =
  normalize_term (parse_header_kind' 0ul 0uL)

let lp_parse_header
  (short_dcid_len: short_dcid_len_t)
  (last: last_packet_number_t)
: Tot (parser parse_header_kind (header' short_dcid_len last))
= assert_norm (parse_header_kind' short_dcid_len last == parse_header_kind);
  parse_bitsum
    (header_sum short_dcid_len last)
    parse_u8
    (parse_header_body short_dcid_len last)

let serialize_common_long : serializer parse_common_long =
  serialize_flbytes 4 `serialize_nondep_then` (serialize_bounded_vlbytes 0 20 `serialize_nondep_then` serialize_bounded_vlbytes 0 20)

let serialize_payload_length_pn
  (last: last_packet_number_t)
  (pn_length: packet_number_length_t)
: Tot (serializer (parse_payload_length_pn last pn_length))
= serialize_varint `serialize_nondep_then` serialize_packet_number last pn_length

let serialize_header_body
  (short_dcid_len: short_dcid_len_t)
  (last: last_packet_number_t)
  (k' : bitsum'_key_type (header_sum short_dcid_len last).b)
: Tot (serializer (dsnd (parse_header_body short_dcid_len last k')))
= match coerce (bitsum'_key_type first_byte) k' with
  | (| Short, (| (), (| (), (| pn_length, () |) |) |) |) ->
    serialize_weaken (strong_parser_kind 0 20 None) (serialize_flbytes (U32.v short_dcid_len)) `serialize_nondep_then` serialize_packet_number last pn_length
  | (| Long, (| (), (| Initial, (| (), (| pn_length, () |) |) |) |) |) ->
    serialize_common_long `serialize_nondep_then` (serialize_bounded_vlgenbytes 0 token_max_len (serialize_bounded_varint 0 token_max_len) `serialize_nondep_then` serialize_payload_length_pn last pn_length)
  | (| Long, (| (), (| ZeroRTT, (| (), (| pn_length, () |) |) |) |) |) ->
    serialize_common_long `serialize_nondep_then` serialize_payload_length_pn last pn_length
  | (| Long, (| (), (| Handshake, (| (), (| pn_length, () |) |) |) |) |) ->
    serialize_common_long `serialize_nondep_then` serialize_payload_length_pn last pn_length
  | (| Long, (| (), (| Retry, () |) |) |) ->
    serialize_common_long `serialize_nondep_then` serialize_bounded_vlbytes 0 20

let serialize_header
  (short_dcid_len: short_dcid_len_t)
  (last: last_packet_number_t)
: Tot (serializer (lp_parse_header short_dcid_len last))
= assert_norm (parse_header_kind' short_dcid_len last == parse_header_kind);
  serialize_bitsum
    (header_sum short_dcid_len last)
    serialize_u8
    #(parse_header_body short_dcid_len last)
    (serialize_header_body short_dcid_len last)

module LC = LowParse.Low.Combinators
module LB = LowParse.Low.Bytes
module LI = LowParse.Low.BoundedInt
module LJ = LowParse.Low.Int
module LL = LowParse.Low.BitSum

inline_for_extraction
let validate_common_long : LC.validator parse_common_long =
  LB.validate_flbytes 4 4ul `LC.validate_nondep_then` (LB.validate_bounded_vlbytes 0 20 `LC.validate_nondep_then` LB.validate_bounded_vlbytes 0 20)

inline_for_extraction
noextract
let validate_payload_length_pn
  (last: last_packet_number_t)
  (pn_length: packet_number_length_t)
: Tot (LC.validator (parse_payload_length_pn last pn_length))
= validate_varint `LC.validate_nondep_then` validate_packet_number last pn_length

[@filter_bitsum'_t_attr]
inline_for_extraction
noextract
let validate_header_body_cases
  (short_dcid_len: short_dcid_len_t)
  (last: last_packet_number_t)
  (k' : bitsum'_key_type (header_sum short_dcid_len last).b)
: Tot (LC.validator (dsnd (parse_header_body short_dcid_len last k')))
= match coerce (bitsum'_key_type first_byte) k' with
  | (| Short, (| (), (| (), (| pn_length, () |) |) |) |) ->
    LC.validate_weaken (strong_parser_kind 0 20 None) (LB.validate_flbytes (U32.v short_dcid_len) short_dcid_len) () `LC.validate_nondep_then` validate_packet_number last pn_length
  | (| Long, (| (), (| Initial, (| (), (| pn_length, () |) |) |) |) |) ->
    validate_common_long `LC.validate_nondep_then` (LB.validate_bounded_vlgenbytes 0 0ul token_max_len (U32.uint_to_t token_max_len) (validate_bounded_varint 0ul (U32.uint_to_t token_max_len)) (read_bounded_varint 0 token_max_len) `LC.validate_nondep_then` validate_payload_length_pn last pn_length)
  | (| Long, (| (), (| ZeroRTT, (| (), (| pn_length, () |) |) |) |) |) ->
    validate_common_long `LC.validate_nondep_then` validate_payload_length_pn last pn_length
  | (| Long, (| (), (| Handshake, (| (), (| pn_length, () |) |) |) |) |) ->
    validate_common_long `LC.validate_nondep_then` validate_payload_length_pn last pn_length
  | (| Long, (| (), (| Retry, () |) |) |) ->
    validate_common_long `LC.validate_nondep_then` LB.validate_bounded_vlbytes 0 20

let filter_first_byte'
: (filter_bitsum'_t first_byte)
= norm [primops; iota; zeta; delta_attr [`%filter_bitsum'_t_attr]]
  (mk_filter_bitsum'_t' first_byte)

inline_for_extraction
let filter_first_byte
  (short_dcid_len: short_dcid_len_t)
  (last: last_packet_number_t)
: Tot (filter_bitsum'_t (header_sum short_dcid_len last).b)
= coerce (filter_bitsum'_t (header_sum short_dcid_len last).b) filter_first_byte'

inline_for_extraction
noextract
let mk_validate_header_body_cases'
: LL.validate_bitsum_cases_t first_byte
= norm [primops; iota; zeta; delta_attr [`%filter_bitsum'_t_attr]]
  (LL.mk_validate_bitsum_cases_t' first_byte)

inline_for_extraction
noextract
let mk_validate_header_body_cases
  (short_dcid_len: short_dcid_len_t)
  (last: last_packet_number_t)
: LL.validate_bitsum_cases_t (header_sum short_dcid_len last).b
= coerce (LL.validate_bitsum_cases_t (header_sum short_dcid_len last).b) mk_validate_header_body_cases' 

let validate_header
  (short_dcid_len: short_dcid_len_t)
  (last: last_packet_number_t)
: Tot (LL.validator (lp_parse_header short_dcid_len last))
= assert_norm (parse_header_kind' short_dcid_len last == parse_header_kind);
  LL.validate_bitsum
    (header_sum short_dcid_len last)
    (LJ.validate_u8 ())
    LJ.read_u8
    (filter_first_byte short_dcid_len last)
    (parse_header_body short_dcid_len last)
    (validate_header_body_cases short_dcid_len last)
    (mk_validate_header_body_cases short_dcid_len last)

#pop-options

(* Properties of the serializer *)

let serialize_header_ext
  (cid_len1 cid_len2: short_dcid_len_t)
  (last1 last2: last_packet_number_t)
  (x: header)
: Lemma
  (requires (
    parse_header_prop cid_len1 last1 x /\
    parse_header_prop cid_len2 last2 x
  ))
  (ensures (
    serialize (serialize_header cid_len1 last1) x == serialize (serialize_header cid_len2 last2) x
  ))
= admit ()

(* Fulfill the interface *)

let last_packet_number
  (h: header)
: Tot last_packet_number_t
= if is_retry h then 0uL else let pn = packet_number h in if pn = 0uL then 0uL else pn `U64.sub` 1uL

#push-options "--z3rlimit 32"

let parse_header_prop_intro
  (h: header)
: Lemma
  (parse_header_prop (U32.uint_to_t (dcid_len h)) (last_packet_number h) h)
= ()

#pop-options

let format_header' (h: header) : GTot bytes =
  parse_header_prop_intro h;
  serialize (serialize_header (U32.uint_to_t (dcid_len h)) (last_packet_number h)) h

let header_len h =
  parse_header_prop_intro h;
  Seq.length (format_header' h)

let format_header h = format_header' h

#push-options "--z3rlimit 32"

let format_header_is_short h =
  parse_header_prop_intro h;
  let dl = U32.uint_to_t (dcid_len h) in
  let last = last_packet_number h in
  serialize_bitsum_eq (header_sum dl last) LI.serialize_u8 (serialize_header_body dl last) h;
  let b = header_sum dl last in
  let tg = b.tag_of_data (bitsum'_type b.b) id h in
  let x = synth_bitsum'_recip b.b tg in
  LI.serialize_u8_spec x;
  assert (Seq.index (format_header h) 0 == x);
  assert (MShort? h <==> uint8.get_bitfield (Seq.index (format_header h) 0) 7 8 == (LowParse.Spec.Enum.enum_repr_of_key header_form Short <: U8.t))

#pop-options

let format_header_is_retry h = admit ()

let format_header_pn_length h = admit ()

let pn_offset h = admit ()

let putative_pn_offset cid_len x = admit ()

let putative_pn_offset_frame cid_len x1 x2 = admit ()

let putative_pn_offset_correct h cid_len = admit ()

let parse_header cid_len last b =
  match parse (lp_parse_header (U32.uint_to_t cid_len) (U64.uint_to_t last)) b with
  | None -> H_Failure
  | Some (h, consumed) -> H_Success h (Seq.slice b consumed (Seq.length b))

module Seq = FStar.Seq

#push-options "--z3rlimit 128"

let lemma_header_parsing_correct
  h c cid_len last
=
  parse_header_prop_intro h;
  serialize_header_ext (U32.uint_to_t (dcid_len h)) (U32.uint_to_t cid_len) (last_packet_number h) (U64.uint_to_t last) h;
  let s = format_header h in
  assert (s == serialize (serialize_header (U32.uint_to_t cid_len) (U64.uint_to_t last)) h);
  parse_serialize (serialize_header (U32.uint_to_t cid_len) (U64.uint_to_t last)) h;
  parse_strong_prefix (lp_parse_header (U32.uint_to_t cid_len) (U64.uint_to_t last)) s (s `Seq.append` c);
  match parse_header cid_len last Seq.(format_header h @| c) with
  | H_Failure -> ()
  | H_Success h' c' -> assert (h == h' /\ c `Seq.equal` c')

let lemma_header_parsing_safe
  cid_len last b1 b2
= match parse_header cid_len last b1 with
  | H_Failure -> ()
  | H_Success h1 c1 ->
    let consumed = Seq.length b1 - Seq.length c1 in
    assert (Some? (parse (lp_parse_header (U32.uint_to_t cid_len) (U64.uint_to_t last)) b1)); //  == Some (h1, consumed));
    let Some (h1', consumed') = parse (lp_parse_header (U32.uint_to_t cid_len) (U64.uint_to_t last)) b1 in
    assert (h1 == h1');
    let consumed' : consumed_length b1 = consumed' in
    assert (consumed' <= Seq.length b1);
    assert (c1 == Seq.slice b1 consumed' (Seq.length b1));
    assert (consumed == consumed');
    parse_injective (lp_parse_header (U32.uint_to_t cid_len) (U64.uint_to_t last)) b1 b2;
    Seq.lemma_split b1 consumed;
    assert (parse_header cid_len last b2 == H_Success h1 c1);
    Seq.lemma_split b2 consumed;
    assert (b1 == b2)

#pop-options

(*
  match parse_header cid_len last b1, parse_header cid_len last b2 with
  | H_Failure, _ -> ()
  | H_Success h1 c1, H_Success h2 c2 -> assert (h1 == h2 /\ c1 `Seq.equal` c2); assume (b1 == b2)
  | _ -> assert False
*)

(*
let parse_header  cid_len b =

let test b =
  let sl = LowParse.Slice.make_slice b 42ul in
  validate_header 18ul sl 0ul
