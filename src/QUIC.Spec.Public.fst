module QUIC.Spec.Public

module LP = LowParse.Spec
module LPB = LowParse.Spec.BitSum

inline_for_extraction
type header_form_t =
  | Long
  | Short

[@LPB.filter_bitsum'_t_attr]
inline_for_extraction
noextract
let header_form : LP.enum header_form_t (LPB.bitfield LPB.uint8 1) = [
  Long, 1uy;
  Short, 0uy;
]

[@LPB.filter_bitsum'_t_attr]
inline_for_extraction
noextract
let fixed_bit : LP.enum unit (LPB.bitfield LPB.uint8 1) = [
  (), 1uy;
]

inline_for_extraction
type long_packet_type_t =
  | Initial
  | ZeroRTT
  | Handshake
  | Retry

[@LPB.filter_bitsum'_t_attr]
inline_for_extraction
noextract
let long_packet_type : LP.enum long_packet_type_t (LPB.bitfield LPB.uint8 2) = [
  Initial, 0uy;
  ZeroRTT, 1uy;
  Handshake, 2uy;
  Retry, 3uy;
]

[@LPB.filter_bitsum'_t_attr]
inline_for_extraction
noextract
let first_byte : LPB.bitsum' LPB.uint8 8 =
  LPB.BitSum' _ _ header_form (function
    | Short ->
      LPB.BitSum' _ _ fixed_bit (fun _ ->
        LPB.BitField (* spin bit *) 1 (
          LPB.BitField (* protected bits *) 5 (
            LPB.BitStop ()
          )
        )
      )
    | Long ->
      LPB.BitSum' _ _ fixed_bit (fun _ ->
        LPB.BitSum' _ _ long_packet_type (function
          | _ -> LPB.BitField (* protected bits *) 4 (LPB.BitStop ())
        )
      )
  )

module U32 = FStar.UInt32

inline_for_extraction
let short_dcid_len_t = (short_dcid_len: U32.t { U32.v short_dcid_len <= 20 })

inline_for_extraction
noextract
let token_max_len = 16383 // arbitrary bound

module FB = FStar.Bytes

inline_for_extraction
let vlbytes (min: nat) (max: nat) =
  (x: FB.bytes { min <= FB.length x /\ FB.length x <= max })

module U64 = FStar.UInt64

inline_for_extraction
let uint62_bound : (uint62_bound: U64.t { U64.v uint62_bound == pow2 62 }) =
  [@inline_let] let v = 4611686018427387904uL in
  [@inline_let] let _ = assert_norm (U64.v v == pow2 62) in
  v

inline_for_extraction
let uint62_t = (x: U64.t { U64.v x < U64.v uint62_bound })

module U8 = FStar.UInt8

inline_for_extraction
noextract
let bitfield
  (sz: nat { sz <= 8 })
: Tot eqtype
= (x: U8.t { U8.v x < pow2 sz })

inline_for_extraction
let payload_and_pn_length_t : Type0 =
  (payload_and_pn_length: uint62_t { U64.v payload_and_pn_length >= 20 })

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

#push-options "--z3rlimit 16"

inline_for_extraction
noextract
let first_byte_of_header'
  (short_dcid_len: short_dcid_len_t)
  (t: Type0)
  (f: (LPB.bitsum'_type first_byte -> Tot t))
  (m: header' short_dcid_len)
: Tot t
= match m with
  | PShort protected_bits spin dcid ->
    let spin : LPB.bitfield LPB.uint8 1 = if spin then 1uy else 0uy in
    f (| Short, (| (), (spin, (protected_bits, () ) ) |) |)
  | PLong protected_bits version dcid scid spec ->
    begin match spec with
    | PInitial _ payload_and_pn_length ->
      f (| Long, (| (), (| Initial, (protected_bits, () ) |) |) |)
    | PZeroRTT payload_and_pn_length ->
      f (| Long, (| (), (| ZeroRTT, (protected_bits, () ) |) |) |)
    | PHandshake payload_and_pn_length ->
      f (| Long, (| (), (| Handshake, (protected_bits, () ) |) |) |)
    | PRetry _ ->
      f (| Long, (| (), (| Retry, (protected_bits, () ) |) |) |)
    end

#pop-options

let first_byte_of_header
  (short_dcid_len: short_dcid_len_t)
  (m: header' short_dcid_len)
: Tot (LPB.bitsum'_type first_byte)
= first_byte_of_header' short_dcid_len (LPB.bitsum'_type first_byte) id m

[@LPB.filter_bitsum'_t_attr]
inline_for_extraction
noextract
let common_long_t
: Type0
= (U32.t & (LP.parse_bounded_vlbytes_t 0 20 & LP.parse_bounded_vlbytes_t 0 20))

inline_for_extraction
let payload_and_pn_length_prop
  (x: uint62_t)
: Tot bool
= x `U64.gte` 20uL

let payload_and_pn_length_t' = LP.parse_filter_refine payload_and_pn_length_prop

#push-options "--z3rlimit 32 --max_fuel 8 --max_ifuel 8 --initial_fuel 8 --initial_ifuel 8"

let long_zero_rtt_body_t = (common_long_t & payload_and_pn_length_t')
let long_handshake_body_t = (common_long_t & payload_and_pn_length_t')
let long_retry_body_t = (common_long_t & LP.parse_bounded_vlbytes_t 0 20)
let long_initial_body_t = (common_long_t & (LP.parse_bounded_vlbytes_t 0 token_max_len & payload_and_pn_length_t'))

[@LPB.filter_bitsum'_t_attr]
inline_for_extraction
noextract
let header_body_type
  (short_dcid_len: short_dcid_len_t)
  (k' : LPB.bitsum'_key_type first_byte)
: Tot Type0
= match k' with
  | (| Long, (| (), (| Initial, () |) |) |) ->
    long_initial_body_t
  | (| Long, (| (), (| ZeroRTT, () |) |) |) ->
    long_zero_rtt_body_t
  | (| Long, (| (), (| Handshake, () |) |) |) ->
    long_handshake_body_t
  | (| Long, (| (), (| Retry, () |) |) |) ->
    long_retry_body_t
  | (| Short, (| (), () |) |) ->
    FB.lbytes (U32.v short_dcid_len)

[@LPB.filter_bitsum'_t_attr]
inline_for_extraction
noextract
let mk_header
  (short_dcid_len: short_dcid_len_t)
  (k' : LPB.bitsum'_type first_byte)
  (pl: header_body_type short_dcid_len (LPB.bitsum'_key_of_t first_byte k'))
: Tot (LP.refine_with_tag (first_byte_of_header short_dcid_len) k')
= match k' with
  | (| Short, (| (), (spin, (protected_bits, ()) ) |) |) ->
    let spin = (spin = 1uy) in
    let dcid = LP.coerce (FB.lbytes (U32.v short_dcid_len)) pl in
    PShort protected_bits spin dcid
  | (| Long, (| (), (| Initial, (protected_bits, ()) |) |) |) ->
    begin match LP.coerce (common_long_t & (LP.parse_bounded_vlbytes_t 0 token_max_len & payload_and_pn_length_t')) pl with
    | ((version, (dcid, scid)), (token, (payload_and_pn_length))) ->
      PLong protected_bits version dcid scid (PInitial token payload_and_pn_length)
    end
  | (| Long, (| (), (| ZeroRTT, (protected_bits, ()) |) |) |) ->
    begin match LP.coerce (common_long_t & payload_and_pn_length_t') pl with
    | ((version, (dcid, scid)), payload_and_pn_length) ->
      PLong protected_bits version dcid scid (PZeroRTT payload_and_pn_length)
    end
  | (| Long, (| (), (| Handshake, (protected_bits, ()) |) |) |) ->
    begin match LP.coerce (common_long_t & payload_and_pn_length_t') pl with
    | ((version, (dcid, scid)), (payload_and_pn_length)) ->
      PLong protected_bits version dcid scid (PHandshake (payload_and_pn_length))
    end
  | (| Long, (| (), (| Retry, (protected_bits, ()) |) |) |) ->
    begin match LP.coerce (common_long_t & LP.parse_bounded_vlbytes_t 0 20) pl with
    | ((version, (dcid, scid)), odcid) ->
      PLong protected_bits version dcid scid (PRetry odcid)
    end

[@LPB.filter_bitsum'_t_attr]
inline_for_extraction
noextract
let mk_header_body
  (short_dcid_len: short_dcid_len_t)
  (k' : LPB.bitsum'_type first_byte)
  (pl: LP.refine_with_tag (first_byte_of_header short_dcid_len) k')
: Tot (header_body_type short_dcid_len (LPB.bitsum'_key_of_t first_byte k'))
= match k' with
  | (| Short, (| (), (spin, (protected_bits, ())) |) |) ->
    begin match pl with
    | PShort _ _ dcid -> LP.coerce (header_body_type short_dcid_len (LPB.bitsum'_key_of_t first_byte k')) ((dcid) <: (FB.lbytes (U32.v short_dcid_len)))
    end
  | (| Long, (| (), (| Initial, (protected_bits, ()) |) |) |) ->
    begin match pl with
    | PLong _ version dcid scid (PInitial token payload_and_pn_length) ->
      LP.coerce (header_body_type short_dcid_len (LPB.bitsum'_key_of_t first_byte k')) (((version, (dcid, scid)), (token, (payload_and_pn_length))) <: (common_long_t & (LP.parse_bounded_vlbytes_t 0 token_max_len & payload_and_pn_length_t')))
    end
  | (| Long, (| (), (| ZeroRTT, (protected_bits, ()) |) |) |) ->
    begin match pl with
    | PLong _ version dcid scid (PZeroRTT payload_and_pn_length) ->
      LP.coerce (header_body_type short_dcid_len (LPB.bitsum'_key_of_t first_byte k')) (((version, (dcid, scid)), (payload_and_pn_length)) <: (common_long_t & payload_and_pn_length_t'))
    end
  | (| Long, (| (), (| Handshake, (protected_bits, ()) |) |) |) ->
    begin match pl with
    | PLong _ version dcid scid (PHandshake payload_and_pn_length) ->
      LP.coerce (header_body_type short_dcid_len (LPB.bitsum'_key_of_t first_byte k')) (((version, (dcid, scid)), (payload_and_pn_length)) <: (common_long_t & payload_and_pn_length_t'))
    end
  | (| Long, (| (), (| Retry, (protected_bits, ()) |) |) |) ->
    begin match pl with
    | PLong _ version dcid scid (PRetry odcid) ->
      LP.coerce (header_body_type short_dcid_len (LPB.bitsum'_key_of_t first_byte k')) (((version, (dcid, scid)), odcid) <: (common_long_t & LP.parse_bounded_vlbytes_t 0 20))
    end

[@LPB.filter_bitsum'_t_attr]
inline_for_extraction
noextract
let header_synth
  (short_dcid_len: short_dcid_len_t)
: Tot (LPB.synth_case_t first_byte (header' short_dcid_len) (first_byte_of_header short_dcid_len) (header_body_type short_dcid_len))
= 
  (LPB.SynthCase
    #_ #_ #_ #first_byte #_ #(first_byte_of_header short_dcid_len) #(header_body_type short_dcid_len)
    (mk_header short_dcid_len)
    (fun k x y -> ())
    (mk_header_body short_dcid_len)
    (fun k x -> ())
  )

let parse_common_long : LP.parser _ common_long_t =
  LP.parse_u32 `LP.nondep_then` (LP.parse_bounded_vlbytes 0 20 `LP.nondep_then` LP.parse_bounded_vlbytes 0 20)

module VI = QUIC.Spec.VarInt

let parse_payload_and_pn_length : LP.parser _ payload_and_pn_length_t' =
  LP.parse_filter VI.parse_varint payload_and_pn_length_prop

let parse_long_zero_rtt_body : LP.parser _ long_zero_rtt_body_t = parse_common_long `LP.nondep_then` parse_payload_and_pn_length
let parse_long_handshake_body : LP.parser _ long_handshake_body_t = parse_common_long `LP.nondep_then` parse_payload_and_pn_length
let parse_long_retry_body : LP.parser _ long_retry_body_t = parse_common_long `LP.nondep_then` LP.parse_bounded_vlbytes 0 20
let parse_long_initial_body : LP.parser _ long_initial_body_t = parse_common_long `LP.nondep_then` (
      LP.parse_bounded_vlgenbytes 0 token_max_len (VI.parse_bounded_varint 0 token_max_len) `LP.nondep_then` parse_payload_and_pn_length)

[@LPB.filter_bitsum'_t_attr]
inline_for_extraction
noextract
let parse_header_body
  (short_dcid_len: short_dcid_len_t)
  (k' : LPB.bitsum'_key_type first_byte)
: Tot (k: LP.parser_kind & LP.parser k (header_body_type short_dcid_len k'))
= match k' with
  | (| Short, (| (), () |) |) ->
    (| _ , LP.weaken (LP.strong_parser_kind 0 20 None) (LP.parse_flbytes (U32.v short_dcid_len)) |)
  | (| Long, (| (), (| Initial, () |) |) |) ->
    (| _, parse_long_initial_body  |)
  | (| Long, (| (), (| ZeroRTT, () |) |) |) ->
    (| _, parse_long_zero_rtt_body |)
  | (| Long, (| (), (| Handshake, () |) |) |) ->
    (| _, parse_long_handshake_body |)
  | (| Long, (| (), (| Retry, () |) |) |) ->
    (| _, parse_long_retry_body |)

[@LPB.filter_bitsum'_t_attr]
inline_for_extraction
noextract
let parse_header_kind'
  (short_dcid_len: short_dcid_len_t)
: Tot LP.parser_kind
= LPB.parse_bitsum_kind LP.parse_u8_kind first_byte (header_body_type short_dcid_len) (parse_header_body short_dcid_len)

let parse_header
  (short_dcid_len: short_dcid_len_t)
: Tot (LP.parser (parse_header_kind' short_dcid_len) (header' short_dcid_len))
= LPB.parse_bitsum
    first_byte
    (first_byte_of_header short_dcid_len)
    (header_body_type short_dcid_len)
    (header_synth short_dcid_len)
    LP.parse_u8
    (parse_header_body short_dcid_len)

let serialize_common_long : LP.serializer parse_common_long =
  LP.serialize_u32 `LP.serialize_nondep_then` (LP.serialize_bounded_vlbytes 0 20 `LP.serialize_nondep_then` LP.serialize_bounded_vlbytes 0 20)

let serialize_payload_and_pn_length : LP.serializer parse_payload_and_pn_length =
  LP.serialize_filter VI.serialize_varint payload_and_pn_length_prop

let serialize_long_zero_rtt_body : LP.serializer parse_long_zero_rtt_body = serialize_common_long `LP.serialize_nondep_then` serialize_payload_and_pn_length
let serialize_long_handshake_body : LP.serializer parse_long_handshake_body = serialize_common_long `LP.serialize_nondep_then` serialize_payload_and_pn_length
let serialize_long_retry_body : LP.serializer parse_long_retry_body = serialize_common_long `LP.serialize_nondep_then` LP.serialize_bounded_vlbytes 0 20
let serialize_long_initial_body : LP.serializer parse_long_initial_body = serialize_common_long `LP.serialize_nondep_then` (
      LP.serialize_bounded_vlgenbytes 0 token_max_len (VI.serialize_bounded_varint 0 token_max_len) `LP.serialize_nondep_then` serialize_payload_and_pn_length)

let serialize_header_body
  (short_dcid_len: short_dcid_len_t)
  (k' : LPB.bitsum'_key_type first_byte)
: Tot (LP.serializer (dsnd (parse_header_body short_dcid_len k')))
= match LP.coerce (LPB.bitsum'_key_type first_byte) k' with
  | (| Short, (| (), () |) |) ->
    LP.serialize_weaken (LP.strong_parser_kind 0 20 None) (LP.serialize_flbytes (U32.v short_dcid_len))
  | (| Long, (| (), (| ZeroRTT, () |) |) |) ->
    serialize_long_zero_rtt_body
  | (| Long, (| (), (| Handshake, () |) |) |) ->
    serialize_long_handshake_body
  | (| Long, (| (), (| Initial, () |) |) |) ->
    serialize_long_initial_body
  | (| Long, (| (), (| Retry, () |) |) |) ->
    serialize_long_retry_body

let serialize_header
  (short_dcid_len: short_dcid_len_t)
: Tot (LP.serializer (parse_header short_dcid_len))
= LPB.serialize_bitsum
    #LP.parse_u8_kind
    #8
    #U8.t
    first_byte
    #(header' short_dcid_len)
    (first_byte_of_header short_dcid_len)
    (header_body_type short_dcid_len)
    (header_synth short_dcid_len)
    #LP.parse_u8
    LP.serialize_u8
    #(parse_header_body short_dcid_len)
    (serialize_header_body short_dcid_len)
