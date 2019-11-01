module QUIC.Parse
open QUIC.Spec.Base

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

(*
// How to test normalization:
module T = FStar.Tactics
let f (x: FStar.UInt8.t) : Tot unit =
  assert (filter_header_byte x == true) by (
    T.norm [primops; iota; zeta; delta_attr [`%filter_bitsum'_t_attr]];
    T.fail "abc"
  )
*)

(* BEGIN packet number *)

(* From https://tools.ietf.org/html/draft-ietf-quic-transport-22#appendix-A *)

inline_for_extraction
noextract
let integer_size = (x: nat { 1 <= x /\ x <= 4 })

inline_for_extraction
noextract
let bounded_integer_prop
  (sz: integer_size)
  (x: U32.t)
: Tot Type0
= match sz with
  | 1 -> U32.v x < 256
  | 2 -> U32.v x < 65536
  | 3 -> U32.v x < 16777296
  | 4 -> True

inline_for_extraction
noextract
let bounded_integer
  (sz: integer_size)
: Tot eqtype
= (x: U32.t { bounded_integer_prop sz x })

let bound_npn' (pn_len:nat (* { pn_len < 4 } *)) = pow2 (8 `op_Multiply` (pn_len + 1))

inline_for_extraction
let bound_npn
  (pn_len: packet_number_length_t)
: Tot (x: U64.t { U64.v x == bound_npn' (U32.v pn_len - 1) })
= [@inline_let]
  let res =
    if pn_len = 1ul
    then 256uL
    else if pn_len = 2ul
    then 65536uL
    else if pn_len = 3ul
    then 16777216uL
    else 4294967296uL
  in
  [@inline_let]
  let _ =
    assert_norm (pow2 8 == 256);
    assert_norm (pow2 16 == 65536);
    assert_norm (pow2 24 == 16777216);
    assert_norm (pow2 32 == 4294967296)
  in
  res

let reduce_pn' pn_len pn = pn % (bound_npn' pn_len)

inline_for_extraction
let reduce_pn
  (pn_len: packet_number_length_t)
  (pn: uint62)
: Tot (b: bounded_integer (U32.v pn_len) { U32.v b == reduce_pn' (U32.v pn_len - 1) (U64.v pn) })
= [@inline_let]
  let _ =
    assert_norm (pow2 32 == 4294967296)
  in
  if pn_len = 4ul
  then Cast.uint64_to_uint32 pn
  else Cast.uint64_to_uint32 (pn `U64.rem` bound_npn pn_len)

let replace_modulo' (a b new_mod:nat) : Pure nat
  (requires b > 0 /\ new_mod < b)
  (ensures fun res -> res % b = new_mod /\ res / b = a / b) =
  let open FStar.Math.Lemmas in
  let res = a - a%b + new_mod in
  lemma_mod_plus new_mod (a/b) b;
  small_mod new_mod b;
  res

let in_window (pn_len: nat) (last pn:nat) =
  let h = bound_npn' pn_len in
  (last+1 < h/2 /\ pn < h) \/
  (last+1 >= pow2 62 - h/2 /\ pn >= pow2 62 - h) \/
  (last+1 - h/2 < pn /\ pn <= last+1 + h/2)

#push-options "--z3rlimit 20"
let lemma_replace_modulo_bound_aux (k:nat) (a:nat) (b:nat) (u:nat)
  : Lemma (requires a < pow2 k /\ a % pow2 u == 0 /\ b < pow2 u /\ u < k)
  (ensures a + b < pow2 k) =
  let open FStar.Math.Lemmas in
  let open FStar.Mul in
  lemma_div_mod a (pow2 u);
  assert(a + b == pow2 u * (a / pow2 u) + b);
  lemma_div_plus b (a / pow2 u) (pow2 u);
  small_div b (pow2 u);
  lemma_div_lt_nat a k u;
  assert((a / pow2 u) < pow2 (k-u));
  assert(((a + b) / pow2 u) / pow2 (k-u) < 1);
  division_multiplication_lemma (a+b) (pow2 u) (pow2 (k-u));
  pow2_plus u (k-u)

let lemma_replace_modulo_bound (a mod_pow new_mod up_pow:nat) : Lemma
  (requires
    mod_pow < up_pow /\
    new_mod < pow2 mod_pow /\
    a < pow2 up_pow)
  (ensures replace_modulo' a (pow2 mod_pow) new_mod < pow2 up_pow) =
  let open FStar.Math.Lemmas in
  let open FStar.Mul in
  let (pmod,umod) = (pow2 mod_pow, pow2 up_pow) in
  lemma_div_mod a pmod;
  multiple_modulo_lemma (a / pmod) pmod;
  lemma_replace_modulo_bound_aux up_pow (a-a%pow2 mod_pow) new_mod mod_pow
#pop-options

#push-options "--max_fuel 2 --initial_fuel 2 --max_ifuel 1 --initial_ifuel 1"
let expand_pn'
  (pn_len: nat { pn_len < 4 })
  (last: nat { last + 1 < pow2 62})
  (npn: nat { npn < bound_npn' pn_len })
: Tot (pn: nat { pn < pow2 62 /\ in_window pn_len last pn /\ pn % bound_npn' pn_len == npn })
=
  let open FStar.Mul in
  let open FStar.Math.Lemmas in
  let expected = last + 1 in
  let bound = bound_npn' pn_len in
  let candidate = replace_modulo' expected bound npn in
  lemma_replace_modulo_bound expected (8*(pn_len+1)) npn 62;
  if candidate <= last + 1 - bound/2
     && candidate < pow2 62 - bound then // the test for overflow (candidate < pow2 62 - bound) is not present in draft 22.
    let _ = lemma_mod_plus candidate 1 bound in
    candidate + bound
  else if candidate > last + 1 + bound/2
          && candidate >= bound then // in draft 22 the test for underflow (candidate >= bound) uses a strict inequality, which makes it impossible to expand npn to 0
    let _ = lemma_mod_plus candidate (-1) bound in
    candidate - bound
  else candidate
#pop-options

let max (a b:int) : Tot (n:int{n >= a /\ n >= b}) =
  if a > b then a else b // this must exist somewhere...

let lemma_uniqueness_in_window (pn_len: nat { pn_len < 4 }) (last: nat { last < pow2 62 }) (x: nat {x < pow2 62}) (y:nat {y < pow2 62}) : Lemma
  (requires (
    let h = bound_npn' pn_len in
    in_window pn_len last x /\
    in_window pn_len last y /\
    x%h = y%h))
  (ensures x = y) =
  let open FStar.Math.Lemmas in
  pow2_lt_compat 62 (8 `op_Multiply` (pn_len+1));
  let h = bound_npn' pn_len in
  if last+1 < h/2 && x < h then
    lemma_mod_plus_injective h 0 x y
  else if last+1 >= pow2 62 - h/2 && x >= pow2 62 - h then
    let low = pow2 62 - h in
    lemma_mod_plus_injective h low (x-low) (y-low)
  else
    let low = max (last+2-h/2) 0 in
    lemma_mod_plus_injective h low (x-low) (y-low)

val lemma_parse_pn_correct : (pn_len: nat { pn_len < 4 }) -> last:nat{last+1 < pow2 62} -> (pn: nat { pn < pow2 62 }) -> Lemma
  (requires in_window pn_len last pn)
  (ensures expand_pn' pn_len last (reduce_pn' pn_len pn) = pn)

let lemma_parse_pn_correct pn_len last pn =
  lemma_uniqueness_in_window pn_len last pn (expand_pn' pn_len last (reduce_pn' pn_len pn))


#push-options "--max_fuel 2 --initial_fuel 2 --max_ifuel 1 --initial_ifuel 1"
let expand_pn pn_len last npn =
  let open FStar.Mul in
  let open FStar.Math.Lemmas in
  let expected = last + 1 in
  let bound = bound_npn pn_len in
  let candidate = replace_modulo expected bound npn in
  lemma_replace_modulo_bound expected (8*(pn_len+1)) npn 62;
  if candidate <= last + 1 - bound/2
     && candidate < pow2 62 - bound then // the test for overflow (candidate < pow2 62 - bound) is not present in draft 22.
    let _ = lemma_mod_plus candidate 1 bound in
    candidate + bound
  else if candidate > last + 1 + bound/2
          && candidate >= bound then // in draft 22 the test for underflow (candidate >= bound) uses a strict inequality, which makes it impossible to expand npn to 0
    let _ = lemma_mod_plus candidate (-1) bound in
    candidate - bound
  else candidate
#pop-options

(* END packet number *)

inline_for_extraction
let short_dcid_len_t = (short_dcid_len: U32.t { U32.v short_dcid_len <= 20 })

let header_short_dcid_length_prop
  (m: header)
  (short_dcid_len: short_dcid_len_t)
: GTot bool
= if MShort? m
  then FB.length (MShort?.dcid m) = U32.v short_dcid_len
  else true

inline_for_extraction
type header' (short_dcid_len: short_dcid_len_t) = (m: header { header_short_dcid_length_prop m short_dcid_len })


open LowParse.Spec.Bytes

module FB = FStar.Bytes

#push-options "--z3rlimit 16"

inline_for_extraction
noextract
let first_byte_of_header
  (short_dcid_len: short_dcid_len_t)
  (t: Type0)
  (f: (bitsum'_type first_byte -> Tot t))
  (m: header' short_dcid_len)
: Tot t
= match m with
  | MShort spin key_phase dcid packet_number ->
    let spin : bitfield uint8 1 = if spin then 1uy else 0uy in
    let key_phase : bitfield uint8 1 = if key_phase then 1uy else 0uy in
    let pn_length : packet_number_length_t = FB.len packet_number in
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
  (pn_length: packet_number_length_t)
: Tot Type0
= (varint_t & bounded_integer (U32.v pn_length))

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
      MLong version dcid scid (MInitial token payload_length pn_length packet_number)
    end
  | (| Long, (| (), (| ZeroRTT, (| (), (| pn_length, () |) |) |) |) |) ->
    begin match coerce (common_long_t & payload_length_pn pn_length) pl with
    | ((version, (dcid, scid)), (payload_length, packet_number)) ->
      MLong version dcid scid (MZeroRTT payload_length pn_length packet_number)
    end
  | (| Long, (| (), (| Handshake, (| (), (| pn_length, () |) |) |) |) |) ->
    begin match coerce (common_long_t & payload_length_pn pn_length) pl with
    | ((version, (dcid, scid)), (payload_length, packet_number)) ->
      MLong version dcid scid (MHandshake payload_length pn_length packet_number)
    end
  | (| Long, (| (), (| Retry, (unused, ()) |) |) |) ->
    begin match coerce (common_long_t & parse_bounded_vlbytes_t 0 20) pl with
    | ((version, (dcid, scid)), odcid) ->
      MLong version dcid scid (MRetry unused odcid)
    end

#pop-options

#push-options "--z3rlimit 64 --max_fuel 8 --max_ifuel 8 --initial_fuel 8 --initial_ifuel 8"

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
    | MLong version dcid scid (MInitial token payload_length _ packet_number) ->
      coerce (header_body_type short_dcid_len (bitsum'_key_of_t first_byte k')) (((version, (dcid, scid)), (token, (payload_length, packet_number))) <: (common_long_t & (parse_bounded_vlbytes_t 0 token_max_len & payload_length_pn pn_length)))
    end
  | (| Long, (| (), (| ZeroRTT, (| (), (| pn_length, () |) |) |) |) |) ->
    begin match pl with
    | MLong version dcid scid (MZeroRTT payload_length _ packet_number) ->
      coerce (header_body_type short_dcid_len (bitsum'_key_of_t first_byte k')) (((version, (dcid, scid)), (payload_length, packet_number)) <: (common_long_t & payload_length_pn pn_length))
    end
  | (| Long, (| (), (| Handshake, (| (), (| pn_length, () |) |) |) |) |) ->
    begin match pl with
    | MLong version dcid scid (MHandshake payload_length _ packet_number) ->
      coerce (header_body_type short_dcid_len (bitsum'_key_of_t first_byte k')) (((version, (dcid, scid)), (payload_length, packet_number)) <: (common_long_t & payload_length_pn pn_length))
    end
  | (| Long, (| (), (| Retry, (unused, ()) |) |) |) ->
    begin match pl with
    | MLong version dcid scid (MRetry unused odcid) ->
      coerce (header_body_type short_dcid_len (bitsum'_key_of_t first_byte k')) (((version, (dcid, scid)), odcid) <: (common_long_t & parse_bounded_vlbytes_t 0 20))
    end

[@filter_bitsum'_t_attr]
inline_for_extraction
noextract
let header_sum
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
= parse_varint `nondep_then` parse_bounded_integer (U32.v pn_length)

#push-options "--z3rlimit 32 --max_fuel 8 --max_ifuel 8 --initial_fuel 8 --initial_ifuel 8"

[@filter_bitsum'_t_attr]
inline_for_extraction
noextract
let parse_header_body
  (short_dcid_len: short_dcid_len_t)
  (k' : bitsum'_key_type (header_sum short_dcid_len).b)
: Tot (k: parser_kind & parser k (bitsum_type_of_tag (header_sum short_dcid_len) k'))
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
= parse_bitsum_kind parse_u8_kind (header_sum short_dcid_len) (parse_header_body short_dcid_len)

inline_for_extraction
noextract
let parse_header_kind : parser_kind =
  normalize_term (parse_header_kind' 0ul)

let parse_header
  (short_dcid_len: short_dcid_len_t)
: Tot (parser parse_header_kind (header' short_dcid_len))
= assert_norm (parse_header_kind' short_dcid_len == parse_header_kind);
  parse_bitsum
    (header_sum short_dcid_len)
    parse_u8
    (parse_header_body short_dcid_len)

let serialize_common_long : serializer parse_common_long =
  serialize_flbytes 4 `serialize_nondep_then` (serialize_bounded_vlbytes 0 20 `serialize_nondep_then` serialize_bounded_vlbytes 0 20)

let serialize_payload_length_pn
  (pn_length: packet_number_length_t)
: Tot (serializer (parse_payload_length_pn pn_length))
= serialize_varint `serialize_nondep_then` serialize_bounded_integer (U32.v pn_length)

let serialize_header_body
  (short_dcid_len: short_dcid_len_t)
  (k' : bitsum'_key_type (header_sum short_dcid_len).b)
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
    (header_sum short_dcid_len)
    serialize_u8
    #(parse_header_body short_dcid_len)
    (serialize_header_body short_dcid_len)

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
  (pn_length: packet_number_length_t)
: Tot (LC.validator (parse_payload_length_pn pn_length))
= validate_varint `LC.validate_nondep_then` LI.validate_bounded_integer (U32.v pn_length)


[@filter_bitsum'_t_attr]
inline_for_extraction
noextract
let validate_header_body_cases
  (short_dcid_len: short_dcid_len_t)
  (k' : bitsum'_key_type (header_sum short_dcid_len).b)
: Tot (LC.validator (dsnd (parse_header_body short_dcid_len k')))
= match coerce (bitsum'_key_type first_byte) k' with
  | (| Short, (| (), (| (), (| pn_length, () |) |) |) |) ->
    LC.validate_weaken (strong_parser_kind 0 20 None) (LB.validate_flbytes (U32.v short_dcid_len) short_dcid_len) () `LC.validate_nondep_then` LB.validate_flbytes (U32.v pn_length) pn_length
  | (| Long, (| (), (| Initial, (| (), (| pn_length, () |) |) |) |) |) ->
    validate_common_long `LC.validate_nondep_then` (LB.validate_bounded_vlgenbytes 0 0ul token_max_len (U32.uint_to_t token_max_len) (validate_bounded_varint 0ul (U32.uint_to_t token_max_len)) (read_bounded_varint 0 token_max_len) `LC.validate_nondep_then` validate_payload_length_pn pn_length)
  | (| Long, (| (), (| ZeroRTT, (| (), (| pn_length, () |) |) |) |) |) ->
    validate_common_long `LC.validate_nondep_then` validate_payload_length_pn pn_length
  | (| Long, (| (), (| Handshake, (| (), (| pn_length, () |) |) |) |) |) ->
    validate_common_long `LC.validate_nondep_then` validate_payload_length_pn pn_length
  | (| Long, (| (), (| Retry, () |) |) |) ->
    validate_common_long `LC.validate_nondep_then` LB.validate_bounded_vlbytes 0 20

let filter_first_byte'
: (filter_bitsum'_t first_byte)
= norm [primops; iota; zeta; delta_attr [`%filter_bitsum'_t_attr]]
  (mk_filter_bitsum'_t' first_byte)

inline_for_extraction
let filter_first_byte
  (short_dcid_len: short_dcid_len_t)
: Tot (filter_bitsum'_t (header_sum short_dcid_len).b)
= coerce (filter_bitsum'_t (header_sum short_dcid_len).b) filter_first_byte'

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
: LL.validate_bitsum_cases_t (header_sum short_dcid_len).b
= coerce (LL.validate_bitsum_cases_t (header_sum short_dcid_len).b) mk_validate_header_body_cases' 

let validate_header
  (short_dcid_len: short_dcid_len_t)
: Tot (LL.validator (parse_header short_dcid_len))
= assert_norm (parse_header_kind' short_dcid_len == parse_header_kind);
  LL.validate_bitsum
    (header_sum short_dcid_len)
    (LJ.validate_u8 ())
    LJ.read_u8
    (filter_first_byte short_dcid_len)
    (parse_header_body short_dcid_len)
    (validate_header_body_cases short_dcid_len)
    (mk_validate_header_body_cases short_dcid_len)

let test b =
  let sl = LowParse.Slice.make_slice b 42ul in
  validate_header 18ul sl 0ul
