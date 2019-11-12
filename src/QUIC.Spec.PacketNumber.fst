module QUIC.Spec.PacketNumber
open QUIC.Spec.Base
open QUIC.Spec.PacketNumber.Lemmas
open LowParse.Spec.Combinators
open LowParse.Spec.BoundedInt

(* From https://tools.ietf.org/html/draft-ietf-quic-transport-22#appendix-A *)

module Cast = FStar.Int.Cast
module U64 = FStar.UInt64
module U32 = FStar.UInt32
module U16 = FStar.UInt16
module U8 = FStar.UInt8

inline_for_extraction
let bound_npn
  (pn_len: packet_number_length_t)
: Tot (x: U64.t { U64.v x == bound_npn' (U32.v pn_len - 1) })
= if pn_len = 1ul
  then 256uL
  else if pn_len = 2ul
  then 65536uL
  else if pn_len = 3ul
  then 16777216uL
  else 4294967296uL

let reduce_pn' pn_len pn = pn % (bound_npn' pn_len)

inline_for_extraction
let reduce_pn
  (pn_len: packet_number_length_t)
  (pn: uint62_t)
: Tot (b: bounded_integer (U32.v pn_len) { U32.v b == reduce_pn' (U32.v pn_len - 1) (U64.v pn) })
= [@inline_let]
  let _ =
    assert_norm (pow2 32 == 4294967296)
  in
  if pn_len = 4ul
  then Cast.uint64_to_uint32 pn
  else Cast.uint64_to_uint32 (pn `U64.rem` bound_npn pn_len)

let in_window_self (pn_len: nat { pn_len < 4 }) (pn:nat) : Lemma
  (in_window pn_len pn (if pn = 0 then 0 else pn - 1))
= ()

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

val lemma_parse_pn_correct : (pn_len: nat { pn_len < 4 }) -> last:nat{last+1 < pow2 62} -> (pn: nat { pn < U64.v uint62_bound }) -> Lemma
  (requires in_window pn_len last pn)
  (ensures expand_pn' pn_len last (reduce_pn' pn_len pn) = pn)

let lemma_parse_pn_correct pn_len last pn =
  lemma_uniqueness_in_window pn_len last pn (expand_pn' pn_len last (reduce_pn' pn_len pn))

#push-options "--max_fuel 2 --initial_fuel 2 --max_ifuel 1 --initial_ifuel 1 --z3rlimit 64"

let expand_pn
  (pn_len: packet_number_length_t)
  (last: last_packet_number_t)
  (npn: bounded_integer (U32.v pn_len))
: Tot (pn: uint62_t { U64.v pn == expand_pn' (U32.v pn_len - 1) (U64.v last) (U32.v npn) })
= let open FStar.Mul in
  let open FStar.Math.Lemmas in
  let expected : uint62_t = last `U64.add` 1uL in
  let bound = bound_npn pn_len in
  let candidate = replace_modulo expected bound (Cast.uint32_to_uint64 npn) in
  if (bound `U64.div` 2uL) `U64.lte` expected
     && candidate `U64.lte` (expected `U64.sub` (bound `U64.div` 2uL))
     && candidate `U64.lt` (uint62_bound `U64.sub` bound) then // the test for overflow (candidate < pow2 62 - bound) is not present in draft 22.
//    let _ = lemma_mod_plus candidate 1 bound in
    candidate `U64.add` bound
  else if candidate `U64.gt` (expected `U64.add` (bound `U64.div` 2uL))
          && candidate `U64.gte` bound then // in draft 22 the test for underflow (candidate >= bound) uses a strict inequality, which makes it impossible to expand npn to 0
//    let _ = lemma_mod_plus candidate (-1) bound in
    candidate `U64.sub` bound
  else candidate
#pop-options

inline_for_extraction
let synth_packet_number
  (last: last_packet_number_t)
  (pn_len: packet_number_length_t)
  (npn: bounded_integer (U32.v pn_len))
: Tot (pn: packet_number_t last pn_len { U64.v pn == expand_pn' (U32.v pn_len - 1) (U64.v last) (U32.v npn) })
= expand_pn pn_len last npn

let parse_packet_number
  (last: last_packet_number_t)
  (pn_len: packet_number_length_t)
: Tot (parser (parse_bounded_integer_kind (U32.v pn_len)) (packet_number_t last pn_len) )
= parse_bounded_integer (U32.v pn_len) `parse_synth` synth_packet_number last pn_len

inline_for_extraction
let synth_packet_number_recip
  (last: last_packet_number_t)
  (pn_len: packet_number_length_t)
  (pn: packet_number_t last pn_len)
: Tot  (bounded_integer (U32.v pn_len))
= reduce_pn pn_len pn

let synth_packet_number_recip_inverse
  (last: last_packet_number_t)
  (pn_len: packet_number_length_t)
: Lemma
  (synth_inverse (synth_packet_number last pn_len) (synth_packet_number_recip last pn_len))
//  [SMTPat (synth_inverse (synth_packet_number last pn_len) (synth_packet_number_recip last pn_len))] // TODO: WHY WHY WHY does this pattern not trigger?
= synth_inverse_intro' #(bounded_integer (U32.v pn_len)) #(packet_number_t last pn_len) (synth_packet_number last pn_len) (synth_packet_number_recip last pn_len) (fun pn ->
    lemma_parse_pn_correct (U32.v pn_len - 1) (U64.v last) (U64.v pn)
  )

let serialize_packet_number
  (last: last_packet_number_t)
  (pn_len: packet_number_length_t)
: Tot (serializer (parse_packet_number last pn_len))
= synth_packet_number_recip_inverse last pn_len;
  serialize_synth
    _
    (synth_packet_number last pn_len)
    (serialize_bounded_integer (U32.v pn_len))
    (synth_packet_number_recip last pn_len)
    ()

#push-options "--z3rlimit 16"

let serialize_packet_number_ext
  (last1 last2: last_packet_number_t)
  (pn_len: packet_number_length_t)
  (pn: uint62_t)
: Lemma
  (requires (
    in_window (U32.v pn_len - 1) (U64.v last1) (U64.v pn) /\
    in_window (U32.v pn_len - 1) (U64.v last2) (U64.v pn)
  ))
  (ensures (
    in_window (U32.v pn_len - 1) (U64.v last1) (U64.v pn) /\
    in_window (U32.v pn_len - 1) (U64.v last2) (U64.v pn) /\
    serialize (serialize_packet_number last1 pn_len) pn == serialize (serialize_packet_number last2 pn_len) pn
  ))
= synth_packet_number_recip_inverse last1 pn_len;
  synth_packet_number_recip_inverse last2 pn_len;
  serialize_synth_eq 
    _
    (synth_packet_number last1 pn_len)
    (serialize_bounded_integer (U32.v pn_len))
    (synth_packet_number_recip last1 pn_len)
    ()
    pn;
  serialize_synth_eq 
    _
    (synth_packet_number last2 pn_len)
    (serialize_bounded_integer (U32.v pn_len))
    (synth_packet_number_recip last2 pn_len)
    ()
    pn
