module QUIC.Spec.PacketNumber
open QUIC.Spec.PacketNumber.Lemmas
open LowParse.Spec.Combinators
open LowParse.Spec.BoundedInt

(* From https://tools.ietf.org/html/draft-ietf-quic-transport-22#appendix-A *)

module Cast = FStar.Int.Cast
module U64 = FStar.UInt64
module U32 = FStar.UInt32
module U16 = FStar.UInt16
module U8 = FStar.UInt8

module Secret = QUIC.Secret

let secrets_are_equal_2
  (x: Secret.uint64 { Secret.v x < pow2 2 })
  (y: Secret.uint64 { Secret.v y < pow2 2 })
: Tot (z: Secret.uint64 {
    Secret.v z == (if Secret.v x = Secret.v y then 1 else 0)
  })
= Secret.norm (Secret.secrets_are_equal 2 x y)

#push-options "--z3rlimit 16"

let bound_npn
  (pn_len: packet_number_length_t)
: Tot (x: packet_number_t { Secret.v x == bound_npn' (Secret.v pn_len - 1) })
= let pn_len_1 = Secret.to_u64 (pn_len `Secret.sub` Secret.to_u32 1ul) in
  ((pn_len_1 `secrets_are_equal_2` Secret.to_u64 0ul) `Secret.mul` Secret.to_u64 256uL) `Secret.add`
  ((pn_len_1 `secrets_are_equal_2` Secret.to_u64 1ul) `Secret.mul` Secret.to_u64 65536uL) `Secret.add`
  ((pn_len_1 `secrets_are_equal_2` Secret.to_u64 2ul) `Secret.mul` Secret.to_u64 16777216uL) `Secret.add`
  ((pn_len_1 `secrets_are_equal_2` Secret.to_u64 3ul) `Secret.mul` Secret.to_u64 4294967296uL)

#pop-options

let reduce_pn'
  (pn_len: nat { pn_len < 4 })
  (pn: nat)
: GTot nat
= pn % (bound_npn' pn_len)

module U = FStar.UInt

#push-options "--z3rlimit 32"

let reduce_pn
  (pn_len: packet_number_length_t)
  (pn: packet_number_t)
: GTot (b: bounded_integer (Secret.v pn_len) { U32.v b == reduce_pn' (Secret.v pn_len - 1) (Secret.v pn) })
= let mask = bound_npn pn_len `Secret.sub` Secret.to_u64 1uL in
  Secret.logand_spec pn mask;
  logand_mask #64 (Secret.v pn) (8 `Prims.op_Multiply` Secret.v pn_len);
  (Cast.uint64_to_uint32 (U64.uint_to_t (Secret.v (pn `Secret.logand` mask))) <: U32.t)

#pop-options

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

val lemma_parse_pn_correct : (pn_len: nat { pn_len < 4 }) -> last:nat{last+1 < pow2 62} -> (pn: nat { pn < U64.v U62.bound }) -> Lemma
  (requires in_window pn_len last pn)
  (ensures expand_pn' pn_len last (reduce_pn' pn_len pn) = pn)

let lemma_parse_pn_correct pn_len last pn =
  lemma_uniqueness_in_window pn_len last pn (expand_pn' pn_len last (reduce_pn' pn_len pn))

let secret_is_le_64
  (x: Secret.uint64)
  (y: Secret.uint64)
: Tot (z: Secret.uint64 { Secret.v z == (if Secret.v x <= Secret.v y then 1 else 0) })
= Secret.norm (Secret.secret_is_le 64 x y)

let secret_is_lt_64
  (x: Secret.uint64)
  (y: Secret.uint64)
: Tot (z: Secret.uint64 { Secret.v z == (if Secret.v x < Secret.v y then 1 else 0) })
= Secret.norm (Secret.secret_is_lt 64 x y)

#push-options "--max_fuel 2 --initial_fuel 2 --max_ifuel 1 --initial_ifuel 1 --z3rlimit 512 --query_stats"

inline_for_extraction
let expand_pn_aux
  (pn_len: packet_number_length_t)
  (last: last_packet_number_t)
  (npn: bounded_integer (Secret.v pn_len))
: Tot (pn: Secret.uint64 { Secret.v pn == expand_pn' (Secret.v pn_len - 1) (Secret.v last) (U32.v npn) })
= let open FStar.Mul in
  let open FStar.Math.Lemmas in
  let expected : U62.secret = last `Secret.add` Secret.to_u64 1uL in
  let bound = bound_npn pn_len in
  let bound_2 = bound `Secret.shift_right` 1ul in
  FStar.UInt.shift_right_value_lemma #64 (Secret.v bound) 1;
  assert (Secret.v bound_2 == Secret.v bound / 2);
  let candidate = replace_modulo expected (8 `Prims.op_Multiply` Secret.v pn_len) (bound `Secret.sub` Secret.to_u64 1uL) (Secret.to_u64 (Cast.uint32_to_uint64 npn)) in
  let bound_2_le_expected = bound_2 `secret_is_le_64` expected in
  let cond_1 =
    bound_2_le_expected `Secret.logand_one_bit`
    (candidate `secret_is_le_64` ((bound_2_le_expected `Secret.mul` expected) `Secret.sub` (bound_2_le_expected `Secret.mul` bound_2))) `Secret.logand_one_bit`
    (candidate `secret_is_lt_64` (Secret.to_u64 U62.bound `Secret.sub` bound))
  in
  assert (Secret.v cond_1 == (
    if
      Secret.v bound_2 <= Secret.v expected &&
      Secret.v candidate <= (Secret.v expected - Secret.v bound_2) &&
      Secret.v candidate < U62.v U62.bound - Secret.v bound
    then 1
    else 0
  ));
  let cond_2 =
    Secret.lognot_one_bit cond_1 `Secret.logand_one_bit`
    ((expected `Secret.add` bound_2) `secret_is_lt_64` candidate) `Secret.logand_one_bit`
    (bound `secret_is_le_64` candidate)
  in
  assert (Secret.v cond_2 == (
    if
      Secret.v cond_1 = 0 &&
      Secret.v expected + Secret.v bound_2 < Secret.v candidate &&
      Secret.v bound <= Secret.v candidate
    then 1
    else 0
  ));
  (candidate `Secret.add` (cond_1 `Secret.mul` bound)) `Secret.sub` (cond_2 `Secret.mul` bound)

inline_for_extraction
let expand_pn
  (pn_len: packet_number_length_t)
  (last: last_packet_number_t)
  (npn: bounded_integer (Secret.v pn_len))
: Tot (pn: packet_number_t { Secret.v pn == expand_pn' (Secret.v pn_len - 1) (Secret.v last) (U32.v npn) })
= expand_pn_aux pn_len last npn

#pop-options

inline_for_extraction
let synth_packet_number
  (last: last_packet_number_t)
  (pn_len: packet_number_length_t)
  (npn: bounded_integer (Secret.v pn_len))
: Tot (pn: packet_number_t' last pn_len { Secret.v pn == expand_pn' (Secret.v pn_len - 1) (Secret.v last) (U32.v npn) })
= expand_pn pn_len last npn

let parse_packet_number
  (last: last_packet_number_t)
  (pn_len: packet_number_length_t)
: Tot (parser (parse_bounded_integer_kind (Secret.v pn_len)) (packet_number_t' last pn_len) )
= parse_bounded_integer (Secret.v pn_len) `parse_synth` synth_packet_number last pn_len

let synth_packet_number_recip
  (last: last_packet_number_t)
  (pn_len: packet_number_length_t)
  (pn: packet_number_t' last pn_len)
: GTot  (bounded_integer (Secret.v pn_len))
= reduce_pn pn_len pn

let synth_packet_number_recip_inverse
  (last: last_packet_number_t)
  (pn_len: packet_number_length_t)
: Lemma
  (synth_inverse (synth_packet_number last pn_len) (synth_packet_number_recip last pn_len))
//  [SMTPat (synth_inverse (synth_packet_number last pn_len) (synth_packet_number_recip last pn_len))] // TODO: WHY WHY WHY does this pattern not trigger?
= synth_inverse_intro' #(bounded_integer (Secret.v pn_len)) #(packet_number_t' last pn_len) (synth_packet_number last pn_len) (synth_packet_number_recip last pn_len) (fun pn ->
    lemma_parse_pn_correct (Secret.v pn_len - 1) (Secret.v last) (Secret.v pn)
  )

let serialize_packet_number
  (last: last_packet_number_t)
  (pn_len: packet_number_length_t)
: Tot (serializer (parse_packet_number last pn_len))
= synth_packet_number_recip_inverse last pn_len;
  serialize_synth
    _
    (synth_packet_number last pn_len)
    (serialize_bounded_integer (Secret.v pn_len))
    (synth_packet_number_recip last pn_len)
    ()

#push-options "--z3rlimit 16"

let serialize_packet_number_ext
  last1 last2 pn_len pn
= synth_packet_number_recip_inverse last1 pn_len;
  synth_packet_number_recip_inverse last2 pn_len;
  serialize_synth_eq 
    _
    (synth_packet_number last1 pn_len)
    (serialize_bounded_integer (Secret.v pn_len))
    (synth_packet_number_recip last1 pn_len)
    ()
    pn;
  serialize_synth_eq 
    _
    (synth_packet_number last2 pn_len)
    (serialize_bounded_integer (Secret.v pn_len))
    (synth_packet_number_recip last2 pn_len)
    ()
    pn

#pop-options
