module QUIC.Secret.Int
include Lib.IntTypes

module U8 = FStar.UInt8
module U16 = FStar.UInt16
module U32 = FStar.UInt32
module U64 = FStar.UInt64

unfold
let v #t #l (u: int_t t l) : GTot (range_t t) =
  v u

noextract
noeq
type must_inline =

noextract
unfold
let norm = norm [delta_attr [(`%must_inline)]; iota; zeta; primops]

noextract
let supported_type = function
  | U8 | U16 | U32 | U64 -> true
  | _ -> false

module U = FStar.UInt


(* Patterns *)


let logand_spec'
  (#t:inttype)
  (#l:secrecy_level)
  (a:int_t t l)
  (b:int_t t l)
: Lemma (v (a `logand` b) == v a `logand_v` v b)
  [SMTPat (v (a `logand` b))]
= logand_spec a b

let logor_spec'
  (#t:inttype)
  (#l:secrecy_level)
  (a:int_t t l)
  (b:int_t t l)
: Lemma (v (a `logor` b) == v a `logor_v` v b)
  [SMTPat (v (a `logor` b))]
= logor_spec a b

let logxor_spec'
  (#t:inttype)
  (#l:secrecy_level)
  (a:int_t t l)
  (b:int_t t l)
: Lemma (v (a `logxor` b) == v a `logxor_v` v b)
  [SMTPat (v (a `logxor` b))]
= logxor_spec a b

inline_for_extraction
[@"opaque_to_smt"]
let lognot'
  (#t:inttype { supported_type t })
  (#l:secrecy_level)
  (x: uint_t t l)
: Tot (y: uint_t t l { v y == U.lognot #(bits t) (v x) })
= U.nth_lemma #(bits t) (U.lognot (v x)) (v x `U.logxor` v (ones t l));
  x `logxor` ones t l

(*
let shift_left_spec'
  (#t:inttype { supported_type t } )
  (#l:secrecy_level)
  (a:int_t t l)
  (b:shiftval t)
: Lemma (v (a `shift_left` b) == U.shift_left #(bits t) (v a) (v b))
  [SMTPat (v (a `shift_left` b))]
= ()

let shift_right_spec'
  (#t:inttype { supported_type t } )
  (#l:secrecy_level)
  (a:int_t t l)
  (b:shiftval t)
: Lemma (v (a `shift_right` b) == U.shift_right #(bits t) (v a) (v b))
  [SMTPat (v (a `shift_right` b))]
= ()
*)

(* Logic *)

inline_for_extraction
noextract
[@"opaque_to_smt"]
let logand_one_bit
  (#t: inttype { supported_type t })
  (#sec: secrecy_level)
  (x: int_t t sec { v x == 0 \/ v x == 1 })
  (y: int_t t sec { v y == 0 \/ v y == 1 })
: Tot (z: int_t t sec { v z == (if v x = 1 && v y = 1 then 1 else 0) })
= x `mul` y

let logor_one_bit_8
  (sec: secrecy_level)
  (x: int_t U8 sec { v x == 0 \/ v x == 1 })
  (y: int_t U8 sec { v y == 0 \/ v y == 1 })
: Lemma
  (v (x `logor` y) == (if v x = 1 || v y = 1 then 1 else 0))
= logor_spec x y;
  allow_inversion secrecy_level;
  assert (U8.logor 0uy 0uy == 0uy);
  assert (U8.logor 0uy 1uy == 1uy);
  assert (U8.logor 1uy 0uy == 1uy);
  assert (U8.logor 1uy 1uy == 1uy)

let logor_one_bit_16
  (sec: secrecy_level)
  (x: int_t U16 sec { v x == 0 \/ v x == 1 })
  (y: int_t U16 sec { v y == 0 \/ v y == 1 })
: Lemma
  (v (x `logor` y) == (if v x = 1 || v y = 1 then 1 else 0))
= logor_spec x y;
  allow_inversion secrecy_level;
  assert (U16.logor 0us 0us == 0us);
  assert (U16.logor 0us 1us == 1us);
  assert (U16.logor 1us 0us == 1us);
  assert (U16.logor 1us 1us == 1us)

let logor_one_bit_32
  (sec: secrecy_level)
  (x: int_t U32 sec { v x == 0 \/ v x == 1 })
  (y: int_t U32 sec { v y == 0 \/ v y == 1 })
: Lemma
  (v (x `logor` y) == (if v x = 1 || v y = 1 then 1 else 0))
= logor_spec x y;
  allow_inversion secrecy_level;
  assert (U32.logor 0ul 0ul == 0ul);
  assert (U32.logor 0ul 1ul == 1ul);
  assert (U32.logor 1ul 0ul == 1ul);
  assert (U32.logor 1ul 1ul == 1ul)

let logor_one_bit_64
  (sec: secrecy_level)
  (x: int_t U64 sec { v x == 0 \/ v x == 1 })
  (y: int_t U64 sec { v y == 0 \/ v y == 1 })
: Lemma
  (v (x `logor` y) == (if v x = 1 || v y = 1 then 1 else 0))
= logor_spec x y;
  allow_inversion secrecy_level;
  assert (U64.logor 0uL 0uL == 0uL);
  assert (U64.logor 0uL 1uL == 1uL);
  assert (U64.logor 1uL 0uL == 1uL);
  assert (U64.logor 1uL 1uL == 1uL)

let logor_one_bit'
  (#t: inttype { supported_type t })
  (#sec: secrecy_level)
  (x: int_t t sec { v x == 0 \/ v x == 1 })
  (y: int_t t sec { v y == 0 \/ v y == 1 })
: Lemma
  (v (x `logor` y) == (if v x = 1 || v y = 1 then 1 else 0))
= match t with
  | U8 -> logor_one_bit_8 sec x y
  | U16 -> logor_one_bit_16 sec x y
  | U32 -> logor_one_bit_32 sec x y
  | U64 -> logor_one_bit_64 sec x y

inline_for_extraction
[@"opaque_to_smt"]
noextract
let logor_one_bit
  (#t: inttype { supported_type t })
  (#sec: secrecy_level)
  (x: int_t t sec { v x == 0 \/ v x == 1 })
  (y: int_t t sec { v y == 0 \/ v y == 1 })
: Tot (z: int_t t sec { v z == (if v x = 1 || v y = 1 then 1 else 0) })
= logor_one_bit' x y;
  x `logor` y

let logxor_one_bit_8
  (sec: secrecy_level)
  (x: int_t U8 sec { v x == 0 \/ v x == 1 })
  (y: int_t U8 sec { v y == 0 \/ v y == 1 })
: Lemma
  (v (x `logxor` y) == (if v x = v y then 0 else 1))
= logxor_spec x y;
  allow_inversion secrecy_level;
  assert (U8.logxor 0uy 0uy == 0uy);
  assert (U8.logxor 0uy 1uy == 1uy);
  assert (U8.logxor 1uy 0uy == 1uy);
  assert (U8.logxor 1uy 1uy == 0uy)

let logxor_one_bit_16
  (sec: secrecy_level)
  (x: int_t U16 sec { v x == 0 \/ v x == 1 })
  (y: int_t U16 sec { v y == 0 \/ v y == 1 })
: Lemma
  (v (x `logxor` y) == (if v x = v y then 0 else 1))
= logxor_spec x y;
  allow_inversion secrecy_level;
  assert (U16.logxor 0us 0us == 0us);
  assert (U16.logxor 0us 1us == 1us);
  assert (U16.logxor 1us 0us == 1us);
  assert (U16.logxor 1us 1us == 0us)

let logxor_one_bit_32
  (sec: secrecy_level)
  (x: int_t U32 sec { v x == 0 \/ v x == 1 })
  (y: int_t U32 sec { v y == 0 \/ v y == 1 })
: Lemma
  (v (x `logxor` y) == (if v x = v y then 0 else 1))
= logxor_spec x y;
  allow_inversion secrecy_level;
  assert (U32.logxor 0ul 0ul == 0ul);
  assert (U32.logxor 0ul 1ul == 1ul);
  assert (U32.logxor 1ul 0ul == 1ul);
  assert (U32.logxor 1ul 1ul == 0ul)

let logxor_one_bit_64
  (sec: secrecy_level)
  (x: int_t U64 sec { v x == 0 \/ v x == 1 })
  (y: int_t U64 sec { v y == 0 \/ v y == 1 })
: Lemma
  (v (x `logxor` y) == (if v x = v y then 0 else 1))
= logxor_spec x y;
  allow_inversion secrecy_level;
  assert (U64.logxor 0uL 0uL == 0uL);
  assert (U64.logxor 0uL 1uL == 1uL);
  assert (U64.logxor 1uL 0uL == 1uL);
  assert (U64.logxor 1uL 1uL == 0uL)

let logxor_one_bit'
  (#t: inttype { supported_type t })
  (#sec: secrecy_level)
  (x: int_t t sec { v x == 0 \/ v x == 1 })
  (y: int_t t sec { v y == 0 \/ v y == 1 })
: Lemma
  (v (x `logxor` y) == (if v x = v y then 0 else 1))
= match t with
  | U8 -> logxor_one_bit_8 sec x y
  | U16 -> logxor_one_bit_16 sec x y
  | U32 -> logxor_one_bit_32 sec x y
  | U64 -> logxor_one_bit_64 sec x y

inline_for_extraction
noextract
[@"opaque_to_smt"]
let logxor_one_bit
  (#t: inttype { supported_type t })
  (#sec: secrecy_level)
  (x: int_t t sec { v x == 0 \/ v x == 1 })
  (y: int_t t sec { v y == 0 \/ v y == 1 })
: Tot (z: int_t t sec { v z == (if v x = v y then 0 else 1) })
= logxor_one_bit' x y;
  x `logxor` y

inline_for_extraction
noextract
[@"opaque_to_smt"]
let secret_bool
  (#t: inttype { supported_type t })
  (#sec: secrecy_level)
  (x: bool)
: Tot (z: int_t t sec { v z == (if x then 1 else 0) })
= cast t sec (if x then 1uy else 0uy)

inline_for_extraction
noextract
[@"opaque_to_smt"]
let lognot_one_bit
  (#t: inttype { supported_type t })
  (#sec: secrecy_level)
  (x: int_t t sec { v x == 0 \/ v x == 1 })
: Tot (z: int_t t sec { v z == (if v x = 1 then 0 else 1) })
= x `logxor_one_bit` secret_bool true

(* Decomposition *)

#push-options "--z3rlimit 16"

inline_for_extraction
noextract
[@"opaque_to_smt"]
let rem2
  (#t: inttype { supported_type t })
  (#sec: secrecy_level)
  (x: int_t t sec)
: Tot (z: int_t t sec { v z == v x % 2 })
= 
  logand_spec x (cast t sec 1uy);
  assert_norm (pow2 1 == 2);
  U.logand_mask #(bits t) (v x) 1;
  x `logand` cast t sec 1uy

inline_for_extraction
noextract
[@"opaque_to_smt"]
let div2
  (#t: inttype { supported_type t })
  (#sec: secrecy_level)
  (x: int_t t sec)
: Tot (z: int_t t sec { v z == v x / 2 })
= x `shift_right` 1ul

(* Comparisons *)

[@must_inline "opaque_to_smt"]
noextract
let rec secret_is_nonzero
  (#t: inttype { supported_type t })
  (#sec: secrecy_level)
  (size: nat)
  (x: int_t t sec { v x < pow2 size })
: Tot (y: int_t t sec {
    v y == (if v x = 0 then 0 else 1)
  })
  (decreases size)
= if size = 0
  then secret_bool false
  else
    let test_mod = rem2 x in
    let re = secret_is_nonzero (size - 1) (div2 x) in
    test_mod `logor_one_bit` re

noextract
[@must_inline "opaque_to_smt"]
let rec secrets_are_different
  (#t: inttype { supported_type t })
  (#sec: secrecy_level)
  (size: nat)
  (x: int_t t sec { v x < pow2 size })
  (y: int_t t sec { v y < pow2 size })
: Tot (z: int_t t sec {
    v z == (if v x <> v y then 1 else 0)
  })
  (decreases size)
= 
  if size = 0
  then secret_bool false
  else
    let xm = rem2 x in
    let ym = rem2 y in
    let test_mod = xm `logxor_one_bit` ym in
    let re = secrets_are_different (size - 1) (div2 x) (div2 y) in
    test_mod `logor_one_bit` re

noextract
[@must_inline "opaque_to_smt"]
let secrets_are_equal
  (#t: inttype { supported_type t })
  (#sec: secrecy_level)
  (size: nat)
  (x: int_t t sec { v x < pow2 size })
  (y: int_t t sec { v y < pow2 size })
: Tot (z: int_t t sec {
    v z == (if v x = v y then 1 else 0)
  })
= lognot_one_bit (secrets_are_different size x y)

inline_for_extraction
noextract
[@"opaque_to_smt"]
let one_bit_lt
  (#t: inttype { supported_type t })
  (#sec: secrecy_level)
  (x: int_t t sec { v x == 0 \/ v x == 1 })
  (y: int_t t sec { v y == 0 \/ v y == 1 })
: Tot (z: int_t t sec { v z == (if v x < v y then 1 else 0) })
= lognot_one_bit x `logand_one_bit` y

inline_for_extraction
noextract
[@"opaque_to_smt"]
let one_bit_eq
  (#t: inttype { supported_type t })
  (#sec: secrecy_level)
  (x: int_t t sec { v x == 0 \/ v x == 1 })
  (y: int_t t sec { v y == 0 \/ v y == 1 })
: Tot (z: int_t t sec { v z == (if v x = v y then 1 else 0) })
= lognot_one_bit (x `logxor_one_bit` y)

(* This works, but is very slow.
noextract
[@must_inline]
let rec secret_is_lt
  (#t: inttype { supported_type t })
  (#sec: secrecy_level)
  (size: nat)
  (x: int_t t sec { v x < pow2 size })
  (y: int_t t sec { v y < pow2 size })
: Tot (z: int_t t sec { v z == (if v x < v y then 1 else 0) })
  (decreases size)
= if size = 0
  then secret_bool false
  else
    secret_is_lt (size - 1) (div2 x) (div2 y) `logor_one_bit`
    (secrets_are_equal (size - 1) (div2 x) (div2 y) `logand_one_bit` one_bit_lt (rem2 x) (rem2 y)) 
*)

#push-options "--z3rlimit 64"

#restart-solver

inline_for_extraction
noextract
[@"opaque_to_smt"]
let highest_bit
  (#t: inttype { supported_type t })
  (#sec: secrecy_level)
  (size: nat { size > 0 /\ size <= bits t })
  (x: int_t t sec { v x < pow2 (size) })
: Tot (z: int_t t sec { v z == v x / pow2 (size - 1) /\ (v z == 0 \/ v z == 1) })
= x `shift_right` mk_int (size - 1)

#pop-options

inline_for_extraction
noextract
[@"opaque_to_smt"]
let lowest_bits
  (#t: inttype { supported_type t })
  (#sec: secrecy_level)
  (size: nat { size > 0 /\ size <= bits t })
  (x: int_t t sec { v x < pow2 (size) })
: Tot (z: int_t t sec { v z == v x % pow2 (size - 1) })
= FStar.Math.Lemmas.pow2_le_compat (bits t) (size); 
  x `logand` mod_mask (mk_int (size - 1))

noextract
[@must_inline "opaque_to_smt"]
let rec secret_is_lt
  (#t: inttype { supported_type t })
  (#sec: secrecy_level)
  (size: nat { size <= bits t })
  (x: int_t t sec { v x < pow2 (size) })
  (y: int_t t sec { v y < pow2 (size) })
: Tot (z: int_t t sec { v z == (if v x < v y then 1 else 0) })
  (decreases (size))
= if size = 0
  then secret_bool false
  else
    let xh = highest_bit size x in
    let xl = lowest_bits size x in
    let yh = highest_bit size y in
    let yl = lowest_bits size y in
    (xh `one_bit_lt` yh) `logor_one_bit`
    ((xh `one_bit_eq` yh) `logand_one_bit` secret_is_lt (size - 1) xl yl)

noextract
[@must_inline "opaque_to_smt"]
let rec secret_is_le
  (#t: inttype { supported_type t })
  (#sec: secrecy_level)
  (size: nat { size <= bits t })
  (x: int_t t sec { v x < pow2 (size) })
  (y: int_t t sec { v y < pow2 (size) })
: Tot (z: int_t t sec { v z == (if v x <= v y then 1 else 0) })
  (decreases (size))
= if size = 0
  then secret_bool true
  else
    let xh = highest_bit size x in
    let xl = lowest_bits size x in
    let yh = highest_bit size y in
    let yl = lowest_bits size y in
    (xh `one_bit_lt` yh) `logor_one_bit`
    ((xh `one_bit_eq` yh) `logand_one_bit` secret_is_le (size - 1) xl yl)

module BF = LowParse.BitFields

(* Bitfields of secret integers but public bit positions *) 

inline_for_extraction
noextract
[@"opaque_to_smt"]
let get_bitfield
  (#t: inttype { supported_type t })
  (#l: secrecy_level)
  (x: uint_t t l)
  (lo: U32.t)
  (hi: U32.t { U32.v lo < U32.v hi /\ U32.v hi <= bits t })
: Tot (y: uint_t t l { v y == BF.get_bitfield #(bits t) (v x) (U32.v lo) (U32.v hi) })
= BF.get_bitfield_eq_2 #(bits t) (v x) (U32.v lo) (U32.v hi);
  (x `shift_left` (U32.uint_to_t (bits t) `U32.sub` hi)) `shift_right` (U32.uint_to_t (bits t) `U32.sub` hi `U32.add` lo)

#push-options "--z3rlimit 64"

#restart-solver

inline_for_extraction
noextract
[@"opaque_to_smt"]
let set_bitfield
  (#t: inttype { supported_type t })
  (#l: secrecy_level)
  (x: uint_t t l)
  (lo: U32.t)
  (hi: U32.t { U32.v lo < U32.v hi /\ U32.v hi <= bits t })
  (w: uint_t t l { v w < pow2 (U32.v hi - U32.v lo) })
: Tot (y: uint_t t l { v y == BF.set_bitfield #(bits t) (v x) (U32.v lo) (U32.v hi) (v w) })
= BF.set_bitfield_eq #(bits t) (v x) (U32.v lo) (U32.v hi) (v w);
  U.lognot_lemma_1 #(bits t);
  (x `logand` lognot' ((ones t l `shift_right` (U32.uint_to_t (bits t) `U32.sub` (hi `U32.sub` lo))) `shift_left` lo)) `logor` (w `shift_left` lo)

#pop-options
