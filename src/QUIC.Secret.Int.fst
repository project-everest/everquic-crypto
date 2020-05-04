module QUIC.Secret.Int

let usub
  #t #sec x y
= x `sub` y

let cast_up
  #t1 t2 #sec x
= cast t2 SEC x

let cast_down
  #t1 t2 #sec x
= cast t2 SEC x

let hide
  #t #sec x
= cast t SEC x

let reveal
  #t #sec x
= mk_int #t (v x)


let lognot'
  #t #l x
= U.nth_lemma #(bits t) (U.lognot (v x)) (v x `U.logxor` v (ones t l));
  x `logxor` ones t l

let logand_one_bit
  #t #sec x y
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

let logor_one_bit
  #t #sec x y
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

let logxor_one_bit
  #t #sec x y
= logxor_one_bit' x y;
  x `logxor` y

let secret_bool
  #t #sec x
= cast t sec (if x then 1uy else 0uy)

let lognot_one_bit
  #t #sec x
= x `logxor_one_bit` secret_bool true

(* Conversion between HACL*'s 00/FF style and our 0/1 style *)

[@"opaque_to_smt"]
noextract
inline_for_extraction
let ff00_to_10
  (#t: inttype { supported_type t })
  (#sec: secrecy_level)
  (x: int_t t sec { v x == 0 \/ v x == U.ones (bits t) })
: Tot (y: int_t t sec { v y == (if v x = 0 then 0 else 1) })
= U.logand_lemma_1 #(bits t) 1;
  U.logand_lemma_2 #(bits t) 1;
  mk_int 1 `logand` x

(* Comparisons *)

noextract
[@"opaque_to_smt"]
inline_for_extraction
let secrets_are_equal
  (#t: inttype { supported_type t })
  (size: nat)
  (x: int_t t SEC { v x < pow2 size })
  (y: int_t t SEC { v y < pow2 size })
: Tot (z: int_t t SEC {
    v z == (if v x = v y then 1 else 0)
  })
= eq_mask_lemma #t x y;
  ff00_to_10 (eq_mask #t x y)

noextract
[@"opaque_to_smt"]
inline_for_extraction
let secret_is_lt
  (#t: inttype { supported_type t })
  (size: nat { size <= bits t })
  (x: int_t t SEC { v x < pow2 (size) })
  (y: int_t t SEC { v y < pow2 (size) })
: Tot (z: int_t t SEC { v z == (if v x < v y then 1 else 0) })
  (decreases (size))
= lt_mask_lemma #t x y;
  ff00_to_10 (lt_mask #t x y)

noextract
[@"opaque_to_smt"]
inline_for_extraction
let secret_is_le
  (#t: inttype { supported_type t })
  (size: nat { size <= bits t })
  (x: int_t t SEC { v x < pow2 (size) })
  (y: int_t t SEC { v y < pow2 (size) })
: Tot (z: int_t t SEC { v z == (if v x <= v y then 1 else 0) })
= secret_is_lt size x y `logor_one_bit` secrets_are_equal size x y

#push-options "--z3rlimit 64"

#restart-solver

let get_bitfield
  #t #l x lo hi
= BF.get_bitfield_eq_2 #(bits t) (v x) (U32.v lo) (U32.v hi);
  (x `shift_left` (U32.uint_to_t (bits t) `U32.sub` hi)) `shift_right` (U32.uint_to_t (bits t) `U32.sub` hi `U32.add` lo)

#restart-solver

let set_bitfield
  #t #l x lo hi w
= BF.set_bitfield_eq #(bits t) (v x) (U32.v lo) (U32.v hi) (v w);
  U.lognot_lemma_1 #(bits t);
  (x `logand` lognot' ((ones t l `shift_right` (U32.uint_to_t (bits t) `U32.sub` (hi `U32.sub` lo))) `shift_left` lo)) `logor` (w `shift_left` lo)

#pop-options

(* Instances *)

let secrets_are_equal_32_2
  x y
= (secrets_are_equal 2 x y)

let secret_is_le_64
  x y
= (secret_is_le 64 x y)

let secret_is_lt_64
  x y
= (secret_is_lt 64 x y)

let secrets_are_equal_64_2
  x y
= (secrets_are_equal 2 x y)

let secrets_are_equal_62
  x y
= (secrets_are_equal 62 x y)

#push-options "--z3rlimit 16"

let min
  #t x y
=
  let cond = secret_is_le (bits t) x y in
  (cond `mul` x) `add` (lognot_one_bit cond `mul` y)

let max
  #t x y
=
  let cond = secret_is_le (bits t) y x in
  (cond `mul` x) `add` (lognot_one_bit cond `mul` y)

#pop-options
