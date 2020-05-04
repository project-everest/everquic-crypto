module QUIC.Secret.Int.Aux
include QUIC.Secret.Int.Base

module U = FStar.UInt

module U8 = FStar.UInt8
module U16 = FStar.UInt16
module U32 = FStar.UInt32
module U64 = FStar.UInt64


noextract noeq type must_inline =

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

#push-options "--z3rlimit 32"

[@"opaque_to_smt"]
noextract
inline_for_extraction
let ff00_to_10
  (#t: inttype { supported_type t })
  (#sec: secrecy_level)
  (x: int_t t sec { v x == 0 \/ v x == U.ones (bits t) })
: Tot (y: int_t t sec { v y == (if v x = 0 then 0 else 1) })
= logand_zeros (mk_int #t #sec 1);
  logand_ones (mk_int #t #sec 1);
  mk_int 1 `logand` x

#pop-options

[@"opaque_to_smt"]
noextract
inline_for_extraction
let secrets_are_equal
  (#t: inttype { supported_type t })
  (x: int_t t SEC)
  (y: int_t t SEC)
: Tot (z: int_t t SEC { v z == (if v x = v y then 1 else 0) })
  (decreases (size))
= ff00_to_10 (eq_mask x y)

[@"opaque_to_smt"]
noextract
inline_for_extraction
let secret_is_lt
  (#t: inttype { supported_type t })
  (x: int_t t SEC)
  (y: int_t t SEC)
: Tot (z: int_t t SEC { v z == (if v x < v y then 1 else 0) })
  (decreases (size))
= ff00_to_10 (lt_mask x y)

inline_for_extraction
noextract
[@"opaque_to_smt" must_inline]
let min
  (#t: inttype { supported_type t })
  (x y: uint_t t SEC)
: Tot (z: uint_t t SEC { v z == (if v x <= v y then v x else v y) })
=
  let cond = secret_is_lt x y in
  (cond `mul` x) `add` (lognot_one_bit cond `mul` y)

inline_for_extraction
noextract
[@"opaque_to_smt" must_inline]
let max
  (#t: inttype { supported_type t })
  (x y: uint_t t SEC)
: Tot (z: uint_t t SEC { v z == (if v y <= v x then v x else v y) })
= let cond = secret_is_lt y x in
  (cond `mul` x) `add` (lognot_one_bit cond `mul` y)

val min64
  (x y: uint64)
: Tot (z: uint64 { v z == (if v x <= v y then v x else v y) })

let min64
  x y
= min x y

val max64
  (x y: uint64)
: Tot (z: uint64 { v z == (if v y <= v x then v x else v y) })

let max64
  x y
= max x y
