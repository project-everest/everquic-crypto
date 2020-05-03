module QUIC.Secret.Int
include QUIC.Secret.Int.Base

module U8 = FStar.UInt8
module U16 = FStar.UInt16
module U32 = FStar.UInt32
module U64 = FStar.UInt64
module U = FStar.UInt
module BF = LowParse.BitFields

inline_for_extraction
noextract
val hide
  (#t: inttype { unsigned t })
  (#sec: secrecy_level)
  (x: uint_t t sec)
: Tot (y: uint_t t SEC { v y == v x })

inline_for_extraction
noextract
val reveal
  (#t: inttype { unsigned t })
  (#sec: secrecy_level)
  (x: uint_t t sec)
: GTot (y: uint_t t PUB { v y == v x })

let hide_reveal
  (#t: inttype { unsigned t })
  (x: uint_t t SEC)
: Lemma
  (hide (reveal x) == x)
  [SMTPat (hide (reveal x))]
= ()

let reveal_hide
  (#t: inttype { unsigned t })
  (x: uint_t t PUB)
: Lemma
  (reveal (hide x) == x)
  [SMTPat (reveal (hide x))]
= ()

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
val lognot'
  (#t:inttype { supported_type t })
  (#l:secrecy_level)
  (x: uint_t t l)
: Tot (y: uint_t t l { v y == U.lognot #(bits t) (v x) })

(* Logic *)

inline_for_extraction
noextract
val logand_one_bit
  (#t: inttype { supported_type t })
  (#sec: secrecy_level)
  (x: int_t t sec { v x == 0 \/ v x == 1 })
  (y: int_t t sec { v y == 0 \/ v y == 1 })
: Tot (z: int_t t sec { v z == (if v x = 1 && v y = 1 then 1 else 0) })

inline_for_extraction
noextract
val logor_one_bit
  (#t: inttype { supported_type t })
  (#sec: secrecy_level)
  (x: int_t t sec { v x == 0 \/ v x == 1 })
  (y: int_t t sec { v y == 0 \/ v y == 1 })
: Tot (z: int_t t sec { v z == (if v x = 1 || v y = 1 then 1 else 0) })

inline_for_extraction
noextract
val logxor_one_bit
  (#t: inttype { supported_type t })
  (#sec: secrecy_level)
  (x: int_t t sec { v x == 0 \/ v x == 1 })
  (y: int_t t sec { v y == 0 \/ v y == 1 })
: Tot (z: int_t t sec { v z == (if v x = v y then 0 else 1) })

inline_for_extraction
noextract
val secret_bool
  (#t: inttype { supported_type t })
  (#sec: secrecy_level)
  (x: bool)
: Tot (z: int_t t sec { v z == (if x then 1 else 0) })

inline_for_extraction
noextract
val lognot_one_bit
  (#t: inttype { supported_type t })
  (#sec: secrecy_level)
  (x: int_t t sec { v x == 0 \/ v x == 1 })
: Tot (z: int_t t sec { v z == (if v x = 1 then 0 else 1) })


(* Bitfields of secret integers but public bit positions *) 

inline_for_extraction
noextract
val get_bitfield
  (#t: inttype { supported_type t })
  (#l: secrecy_level)
  (x: uint_t t l)
  (lo: U32.t)
  (hi: U32.t { U32.v lo < U32.v hi /\ U32.v hi <= bits t })
: Tot (y: uint_t t l { v y == BF.get_bitfield #(bits t) (v x) (U32.v lo) (U32.v hi) })

inline_for_extraction
noextract
[@"opaque_to_smt"]
val set_bitfield
  (#t: inttype { supported_type t })
  (#l: secrecy_level)
  (x: uint_t t l)
  (lo: U32.t)
  (hi: U32.t { U32.v lo < U32.v hi /\ U32.v hi <= bits t })
  (w: uint_t t l { v w < pow2 (U32.v hi - U32.v lo) })
: Tot (y: uint_t t l { v y == BF.set_bitfield #(bits t) (v x) (U32.v lo) (U32.v hi) (v w) })

(* Comparisons *)

val secrets_are_equal_32_2
  (x: uint32 { v x < pow2 2 })
  (y: uint32 { v y < pow2 2 })
: Tot (z: uint32 {
    v z == (if v x = v y then 1 else 0)
  })

val secret_is_le_64
  (x: uint64)
  (y: uint64)
: Tot (z: uint64 { v z == (if v x <= v y then 1 else 0) })

val secret_is_lt_64
  (x: uint64)
  (y: uint64)
: Tot (z: uint64 { v z == (if v x < v y then 1 else 0) })

val secrets_are_equal_64_2
  (x: uint64 { v x < pow2 2 })
  (y: uint64 { v y < pow2 2 })
: Tot (z: uint64 {
    v z == (if v x = v y then 1 else 0)
  })

val secrets_are_equal_62
  (x: uint64 { v x < pow2 62 })
  (y: uint64 { v y < pow2 62 })
: Tot (z: uint64 {
    v z == (if v x = v y then 1 else 0)
  })
