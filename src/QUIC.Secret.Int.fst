module QUIC.Secret.Int
module Aux = QUIC.Secret.Int.Aux

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

let logand_one_bit = Aux.logand_one_bit

let logor_one_bit = Aux.logor_one_bit

let logxor_one_bit = Aux.logxor_one_bit

let secret_bool = Aux.secret_bool

let lognot_one_bit = Aux.lognot_one_bit

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
  (x: uint32 { v x < pow2 2 })
  (y: uint32 { v y < pow2 2 })
: Tot (z: uint32 {
    v z == (if v x = v y then 1 else 0)
  })
= Aux.secrets_are_equal' x y
//  norm [delta_attr [(`%Aux.must_inline)]; iota; zeta; primops] (Aux.secrets_are_equal 2 x y)

let secret_is_le_64
  (x: uint64)
  (y: uint64)
: Tot (z: uint64 { v z == (if v x <= v y then 1 else 0) })
= norm [delta_attr [(`%Aux.must_inline)]; iota; zeta; primops] (Aux.secret_is_le 64 x y)

let secret_is_lt_64
  (x: uint64)
  (y: uint64)
: Tot (z: uint64 { v z == (if v x < v y then 1 else 0) })
= norm [delta_attr [(`%Aux.must_inline)]; iota; zeta; primops] (Aux.secret_is_lt 64 x y)

let secrets_are_equal_64_2
  (x: uint64 { v x < pow2 2 })
  (y: uint64 { v y < pow2 2 })
: Tot (z: uint64 {
    v z == (if v x = v y then 1 else 0)
  })
= norm [delta_attr [(`%Aux.must_inline)]; iota; zeta; primops] (Aux.secrets_are_equal 2 x y)

let secrets_are_equal_62
  (x: uint64 { v x < pow2 62 })
  (y: uint64 { v y < pow2 62 })
: Tot (z: uint64 {
    v z == (if v x = v y then 1 else 0)
  })
= // Aux.secrets_are_equal' x y
  norm [delta_attr [(`%Aux.must_inline)]; iota; zeta; primops] (Aux.secrets_are_equal 62 x y)

let min64 x y = Aux.min64 x y

let max64 x y = Aux.max64 x y
