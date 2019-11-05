module QUIC.Parse.Lemmas
open QUIC.Spec.Base

let replace_modulo' (a b new_mod:nat) : Pure nat
  (requires b > 0 /\ new_mod < b)
  (ensures fun res -> res % b = new_mod /\ res / b = a / b) =
  let open FStar.Math.Lemmas in
  let res = a - a%b + new_mod in
  lemma_mod_plus new_mod (a/b) b;
  small_mod new_mod b;
  res

#push-options "--z3rlimit 256"
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

module U64 = FStar.UInt64

#restart-solver

inline_for_extraction
let replace_modulo (a: uint62_t) (b new_mod: U64.t) : Pure U64.t
  (requires U64.v b > 0 /\ U64.v new_mod < U64.v b)
  (ensures fun res -> U64.v res == replace_modulo' (U64.v a) (U64.v b) (U64.v new_mod))
=
  let open FStar.Math.Lemmas in
  [@inline_let] let _ =
    lemma_mod_plus (U64.v new_mod) (U64.v a / U64.v b) (U64.v b);
    small_mod (U64.v new_mod) (U64.v b)
  in
  (a `U64.sub` (a `U64.rem` b)) `U64.add` new_mod

#pop-options
