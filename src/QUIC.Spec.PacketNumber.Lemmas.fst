module QUIC.Spec.PacketNumber.Lemmas

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
#pop-options

#push-options "--z3rlimit 512"

#restart-solver
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

module Secret = QUIC.Secret.Int
module U = FStar.UInt
  
let logand_mask (#n:pos) (a:U.uint_t n) (m:nat{m <= n})
: Lemma (pow2 m <= pow2 n /\ U.logand #n a (pow2 m - 1) == a % pow2 m)
= if m = 0
  then U.logand_lemma_1 a
  else if m = n
  then begin
    FStar.Math.Lemmas.small_mod a (pow2 n);
    U.logand_lemma_2 a
  end
  else U.logand_mask a m

#pop-options

#push-options "--z3rlimit 1024"

#restart-solver

inline_for_extraction
let replace_modulo
  (a: Secret.uint64 { Secret.v a < pow2 62 })
  (b_size: FStar.Ghost.erased nat { b_size <= 64 })
  (b_mask: Secret.uint64 { Secret.v b_mask == pow2 b_size - 1 })
  (new_mod: Secret.uint64)
: Pure Secret.uint64
  (requires Secret.v new_mod < pow2 (b_size))
  (ensures fun res -> Secret.v res == replace_modulo' (Secret.v a) (pow2 (b_size)) (Secret.v new_mod))
=
  let open FStar.Math.Lemmas in
  [@inline_let] let _ =
    lemma_mod_plus (Secret.v new_mod) (Secret.v a / pow2 b_size) (pow2 b_size);
    Secret.logand_spec a b_mask;
    logand_mask #64 (Secret.v a) b_size;
    small_mod (Secret.v new_mod) (pow2 b_size);
    lemma_mod_lt (Secret.v a) (pow2 b_size)
  in
  (a `Secret.sub` (a `Secret.logand` b_mask)) `Secret.add` new_mod

#pop-options
