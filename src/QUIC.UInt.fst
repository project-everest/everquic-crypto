module QUIC.UInt
include FStar.UInt
open FStar.Math.Lemmas

#push-options "--z3rlimit 16"

let rec to_vec_prefix
  (n: nat)
  (k: nat)
  (a: uint_t k)
: Lemma
  (requires (k <= n))
  (ensures (
    pow2 k <= pow2 n /\
    to_vec #k a `Seq.equal` Seq.slice (to_vec #n a) (n - k) n
  ))
  (decreases k)
= if k = 0
  then ()
  else to_vec_prefix (n - 1) (k - 1) (a / 2)

let rec to_vec_inc
  (n: nat)
  (k: nat)
  (a: uint_t k)
: Lemma
  (requires (k <= n))
  (ensures (
    pow2 k <= pow2 n /\
    to_vec #n a `Seq.equal` (Seq.create (n - k) false `Seq.append` to_vec #k a)
  ))
  (decreases k)
= if k = 0
  then ()
  else to_vec_inc (n - 1) (k - 1) (a / 2)

let lemma_logxor_lt (#n:pos) (a b:uint_t n) (k:nat{k <= n})
  : Lemma (requires a < pow2 k /\ b < pow2 k)
    (ensures a `logxor` b < pow2 k)
= if k = n
  then ()
  else if k = 0
  then begin
    assert_norm (pow2 0 == 1);
    assert (a == 0);
    assert (b == 0);
    logxor_self #n 0
  end
  else begin
    pow2_lt_compat n k;
    to_vec_inc n k a;
    to_vec_inc n k b;
    to_vec_inc n k (logxor #k a b);
    nth_lemma #n (logxor #k a b) (logxor #n a b)
  end

#pop-options
