module QUIC.Impl.Lemmas
include QUIC.Spec.Lemmas

module G = FStar.Ghost
module S = QUIC.Secret.Seq

module U64 = FStar.UInt64
module U32 = FStar.UInt32
module U8 = FStar.UInt8

module QS = QUIC.Spec
module QSL = QUIC.Spec.Lemmas

module Secret = QUIC.Secret.Int

#set-options "--max_fuel 0 --max_ifuel 0"

/// The usual sequence lemmas
/// -------------------------

let lemma_five_cuts (s: S.seq U8.t) (i1 i2 i3 i4 i5: nat) (s0 s1 s2 s3 s4 s5: S.seq U8.t): Lemma
  (requires (
    i1 <= S.length s /\
    i2 <= S.length s /\
    i3 <= S.length s /\
    i4 <= S.length s /\
    i5 <= S.length s /\
    i1 <= i2 /\
    i2 <= i3 /\
    i3 <= i4 /\
    i4 <= i5 /\
    s0 `Seq.equal` S.slice s 0 i1 /\
    s1 `Seq.equal` S.slice s i1 i2 /\
    s2 `Seq.equal` S.slice s i2 i3 /\
    s3 `Seq.equal` S.slice s i3 i4 /\
    s4 `Seq.equal` S.slice s i4 i5 /\
    s5 `Seq.equal` S.slice s i5 (S.length s)))
  (ensures (
    let open S in
    s `equal` (s0 @| s1 @| s2 @| s3 @| s4 @| s5)))
=
  ()

let hash_is_keysized_ (a: QS.ha): Lemma
  (ensures (QS.keysized a (Spec.Hash.Definitions.hash_length a)))
=
  assert_norm (512 < pow2 61);
  assert_norm (512 < pow2 125)


let lemma_slice s (i: nat { i <= S.length s }): Lemma
  (ensures (s `S.equal` S.append (S.slice s 0 i) (S.slice s i (S.length s))))
=
  ()

let lemma_slice3 #a (s: S.seq a) (i j: nat): Lemma
  (requires (i <= j /\ j <= S.length s))
  (ensures (s `S.equal`
    (S.slice s 0 i `S.append` S.slice s i j `S.append` S.slice s j (S.length s))))
=
  ()

let lemma_slice0 #a (s: S.seq a): Lemma (S.slice s 0 (S.length s) `S.equal` s) = ()

let lemma_slice1 #a (s: S.seq a) (i j: nat): Lemma
  (requires (i <= j /\ j <= S.length s))
  (ensures (S.slice s 0 j `S.equal`
    (S.slice s 0 i `S.append` S.slice s i j)))
=
  ()


open FStar.Mul

/// Lemmas about pointwise_op
/// -------------------------------------------

#push-options "--max_fuel 1 --z3rlimit 100"
let pointwise_upd (#a: Type) f b1 b2 i pos (x: a): Lemma
  (requires (S.length b2 + pos <= S.length b1 /\ i < pos))
  (ensures (S.upd (QSL.pointwise_op f b1 b2 pos) i x `S.equal`
    QSL.pointwise_op f (S.upd b1 i x) b2 pos))
  (decreases (S.length b2))
=
  calc (S.equal) {
    QSL.pointwise_op f (S.upd b1 i x) b2 pos;
  (S.equal) { lemma_slice (S.upd b1 i x) (i + 1) }
    QSL.pointwise_op f
      S.(slice (S.upd b1 i x) 0 (i + 1) @| S.slice (S.upd b1 i x) (i + 1) (S.length b1))
      b2 pos;
  (S.equal) { }
    QSL.pointwise_op f
      S.(slice (S.upd b1 i x) 0 (i + 1) @| S.slice b1 (i + 1) (S.length b1))
      b2 pos;
  (S.equal) {
    QSL.pointwise_op_suff f
      (S.slice (S.upd b1 i x) 0 (i + 1))
      (S.slice b1 (i + 1) (S.length b1)) b2 pos
  }
    S.slice (S.upd b1 i x) 0 (i + 1) `S.append`
    QSL.pointwise_op f
      (S.slice b1 (i + 1) (S.length b1))
      b2 (pos - (i + 1));
  (S.equal) { }
    S.upd (S.slice b1 0 (i + 1)) i x `S.append`
    QSL.pointwise_op f
      (S.slice b1 (i + 1) (S.length b1))
      b2 (pos - (i + 1));
  (S.equal) { }
    S.upd (S.slice b1 0 (i + 1) `S.append`
    QSL.pointwise_op f
      (S.slice b1 (i + 1) (S.length b1))
      b2 (pos - (i + 1))
    ) i x;
  (S.equal) {
    QSL.pointwise_op_suff f
      (S.slice b1 0 (i + 1))
      (S.slice b1 (i + 1) (S.length b1)) b2 pos
  }
    S.upd (
      QSL.pointwise_op f
      (S.slice b1 0 (i + 1) `S.append` S.slice b1 (i + 1) (S.length b1))
      b2 pos
    ) i x;
  (S.equal) { lemma_slice b1 (i + 1) }
    S.upd (QSL.pointwise_op f b1 b2 pos) i x;
  }

let rec pointwise_seq_map2 (#a: Type) (f: a -> a -> a) (s1 s2: S.seq a) (i: nat): Lemma
  (requires (
    let l = S.length s1 in
    S.length s2 = l - i /\ i <= S.length s1))
  (ensures (
    let l = S.length s1 in
    Spec.Loops.seq_map2 f (S.slice s1 i l) s2 `S.equal`
    S.slice (QSL.pointwise_op f s1 s2 i) i l))
  (decreases (S.length s2))
=
  if S.length s2 = 0 then
    ()
  else
    let l = S.length s1 in
    calc (S.equal) {
      Spec.Loops.seq_map2 f (S.slice s1 i l) s2;
    (S.equal) {}
      S.cons (f (S.head (S.slice s1 i l)) (S.head s2))
        (Spec.Loops.seq_map2 f (S.tail (S.slice s1 i l)) (S.tail s2));
    (S.equal) {}
      S.cons (f (S.head (S.slice s1 i l)) (S.head s2))
        (Spec.Loops.seq_map2 f (S.slice s1 (i + 1) l) (S.tail s2));
    (S.equal) { pointwise_seq_map2 f s1 (S.slice s2 1 (S.length s2)) (i + 1) }
      S.cons (f (S.head (S.slice s1 i l)) (S.head s2))
        (S.slice (QSL.pointwise_op f s1 (S.tail s2) (i + 1)) (i + 1) l);
    (S.equal) { }
      S.slice (
        S.upd (QSL.pointwise_op f s1 (S.tail s2) (i + 1))
          i
          (f (S.head (S.slice s1 i l)) (S.head s2)))
        i
        l;
    (S.equal) { }
      S.slice (
        S.upd (QSL.pointwise_op f s1 (S.slice s2 1 (S.length s2)) (i + 1))
          i
          (f (S.head (S.slice s1 i l)) (S.head s2)))
        i
        l;
    (S.equal) {
      pointwise_upd f s1 (S.slice s2 1 (S.length s2)) i (i + 1)
        (f (S.head (S.slice s1 i l)) (S.head s2))
    }
      S.slice
        (QSL.pointwise_op f
          (S.upd s1 i (f (S.head (S.slice s1 i l)) (S.head s2)))
          (S.slice s2 1 (S.length s2))
          (i + 1))
        i l;

    };
    ()
#pop-options

#push-options "--max_fuel 2 --initial_fuel 2 --max_ifuel 1 --initial_ifuel 1"
let rec and_inplace_commutative (s1 s2: S.seq U8.t): Lemma
  (requires S.length s1 = S.length s2)
  (ensures Spec.Loops.seq_map2 U8.logand s1 s2 `S.equal`
    Spec.Loops.seq_map2 U8.logand s2 s1)
  (decreases (S.length s1))
=
  if S.length s1 = 0 then
    ()
  else (
    FStar.UInt.logand_commutative #8 (U8.v (S.head s1)) (U8.v (S.head s2));
    assert (U8.logand (S.head s1) (S.head s2) = U8.logand (S.head s2) (S.head s1));
    and_inplace_commutative (S.tail s1) (S.tail s2);
    assert (Spec.Loops.seq_map2 U8.logand (S.tail s1) (S.tail s2) `S.equal`
      Spec.Loops.seq_map2 U8.logand (S.tail s2) (S.tail s1))
  )
#pop-options

#push-options "--max_fuel 1"
let rec seq_map2_xor0 (s1 s2: S.seq Secret.uint8): Lemma
  (requires
    S.length s1 = S.length s2 /\
    s1 `S.equal` S.create (S.length s2) (Secret.to_u8 0uy))
  (ensures
    Spec.Loops.seq_map2 EverCrypt.CTR.xor8 s1 s2 `S.equal` s2)
  (decreases (S.length s1))
=
  if S.length s1 = 0 then
    ()
  else
    let open FStar.UInt in
    logxor_lemma_1 #8 (Secret.v (S.head s2));
    logxor_lemma_1 #8 (Secret.v (S.head s1));
    logxor_commutative #8 (Secret.v (S.head s1)) (Secret.v (S.head s2));
    assert (Secret.v (S.head (Spec.Loops.seq_map2 EverCrypt.CTR.xor8 s1 s2)) == Secret.v (S.head s2));
    seq_map2_xor0 (S.tail s1) (S.tail s2)
#pop-options

#push-options "--max_fuel 2 --initial_fuel 2 --max_ifuel 1 --initial_ifuel 1"
let upd_op_inplace (#a:Type) op (s: S.seq a) (x: a): Lemma
  (requires S.length s > 0)
  (ensures (S.upd s 0 (S.index s 0 `op` x) `S.equal`
    QSL.pointwise_op op s (S.create 1 x) 0))
=
  ()
#pop-options

/// Endianness lemmas
/// -----------------

#push-options "--z3rlimit 16"
#restart-solver
let rec be_to_n_slice (s: S.seq U8.t) (i: nat): Lemma
  (requires i <= S.length s)
  (ensures FStar.Endianness.be_to_n (S.slice s i (S.length s)) =
    FStar.Endianness.be_to_n s % pow2 (8 `op_Multiply` (S.length s - i)))
  (decreases (S.length s))
=
  FStar.Endianness.reveal_be_to_n s;
  if S.length s = 0 then
    ()
  else
    let open FStar.Endianness in
    if i = S.length s then begin
      reveal_be_to_n S.empty;
      assert_norm (pow2 (8 * 0) = 1);
      assert (S.slice s (S.length s) (S.length s) `S.equal` S.empty);
      assert (be_to_n S.empty = 0);
      assert (be_to_n s % 1 = 0)
    end else
      let s' = (S.slice s i (S.length s)) in
      let s_prefix = (S.slice s 0 (S.length s - 1)) in
      assert (S.length s' <> 0);
      assert (8 <= 8 * (S.length s - i));
      FStar.Math.Lemmas.pow2_le_compat (8 * (S.length s - i)) 8;
      assert_norm (pow2 (8 * 1) = 256);
      assert (U8.v (S.last s) < pow2 (8 * (S.length s - i)));
      assert (S.length s' = S.length s_prefix - i + 1);
      FStar.Math.Lemmas.pow2_le_compat (8 * (S.length s')) (8 * (S.length s - i));
      calc (==) {
        be_to_n s';
      (==) {
        lemma_be_to_n_is_bounded s';
        FStar.Math.Lemmas.small_mod (be_to_n s') (pow2 (8 * (S.length s - i)))
      }
        (be_to_n s') % (pow2 (8 * (S.length s - i)));
      (==) { reveal_be_to_n s' }
        (U8.v (S.last s') + pow2 8 * be_to_n (S.slice s' 0 (S.length s' - 1))) %
          (pow2 (8 * (S.length s - i)));
      (==) { }
        (U8.v (S.last s) + pow2 8 * be_to_n (S.slice s i (S.length s - 1))) %
          (pow2 (8 * (S.length s - i)));
      (==) { }
        (U8.v (S.last s) + pow2 8 * (be_to_n (S.slice s_prefix i (S.length s_prefix)))) %
          (pow2 (8 * (S.length s - i)));
      (==) { be_to_n_slice s_prefix i }
        (U8.v (S.last s) + pow2 8 * (be_to_n s_prefix % pow2 (8 * (S.length s_prefix - i)))) %
          (pow2 (8 * (S.length s - i)));
      (==) { FStar.Math.Lemmas.pow2_multiplication_modulo_lemma_2
        (be_to_n s_prefix) (8 * (S.length s_prefix - i) + 8) 8
      }
        (U8.v (S.last s) +
          ((be_to_n s_prefix * pow2 8) % pow2 (8 * (S.length s_prefix - i) + 8))
        ) %
          (pow2 (8 * (S.length s - i)));
      (==) { }
        (U8.v (S.last s) +
          ((be_to_n s_prefix * pow2 8) % pow2 (8 * (S.length s - i)))
        ) %
          (pow2 (8 * (S.length s - i)));
      (==) { FStar.Math.Lemmas.lemma_mod_add_distr
        (U8.v (S.last s))
        (be_to_n s_prefix * pow2 8)
        (pow2 (8 * (S.length s - i)))
      }
        (U8.v (S.last s) + pow2 8 * be_to_n (S.slice s 0 (S.length s - 1))) %
          pow2 (8 * (S.length s - i));
      }
#pop-options

let n_to_be_lower
  (len: nat)
  (len' : nat)
  (n: nat)
: Lemma
  (requires (
    len <= len' /\
    n < pow2 (8 * len)
  ))
  (ensures (
    let open FStar.Endianness in
    n < pow2 (8 * len') /\
    n_to_be len n `FStar.Seq.equal` FStar.Seq.slice (n_to_be len' n) (len' - len) len'
  ))
= let open FStar.Math.Lemmas in
  let open FStar.Endianness in
  pow2_le_compat (8 * len') (8 * len);
  let s1 = n_to_be len n in
  let s2 = FStar.Seq.slice (n_to_be len' n) (len' - len) len' in
  let phi
    (i: nat {i < len})
  : Lemma
    (S.index s1 i == S.index s2 i)
  = QSL.index_n_to_be len n i;
    QSL.index_n_to_be len' n (i + len' - len)
  in
  Classical.forall_intro phi
