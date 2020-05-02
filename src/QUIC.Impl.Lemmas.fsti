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
module B = LowStar.Buffer
module HST = FStar.HyperStack.ST

val lemma_five_cuts (#t: Type) (s: S.seq t) (i1 i2 i3 i4 i5: nat) (s0 s1 s2 s3 s4 s5: S.seq t): Lemma
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
    s0 `S.equal` S.slice s 0 i1 /\
    s1 `S.equal` S.slice s i1 i2 /\
    s2 `S.equal` S.slice s i2 i3 /\
    s3 `S.equal` S.slice s i3 i4 /\
    s4 `S.equal` S.slice s i4 i5 /\
    s5 `S.equal` S.slice s i5 (S.length s)))
  (ensures (
    let open S in
    s `equal` (s0 @| s1 @| s2 @| s3 @| s4 @| s5)))

val hash_is_keysized_ (a: QS.ha): Lemma
  (ensures (QS.keysized a (Spec.Hash.Definitions.hash_length a)))

val lemma_slice (#t: Type) (s: S.seq t) (i: nat { i <= S.length s }): Lemma
  (ensures (s `S.equal` S.append (S.slice s 0 i) (S.slice s i (S.length s))))

val lemma_slice3 (#a: Type) (s: S.seq a) (i j: nat): Lemma
  (requires (i <= j /\ j <= S.length s))
  (ensures (s `S.equal`
    (S.slice s 0 i `S.append` S.slice s i j `S.append` S.slice s j (S.length s))))

val lemma_slice0 (#a: Type) (s: S.seq a): Lemma (S.slice s 0 (S.length s) `S.equal` s)

val lemma_slice1 (#a: Type) (s: S.seq a) (i j: nat): Lemma
  (requires (i <= j /\ j <= S.length s))
  (ensures (S.slice s 0 j `S.equal`
    (S.slice s 0 i `S.append` S.slice s i j)))

open FStar.Mul

/// Lemmas about pointwise_op
/// -------------------------------------------

val pointwise_upd (#a: Type) (f: a -> a -> Tot a) (b1 b2: S.seq a) (i: nat) (pos: nat) (x: a): Lemma
  (requires (S.length b2 + pos <= S.length b1 /\ i < pos))
  (ensures (S.upd (QSL.pointwise_op f b1 b2 pos) i x `S.equal`
    QSL.pointwise_op f (S.upd b1 i x) b2 pos))

val pointwise_seq_map2 (#a: Type) (f: a -> a -> a) (s1 s2: S.seq a) (i: nat): Lemma
  (requires (
    let l = S.length s1 in
    S.length s2 = l - i /\ i <= S.length s1))
  (ensures (
    let l = S.length s1 in
    Spec.Loops.seq_map2 f (S.slice s1 i l) s2 `S.equal`
    S.slice (QSL.pointwise_op f s1 s2 i) i l))
  (decreases (S.length s2))

val and_inplace_commutative (s1 s2: S.seq U8.t): Lemma
  (requires S.length s1 = S.length s2)
  (ensures Spec.Loops.seq_map2 U8.logand s1 s2 `S.equal`
    Spec.Loops.seq_map2 U8.logand s2 s1)
  (decreases (S.length s1))

val seq_map2_xor0 (s1 s2: S.seq Secret.uint8): Lemma
  (requires
    S.length s1 = S.length s2 /\
    s1 `S.equal` S.create (S.length s2) (Secret.to_u8 0uy))
  (ensures
    Spec.Loops.seq_map2 EverCrypt.CTR.xor8 s1 s2 `S.equal` s2)
  (decreases (S.length s1))

val upd_op_inplace (#a:Type) (op: a -> a -> Tot a) (s: S.seq a) (x: a): Lemma
  (requires S.length s > 0)
  (ensures (S.upd s 0 (S.index s 0 `op` x) `S.equal`
    QSL.pointwise_op op s (S.create 1 x) 0))

val be_to_n_slice (s: S.seq U8.t) (i: nat): Lemma
  (requires i <= S.length s)
  (ensures FStar.Endianness.be_to_n (S.slice s i (S.length s)) =
    FStar.Endianness.be_to_n s % pow2 (8 `op_Multiply` (S.length s - i)))
  (decreases (S.length s))

val n_to_be_lower
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
    n_to_be len n `S.equal` S.slice (n_to_be len' n) (len' - len) len'
  ))

(* Inplace implementation of pointwise_op *)

inline_for_extraction noextract
val op_inplace
  (#t: Type)
  (dst: B.buffer t)
  (src: B.buffer t)
  (src_len: U32.t)
  (ofs: U32.t)
  (op: t -> t -> t)
:
  HST.Stack unit
    (requires fun h0 ->
      B.(all_live h0 [ buf dst; buf src ]) /\
      B.disjoint dst src /\
      B.length src == U32.v src_len /\
      B.length dst >= U32.v ofs + B.length src)
    (ensures fun h0 _ h1 ->
      B.(modifies (loc_buffer dst) h0 h1) /\
      B.as_seq h1 dst `S.equal`
        pointwise_op op (B.as_seq h0 dst) (B.as_seq h0 src) (U32.v ofs) /\
      S.slice (B.as_seq h0 dst) 0 (U32.v ofs) `S.equal`
        S.slice (B.as_seq h1 dst) 0 (U32.v ofs) /\
      S.slice (B.as_seq h0 dst) (U32.v (ofs `U32.add` src_len)) (B.length dst) `S.equal`
      S.slice (B.as_seq h1 dst) (U32.v (ofs `U32.add` src_len)) (B.length dst))

(* Secret operation specs *)

let secret_and_inplace (b1 b2:S.seq Secret.uint8) (pos:nat)
  : Pure (S.seq Secret.uint8)
  (requires S.length b2 + pos <= S.length b1)
  (ensures fun b -> S.length b == S.length b1)
=
  pointwise_op (Secret.logand #Secret.U8 #Secret.SEC) b1 b2 pos

val secret_and_inplace_eq
  (b1 b2: S.seq Secret.uint8)
  (pos: nat)
: Lemma
  (requires (S.length b2 + pos <= S.length b1))
  (ensures (
    S.length b2 + pos <= S.length b1/\
    S.seq_reveal (secret_and_inplace b1 b2 pos) `S.equal` and_inplace (S.seq_reveal b1) (S.seq_reveal b2) pos
  ))
  [SMTPat (secret_and_inplace b1 b2 pos)]

let secret_xor_inplace (b1 b2:Seq.seq Secret.uint8) (pos:nat)
  : Pure (Seq.seq Secret.uint8)
  (requires Seq.length b2 + pos <= Seq.length b1)
  (ensures fun b -> Seq.length b == Seq.length b1)
=
  pointwise_op (Secret.logxor #Secret.U8 #Secret.SEC) b1 b2 pos

val secret_xor_inplace_eq
  (b1 b2: S.seq Secret.uint8)
  (pos: nat)
: Lemma
  (requires (S.length b2 + pos <= S.length b1))
  (ensures (
    S.length b2 + pos <= S.length b1/\
    S.seq_reveal (secret_xor_inplace b1 b2 pos) `S.equal` xor_inplace (S.seq_reveal b1) (S.seq_reveal b2) pos
  ))
  [SMTPat (secret_xor_inplace b1 b2 pos)]
