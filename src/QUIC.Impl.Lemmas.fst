module QUIC.Impl.Lemmas
include QUIC.Spec.Lemmas

#set-options "--max_fuel 0 --max_ifuel 0"

/// The usual sequence lemmas
/// -------------------------

let lemma_five_cuts
  s i1 i2 i3 i4 i5 s0 s1 s2 s3 s4 s5
=
  ()

let hash_is_keysized_
  a
=
  assert_norm (512 < pow2 61);
  assert_norm (512 < pow2 125)

let lemma_slice
  #t s i
=
  ()

let lemma_slice3
  #a s i j
=
  ()

let lemma_slice0
  #a s
= ()

let lemma_slice1
  #a s i j
=
  ()


open FStar.Mul

#push-options "--max_fuel 1 --z3rlimit 100"
let pointwise_upd
  #a f b1 b2 i pos x
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

let rec pointwise_seq_map2
  #a f s1 s2 i
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
let rec and_inplace_commutative
  s1 s2
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
let rec seq_map2_xor0
  s1 s2
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
let upd_op_inplace
  #a op s x
=
  ()
#pop-options

/// Endianness lemmas
/// -----------------

#push-options "--z3rlimit 16"
#restart-solver
let rec be_to_n_slice
  s i
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
  len len' n
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

#restart-solver

let n_to_be_lower'
  len len' n
= let open FStar.Math.Lemmas in
  let open FStar.Endianness in
  pow2_le_compat (8 * len') (8 * len);
  let s1 = n_to_be len' n in
  let s2 = S.create (len' - len) 0uy `S.append` n_to_be len n in 
  let phi
    (i: nat {i < len'})
  : Lemma
    (S.index s1 i == S.index s2 i)
  = QSL.index_n_to_be len' n i;
    assert (len' - 1 - i == len - 1 - (i - (len' - len)));
    if len' - len <= i
    then begin
      QSL.index_n_to_be len n (i - (len' - len))
    end else begin
      pow2_le_compat (8 * (len' - 1 - i)) (8 * len);
      FStar.Math.Lemmas.small_div n (pow2 (8 * (len' - 1 - i)));
      assert (n / pow2 (8 * (len' - 1 - i)) == 0);
      assert (S.index s1 i == 0uy)
    end
  in
  Classical.forall_intro phi

#push-options "--z3rlimit 200"
inline_for_extraction noextract
let op_inplace'
  (#t: Type)
  (dst: B.buffer t)
  (dst_len: Ghost.erased U32.t)
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
      B.length dst == U32.v dst_len /\
      B.length dst >= U32.v ofs + B.length src)
    (ensures fun h0 _ h1 ->
      B.(modifies (loc_buffer dst) h0 h1) /\
      B.as_seq h1 dst `Seq.equal`
        pointwise_op op (B.as_seq h0 dst) (B.as_seq h0 src) (U32.v ofs) /\
      Seq.slice (B.as_seq h0 dst) 0 (U32.v ofs) `Seq.equal`
        Seq.slice (B.as_seq h1 dst) 0 (U32.v ofs) /\
      Seq.slice (B.as_seq h0 dst) (U32.v (ofs `U32.add` src_len)) (U32.v dst_len) `Seq.equal`
      Seq.slice (B.as_seq h1 dst) (U32.v (ofs `U32.add` src_len)) (U32.v dst_len))
=
  let h0 = HST.get () in
  let dst0 = B.sub dst 0ul ofs in
  let dst1 = B.sub dst ofs src_len in
  let dst2 = Ghost.hide (B.gsub dst (ofs `U32.add` src_len) (dst_len `U32.sub` (ofs `U32.add` src_len))) in
  C.Loops.in_place_map2 dst1 src src_len op;
  let h1 = HST.get () in
  calc (Seq.equal) {
    B.as_seq h1 dst;
  (Seq.equal) { lemma_slice3 (B.as_seq h1 dst) (U32.v ofs) (U32.v (ofs `U32.add` src_len)) }
    Seq.slice (B.as_seq h1 dst) 0 (U32.v ofs) `Seq.append`
    (Seq.slice (B.as_seq h1 dst) (U32.v ofs) (U32.v (ofs `U32.add` src_len))) `Seq.append`
    (Seq.slice (B.as_seq h1 dst) (U32.v (ofs `U32.add` src_len)) (B.length dst));
  (Seq.equal) {}
    Seq.slice (B.as_seq h0 dst) 0 (U32.v ofs) `Seq.append`
    (Seq.slice (B.as_seq h1 dst) (U32.v ofs) (U32.v (ofs `U32.add` src_len))) `Seq.append`
    (Seq.slice (B.as_seq h0 dst) (U32.v (ofs `U32.add` src_len)) (B.length dst));
  (Seq.equal) { pointwise_seq_map2 op (B.as_seq h0 dst1) (B.as_seq h0 src) 0 }
    Seq.slice (B.as_seq h0 dst) 0 (U32.v ofs) `Seq.append`
    (pointwise_op op
      (Seq.slice (B.as_seq h0 dst) (U32.v ofs) (U32.v (ofs `U32.add` src_len)))
      (B.as_seq h0 src)
      0) `Seq.append`
    (Seq.slice (B.as_seq h0 dst) (U32.v (ofs `U32.add` src_len)) (B.length dst));
  (Seq.equal) { pointwise_op_suff op (Seq.slice (B.as_seq h0 dst) 0 (U32.v ofs))
    (Seq.slice (B.as_seq h0 dst) (U32.v ofs) (U32.v (ofs `U32.add` src_len)))
    (B.as_seq h0 src)
    (U32.v ofs) }
    pointwise_op op
      (Seq.append (Seq.slice (B.as_seq h0 dst) 0 (U32.v ofs))
        (Seq.slice (B.as_seq h0 dst) (U32.v ofs) (U32.v (ofs `U32.add` src_len))))
      (B.as_seq h0 src)
      (U32.v ofs) `Seq.append`
    (Seq.slice (B.as_seq h0 dst) (U32.v (ofs `U32.add` src_len)) (B.length dst));
  (Seq.equal) { lemma_slice1 (B.as_seq h0 dst) (U32.v ofs) (U32.v (ofs `U32.add` src_len)) }
    pointwise_op op
      (Seq.slice (B.as_seq h0 dst) 0 (U32.v (ofs `U32.add` src_len)))
      (B.as_seq h0 src)
      (U32.v ofs) `Seq.append`
    (Seq.slice (B.as_seq h0 dst) (U32.v (ofs `U32.add` src_len)) (B.length dst));
  (Seq.equal) { pointwise_op_pref op
    (Seq.slice (B.as_seq h0 dst) 0 (U32.v (ofs `U32.add` src_len)))
    (Seq.slice (B.as_seq h0 dst) (U32.v (ofs `U32.add` src_len)) (B.length dst))
    (B.as_seq h0 src)
    (U32.v ofs)
  }
    pointwise_op op
      (Seq.slice (B.as_seq h0 dst) 0 (U32.v (ofs `U32.add` src_len)) `Seq.append`
      (Seq.slice (B.as_seq h0 dst) (U32.v (ofs `U32.add` src_len)) (B.length dst)))
      (B.as_seq h0 src)
      (U32.v ofs);
  (Seq.equal) { lemma_slice (B.as_seq h0 dst) (U32.v (ofs `U32.add` src_len)) }
    pointwise_op op
      (B.as_seq h0 dst)
      (B.as_seq h0 src)
      (U32.v ofs);
  }
#pop-options

let op_inplace
  #t dst src src_len ofs op
= op_inplace' dst (B.len dst) src src_len ofs op

let secret_and_inplace_eq
  b1 b2 pos
= let f
    (i: nat {i < S.length b1})
  : Lemma
    (S.index (S.seq_reveal (secret_and_inplace b1 b2 pos)) i == S.index (and_inplace (S.seq_reveal b1) (S.seq_reveal b2) pos) i)
  =
    pointwise_index (Secret.logand #Secret.U8 #Secret.SEC) b1 b2 i pos;
    pointwise_index U8.logand (S.seq_reveal b1) (S.seq_reveal b2) i pos
  in
  Classical.forall_intro f

let secret_xor_inplace_eq
  b1 b2 pos
= let f
    (i: nat {i < S.length b1})
  : Lemma
    (S.index (S.seq_reveal (secret_xor_inplace b1 b2 pos)) i == S.index (xor_inplace (S.seq_reveal b1) (S.seq_reveal b2) pos) i)
  =
    pointwise_index (Secret.logxor #Secret.U8 #Secret.SEC) b1 b2 i pos;
    pointwise_index U8.logxor (S.seq_reveal b1) (S.seq_reveal b2) i pos
  in
  Classical.forall_intro f
