module QUIC.Spec.Lemmas
open QUIC.Spec.Base

module S = FStar.Seq
module U8 = FStar.UInt8

(* library lemmas *)

let suffix (b:bytes) (n:nat{n <= S.length b}) = S.slice b n (S.length b)

let max (a b:int) : Tot (n:int{n >= a /\ n >= b}) =
  if a > b then a else b // this must exist somewhere...

// Move to FStar.Math.Lemmas?
let lemma_mod_pow2 (a:nat) (b:nat) : Lemma
  (requires a >= b) (ensures pow2 a % pow2 b == 0)
  [SMTPat (pow2 a % pow2 b)]
  =
  let open FStar.Math.Lemmas in
  lemma_div_mod (pow2 a) (pow2 b);
  pow2_minus a b;
  pow2_plus b (a-b)

#push-options "--z3rlimit 16"

let lemma_divrem2 (k:nat) (a:nat) (n:nat)
  : Lemma (requires a >= k /\ n < pow2 k)
  (ensures ((pow2 a + n) % pow2 k == n /\ (pow2 a + n) / pow2 k == pow2 (a - k)))
  =
  let open FStar.Math.Lemmas in
  let open FStar.Mul in
  modulo_distributivity (pow2 a) n (pow2 k);
  small_mod n (pow2 k);
  lemma_div_mod (pow2 a + n) (pow2 k);
  pow2_minus a k

#pop-options

// We really should have this pattern already...
let lemma_mod0 (x:pos) : Lemma (0 % x == 0)
  [SMTPat (0 % x)] = ()

// Move to FStar.Math.Lemmas?
let lemma_pow2_div (a:nat) (b:nat) (k:nat)
  : Lemma (requires a >= k /\ b >= k)
    (ensures (pow2 a + pow2 b) / pow2 k == pow2 (a - k) + pow2 (b - k))
  =
  let open FStar.Math.Lemmas in
  let open FStar.Mul in
  pow2_plus k (b - k);
  division_addition_lemma (pow2 a) (pow2 k) (pow2 (b-k));
  pow2_minus b k;
  pow2_minus a k

#restart-solver

let lemma_pow2_div2 (a:nat) (b:nat) (c:nat)
  : Lemma ((a / pow2 b) / pow2 c == a / (pow2 (c + b)))
  =
  let open FStar.Math.Lemmas in
  pow2_plus b c;
  division_multiplication_lemma a (pow2 b) (pow2 c)

let lemma_div_sub_small (l:nat) (n:nat) (x:nat)
  : Lemma (requires l > 1)
  (ensures (n - n % pow2 8) / pow2 (8 `op_Multiply` (l-1)) == n / pow2 (8 `op_Multiply` (l-1)))
  =
  let open FStar.Math.Lemmas in
  let open FStar.Mul in
  lemma_mod_spec n (pow2 8);
  lemma_pow2_div2 n 8 (8*(l-2));
  lemma_pow2_div2 (n - n % pow2 8) 8 (8*(l-2))

#push-options "--z3rlimit 20"
let rec lemma_be_index (l:pos) (n:nat{n < pow2 (8 `op_Multiply` l)})
  : Lemma (ensures U8.v (S.index (FStar.Endianness.n_to_be l n) 0)
    == n / pow2 (8 `op_Multiply` (l-1)))
    (decreases %[l])
  =
  let open FStar.Endianness in
  let open FStar.Mul in
  let b = n_to_be l n in
  let b0 = S.index b 0 in
  reveal_be_to_n b;
  if l = 1 then ()
  else
    let b1 = S.last b in
    let b' = S.slice b 0 (l-1) in
    let b0' = S.index b' 0 in
    reveal_be_to_n b';
    assert(U8.v b1 == n % pow2 8);
    lemma_be_to_n_is_bounded b';
    lemma_be_index (l-1) (be_to_n b');
    lemma_pow2_div2 (n - U8.v b1) 8 (8 * (l-1) - 8);
    lemma_div_sub_small l n (U8.v b1)
#pop-options


let lemma_be_index_bytes (l:pos) (b:bytes) : Lemma
  (requires S.length b >= l)
  (ensures FStar.Endianness.be_to_n (S.slice b 0 l) / pow2 (8 `op_Multiply` (l-1)) = U8.v (S.index b 0)) =
  let open FStar.Endianness in
  let n = be_to_n (S.slice b 0 l) in
  lemma_be_to_n_is_bounded (S.slice b 0 l);
  lemma_be_index l n;
  n_to_be_be_to_n l (S.slice b 0 l)


/// generic lemmas for sequences

let append_slices1 (#a:eqtype) (s1 s2:S.seq a) : Lemma
  (S.equal s1 (S.slice (S.append s1 s2) 0 (S.length s1))) =
  ()

let append_slices2 (#a:eqtype) (s1 s2:S.seq a) : Lemma
  (Seq.equal s2 (Seq.slice (Seq.append s1 s2) (Seq.length s1) (Seq.length s1 + Seq.length s2))) =
  ()

let append_slices3 (#a:eqtype) (s1 s2:S.seq a) : Lemma
  ( (forall (i:nat) (j:nat).
                i <= j /\ j <= Seq.length s2 ==>
                Seq.equal (Seq.slice s2 i j)
                          (Seq.slice (Seq.append s1 s2) (Seq.length s1 + i) (Seq.length s1 + j)))) =
  ()

let lemma_create_slice b i : Lemma
  (requires S.length b >= i)
  (ensures S.(equal (create 1 (index b i)) (slice b i (i+1)))) =
  ()

let lemma_append_assoc (#a:eqtype) (u v w:S.seq a) : Lemma
  (S.equal S.(u @| v @| w) S.((u @| v) @| w)) =
  ()

let compose_split (#a:eqtype) (b:S.seq a) (i j:nat) : Lemma
  (requires i+j <= S.length b)
  (ensures snd (S.split (snd (S.split b i)) j) = snd (S.split b (i+j))) =
  ()

let lemma_compose_slice (#a:eqtype) (b:S.seq a) (i j k l:nat) : Lemma
  (requires i <= j /\ j <= S.length b /\ k <= l /\ k <= j - i /\ l <= j - i)
  (ensures S.slice (S.slice b i j) k l = S.slice b (i+k) (i+l)) =
  ()

let add_offset (#a:eqtype) (b:S.seq a) (i:nat) (p1 p2:S.seq a) : Lemma
  (requires i <= S.length b /\ S.slice b i (S.length b) = S.(p1@|p2))
  (ensures (
    assert (S.length S.(p1@|p2) = S.length p1+S.length p2);
    S.slice b (i+S.length p1) (S.length b) = p2)) =
  assert (S.length S.(p1@|p2) = S.length p1+S.length p2);
  append_slices2 p1 p2;
  compose_split b i (S.length p1)

let slice_trans (#a:eqtype) (b:S.seq a) (i j k:nat) : Lemma
  (requires i <= j /\ j <= k /\ k <= S.length b)
  (ensures S.slice b i k = S.(slice b i j @| slice b j k)) =
  S.lemma_split (S.slice b i k) (j-i)

let extensionality_slice (#a:eqtype) (b1 b2:S.seq a) (i j:nat) : Lemma
  (requires
    S.length b1 = S.length b2 /\
    i <= j /\ j <= S.length b1 /\
    (forall (k:nat{i<=k /\ k<j}). S.index b1 k = S.index b2 k))
  (ensures S.equal (S.slice b1 i j) (S.slice b2 i j)) =
  let index_slice_aux (b:S.seq a) (i j k:nat) : Lemma
    (requires i <= j /\ j <= S.length b /\ k < j - i)
    (ensures S.index (S.slice b i j) k = S.index b (i+k)) =
    () in
  let index_slice (b:S.seq a{j <= S.length b}) (k:nat{k < j - i}) : Lemma
    (S.index (S.slice b i j) k = S.index b (i+k)) =
    index_slice_aux b i j k in

  FStar.Classical.forall_intro (index_slice b1);
  FStar.Classical.forall_intro (index_slice b2)


// application of a byte operation at a subposition
let rec pointwise_op (#a:eqtype) (f:a->a->a) (b1 b2:S.seq a) (pos:nat) : Pure (S.seq a)
  (requires S.length b2 + pos <= S.length b1)
  (ensures fun b -> S.length b == S.length b1)
  (decreases (S.length b2)) =
  if b2 = S.empty then b1
  else
    let _ = S.lemma_empty b2 in
    let x = f (S.index b1 pos) (S.index b2 0) in
    pointwise_op f (S.upd b1 pos x) (S.slice b2 1 (S.length b2)) (pos + 1)

let pointwise_op_empty
  (#a:eqtype) (f:a->a->a) (b1 b2:S.seq a) (pos:nat)
: Lemma
  (requires (S.length b2 == 0 /\ pos <= S.length b1))
  (ensures (pointwise_op f b1 b2 pos == b1))
= assert (b2 `S.equal` S.empty)

// three lemmas to recover indexes after application of bitwise_op
let rec pointwise_index1 (#a:eqtype) (f:a->a->a) (b1 b2:S.seq a) (i pos:nat) : Lemma
  (requires (S.length b2 + pos <= S.length b1 /\ i < pos))
  (ensures (S.index (pointwise_op f b1 b2 pos) i = S.index b1 i))
  (decreases (S.length b2)) =
  if b2 = S.empty then ()
  else begin
    S.lemma_empty b2;
    let x = f (S.index b1 pos) (S.index b2 0) in
    assert (pointwise_op f b1 b2 pos = pointwise_op f (S.upd b1 pos x) (S.slice b2 1 (S.length b2)) (pos + 1));
    S.lemma_index_upd2 b1 pos x i;
    assert (S.index (S.upd b1 pos x) i = S.index b1 i);
    pointwise_index1 f (S.upd b1 pos x) (S.slice b2 1 (S.length b2)) i (pos + 1)
  end


let rec pointwise_index2 (#a:eqtype) (f:a->a->a) (b1 b2:S.seq a) (i pos:nat) : Lemma
  (requires (S.length b2 + pos <= S.length b1 /\ pos <= i /\ i < S.length b2 + pos))
  (ensures (S.index (pointwise_op f b1 b2 pos) i = f (S.index b1 i) (S.index b2 (i-pos))))
  (decreases (S.length b2)) =
  if S.empty = b2 then ()
  else begin
    let x = f (S.index b1 pos) (S.index b2 0) in
    assert (pointwise_op f b1 b2 pos = pointwise_op f (S.upd b1 pos x) (S.slice b2 1 (S.length b2)) (pos+1));
    if i = pos then begin
      pointwise_index1 f (S.upd b1 pos x) (S.slice b2 1 (S.length b2)) pos (pos+1);
      S.lemma_index_upd1 b1 pos x
    end
    else
      pointwise_index2 f (S.upd b1 pos x) (S.slice b2 1 (S.length b2)) i (pos+1)
  end


let rec pointwise_index3 (#a:eqtype) (f:a->a->a) (b1 b2:S.seq a) (i pos:nat) : Lemma
  (requires (S.length b2 + pos <= i /\ i < S.length b1))
  (ensures (S.index (pointwise_op f b1 b2 pos) i = S.index b1 i))
  (decreases (S.length b2)) =
  if S.empty = b2 then ()
  else begin
    S.lemma_empty b2;
    let x = f (S.index b1 pos) (S.index b2 0) in
    pointwise_index3 f (S.upd b1 pos x) (S.slice b2 1 (S.length b2)) i (pos+1)
  end



let pointwise_op_suff (#a:eqtype) (f:a->a->a) (a1 a2 b:S.seq a) (pos:nat) : Lemma
  (requires pos >= S.length a1 /\ S.length b + pos <= S.length a1 + S.length a2)
  (ensures
    S.equal
      (pointwise_op f S.(a1 @| a2) b pos)
      S.(a1 @| pointwise_op f a2 b (pos - S.length a1))) =
  let b1 = pointwise_op f S.(a1 @| a2) b pos in
  let b2 = S.(a1 @| pointwise_op f a2 b (pos - S.length a1)) in
  let step i : Lemma (S.index b1 i = S.index b2 i) =
    if i < S.length a1 then pointwise_index1 f S.(a1 @| a2) b i pos
    else begin
      if i < pos then begin
        pointwise_index1 f S.(a1 @| a2) b i pos;
        pointwise_index1 f a2 b (i-S.length a1) (pos-S.length a1)
      end else if i < S.length b + pos then begin
        pointwise_index2 f S.(a1 @| a2) b i pos;
        pointwise_index2 f a2 b (i-S.length a1) (pos-S.length a1)
      end else begin
        pointwise_index3 f S.(a1 @| a2) b i pos;
        pointwise_index3 f a2 b (i-S.length a1) (pos-S.length a1)
      end
    end in

  FStar.Classical.forall_intro step


let pointwise_op_pref (#a:eqtype) (f:a->a->a) (a1 a2 b:S.seq a) (pos:nat) : Lemma
  (requires S.length b + pos <= S.length a1)
  (ensures
    S.equal
      (pointwise_op f S.(a1 @| a2) b pos)
      S.(pointwise_op f a1 b pos @| a2)) =
  let b1 = pointwise_op f S.(a1 @| a2) b pos in
  let b2 = S.(pointwise_op f a1 b pos @| a2) in
  let step i : Lemma (S.index b1 i = S.index b2 i) =
    if i < pos then begin
      pointwise_index1 f S.(a1 @| a2) b i pos;
      pointwise_index1 f a1 b i pos
    end else if i < S.length b + pos then begin
      pointwise_index2 f S.(a1 @| a2) b i pos;
      pointwise_index2 f a1 b i pos
    end else begin
      pointwise_index3 f S.(a1 @| a2) b i pos;
      if i < S.length a1 then pointwise_index3 f a1 b i pos
      else ()
    end in

  FStar.Classical.forall_intro step


let pointwise_op_dec (#a:eqtype) (f:a->a->a) (a1 a2 b:S.seq a) (pos:nat) : Lemma
  (requires
    pos <= S.length a1 /\
    S.length a1 <= S.length b + pos /\
    S.length b + pos <= S.length a1 + S.length a2)
  (ensures (
    let open S in
    let (b1,b2) = S.split b (length a1 - pos) in
    equal
      (pointwise_op f (a1 @| a2) b pos)
      (pointwise_op f a1 b1 pos @| pointwise_op f a2 b2 0))) =
  let open S in
  let (b1,b2) = S.split b (length a1 - pos) in
  let p = pointwise_op f (a1 @| a2) b pos in
  let q = pointwise_op f a1 b1 pos @| pointwise_op f a2 b2 0 in
  let step i : Lemma (S.index p i = S.index q i) =
    if i < pos then begin
      pointwise_index1 f (a1 @| a2) b i pos;
      pointwise_index1 f a1 b1 i pos
    end else if i < length a1 then begin
      pointwise_index2 f (a1 @| a2) b i pos;
      pointwise_index2 f a1 b1 i pos
    end else if i < length b + pos then begin
      pointwise_index2 f (a1 @| a2) b i pos;
      pointwise_index2 f a2 b2 (i-length a1) 0
    end else begin
      pointwise_index3 f (a1 @| a2) b i pos;
      pointwise_index3 f a2 b2 (i-length a1) 0
    end in

  FStar.Classical.forall_intro step

#push-options "--z3rlimit 32"

let pointwise_op_append_r
  (#t: eqtype)
  (f: t -> t -> t)
  (a b1 b2: S.seq t)
  (pos: nat)
: Lemma
  (requires (
    pos + S.length b1 + S.length b2 <= S.length a
  ))
  (ensures (
    pointwise_op f a (S.append b1 b2) pos == (
      pointwise_op f (S.slice a 0 (pos + S.length b1)) b1 pos `S.append`
      pointwise_op f (S.slice a (pos + S.length b1) (S.length a)) b2 0
  )))
= S.lemma_split a (pos + S.length b1);
  pointwise_op_dec f (S.slice a 0 (pos + S.length b1)) (S.slice a (pos + S.length b1) (S.length a)) (S.append b1 b2) pos;
  let (b1', b2') = S.split (b1 `S.append` b2) (S.length b1) in
  assert (b1 `S.equal` b1' /\ b2 `S.equal` b2')

#pop-options

let pointwise_op_split
  (#t: eqtype)
  (f: t -> t -> t)
  (a b: S.seq t)
  (pos: nat)
  (pos_split: nat)
: Lemma
  (requires (
    pos <= pos_split /\
    pos_split <= pos + S.length b /\
    pos + S.length b <= S.length a
  ))
  (ensures (
    let (a1, a2) = S.split a pos_split in
    let (b1, b2) = S.split b (pos_split - pos) in
    pointwise_op f a b pos == pointwise_op f a1 b1 pos `S.append` pointwise_op f a2 b2 0
  ))
= S.lemma_split a pos_split;
  pointwise_op_dec f (S.slice a 0 pos_split) (S.slice a pos_split (S.length a)) b pos

let pointwise_op_slice_other
  (#a:eqtype) (f:a->a->a) (b1 b2:S.seq a) (pos:nat)
  (from to: nat)
: Lemma
  (requires (
    S.length b2 + pos <= S.length b1 /\
    from <= to /\
    to <= S.length b1 /\
    (to <= pos \/ pos + S.length b2 <= from)
  ))
  (ensures (
    S.slice (pointwise_op f b1 b2 pos) from to `S.equal` S.slice b1 from to
  ))
= let phi
    (i: nat { from <= i /\ i < to })
  : Lemma
    (S.index (pointwise_op f b1 b2 pos) i == S.index b1 i)
  = if to <= pos
    then pointwise_index1 f b1 b2 i pos
    else pointwise_index3 f b1 b2 i pos
  in
  Classical.forall_intro phi


// application: byte-wise xor
let xor_inplace (b1 b2:bytes) (pos:nat)
  : Pure bytes
  (requires S.length b2 + pos <= S.length b1)
  (ensures fun b -> S.length b == S.length b1)
  (decreases (S.length b2)) =
  pointwise_op U8.logxor b1 b2 pos


// proof of involution of the operator (uses extensionality for the
// byte-wise variant)
let xor_involutive (b1 b2:byte) : Lemma
  (requires True)
  (ensures (b1 `U8.logxor` b2) `U8.logxor` b2 = b1) =
  FStar.UInt.logxor_associative (U8.v b1) (U8.v b2) (U8.v b2);
  FStar.UInt.logxor_self (U8.v b2);
  FStar.UInt.logxor_commutative (FStar.UInt.zero 8) (U8.v b1);
  FStar.UInt.logxor_lemma_1 (U8.v b1)


let rec xor_inplace_involutive (b1 b2:bytes) (pos:nat) : Lemma
  (requires S.length b2 + pos <= S.length b1)
  (ensures S.equal (xor_inplace (xor_inplace b1 b2 pos) b2 pos) b1)
  (decreases (S.length b2)) =
  let xor = xor_inplace (xor_inplace b1 b2 pos) b2 pos in
  let step (i:nat{i < S.length b1}) : Lemma (S.index xor i = S.index b1 i) =
    if i < pos then begin
      pointwise_index1 U8.logxor b1 b2 i pos;
      pointwise_index1 U8.logxor (xor_inplace b1 b2 pos) b2 i pos
    end else if i >= pos+S.length b2 then begin
      pointwise_index3 U8.logxor b1 b2 i pos;
      pointwise_index3 U8.logxor (xor_inplace b1 b2 pos) b2 i pos
    end else begin
      pointwise_index2 U8.logxor b1 b2 i pos;
      pointwise_index2 U8.logxor (xor_inplace b1 b2 pos) b2 i pos;
      xor_involutive  (S.index b1 i) (S.index b2 (i-pos))
    end in

  FStar.Classical.forall_intro step


let rec xor_inplace_commutative (b b1 b2:bytes) (pos1 pos2:nat) : Lemma
  (requires
    S.length b1 + pos1 <= S.length b /\
    S.length b2 + pos2 <= S.length b)
  (ensures S.equal
    (xor_inplace (xor_inplace b b1 pos1) b2 pos2)
    (xor_inplace (xor_inplace b b2 pos2) b1 pos1)) =
  let xor1 = xor_inplace (xor_inplace b b1 pos1) b2 pos2 in
  let xor2 = xor_inplace (xor_inplace b b2 pos2) b1 pos1 in
  let step (i:nat{i < S.length b}) : Lemma (S.index xor1 i = S.index xor2 i) =
    if i < pos1 then begin
      pointwise_index1 U8.logxor b b1 i pos1;
      pointwise_index1 U8.logxor (xor_inplace b b2 pos2) b1 i pos1;
      if i < pos2 then begin
        pointwise_index1 U8.logxor b b2 i pos2;
        pointwise_index1 U8.logxor (xor_inplace b b1 pos1) b2 i pos2
      end else if i >= pos2 + S.length b2 then begin
        pointwise_index3 U8.logxor b b2 i pos2;
        pointwise_index3 U8.logxor (xor_inplace b b1 pos1) b2 i pos2
      end else begin
        pointwise_index2 U8.logxor b b2 i pos2;
        pointwise_index2 U8.logxor (xor_inplace b b1 pos1) b2 i pos2
      end
    end else if i >= pos1 + S.length b1 then begin
      pointwise_index3 U8.logxor b b1 i pos1;
      pointwise_index3 U8.logxor (xor_inplace b b2 pos2) b1 i pos1;
      if i < pos2 then begin
        pointwise_index1 U8.logxor b b2 i pos2;
        pointwise_index1 U8.logxor (xor_inplace b b1 pos1) b2 i pos2
      end else if i >= pos2 + S.length b2 then begin
        pointwise_index3 U8.logxor b b2 i pos2;
        pointwise_index3 U8.logxor (xor_inplace b b1 pos1) b2 i pos2
      end else begin
        pointwise_index2 U8.logxor b b2 i pos2;
        pointwise_index2 U8.logxor (xor_inplace b b1 pos1) b2 i pos2
      end
    end else begin
      pointwise_index2 U8.logxor b b1 i pos1;
      pointwise_index2 U8.logxor (xor_inplace b b2 pos2) b1 i pos1;
      if i < pos2 then begin
        pointwise_index1 U8.logxor b b2 i pos2;
        pointwise_index1 U8.logxor (xor_inplace b b1 pos1) b2 i pos2
      end else if i >= pos2 + S.length b2 then begin
        pointwise_index3 U8.logxor b b2 i pos2;
        pointwise_index3 U8.logxor (xor_inplace b b1 pos1) b2 i pos2
      end else begin
        let ind = U8.v (S.index b i) in
        let ind1 = U8.v (S.index b1 (i-pos1)) in
        let ind2 = U8.v (S.index b2 (i-pos2)) in
        FStar.UInt.logxor_associative #8 ind ind1 ind2;
        FStar.UInt.logxor_associative #8 ind ind2 ind1;
        FStar.UInt.logxor_commutative #8 ind1 ind2;
        pointwise_index2 U8.logxor b b2 i pos2;
        pointwise_index2 U8.logxor (xor_inplace b b1 pos1) b2 i pos2
      end
    end in

  FStar.Classical.forall_intro step

let xor_inplace_zero
  (a b: bytes)
  (phi: (i: nat {i < S.length b}) -> Lemma (S.index b i == 0uy))
  (pos: nat)
: Lemma
  (requires (pos + S.length b <= S.length a))
  (ensures (xor_inplace a b pos `S.equal` a))
= let psi
    (i: nat {i < S.length a})
  : Lemma
    (S.index (xor_inplace a b pos) i == S.index a i)
  = if i < pos
    then pointwise_index1 U8.logxor a b i pos
    else if i >= pos + S.length b
    then pointwise_index3 U8.logxor a b i pos
    else begin
      pointwise_index2 U8.logxor a b i pos;
      phi (i - pos);
      FStar.UInt.logxor_lemma_1 (U8.v (S.index a i))
    end
  in
  Classical.forall_intro psi

let and_inplace (b1 b2:bytes) (pos:nat)
  : Pure bytes
  (requires S.length b2 + pos <= S.length b1)
  (ensures fun b -> S.length b == S.length b1)
  (decreases (S.length b2)) =
  pointwise_op U8.logand b1 b2 pos

let and_inplace_zero
  (a b: bytes)
  (phi: (i: nat {i < S.length b}) -> Lemma (S.index b i == 0uy))
  (i: nat {i < S.length a})
: Lemma
  (requires (S.length b == S.length a))
  (ensures (S.index (and_inplace a b 0) i == 0uy))
= pointwise_index2 U8.logand a b i 0;
  phi i;
  FStar.UInt.logand_lemma_1 (U8.v (S.index a i))

let rec bitwise_op (f:bool->bool->bool) (l1 l2:list bool) : Pure (list bool)
  (requires List.Tot.length l1 = List.Tot.length l2)
  (ensures fun l -> List.Tot.length l = List.Tot.length l1) =
  match l1,l2 with
  | [],[] -> []
  | x1::t1,x2::t2 -> f x1 x2 :: bitwise_op f t1 t2


let rec lemma_bitwise_op_index (f:bool->bool->bool) (l1 l2:list bool) (n:nat) : Lemma
  (requires List.Tot.length l1 = List.Tot.length l2 /\ n < List.Tot.length l1)
  (ensures List.Tot.index (bitwise_op f l1 l2) n = f (List.Tot.index l1 n) (List.Tot.index l2 n)) =
  match l1,l2 with
  | [],[] -> ()
  | x1::t1,x2::t2 ->
    if n = 0 then ()
    else lemma_bitwise_op_index f t1 t2 (n-1)

let rec list_to_seq (#a:eqtype) (l:list a) : (s:(S.seq a){S.length s = List.Tot.length l /\ (forall i. S.index s i = List.Tot.index l i)}) =
  match l with
  | [] -> S.empty
  | h :: t -> S.(create 1 h @| list_to_seq t)

let rec rev_seq (#a:eqtype) (s:S.seq a) : Pure (S.seq a)
  (requires True)
  (ensures fun s' -> S.length s = S.length s')
  (decreases (S.length s)) =
  if s = S.empty then S.empty
  else
    let _ = S.lemma_empty s in
    S.(rev_seq S.(slice s 1 (length s)) @| create 1 (index s 0))


let rec lemma_rev_seq (#a:eqtype) (s:S.seq a) (i:nat) : Lemma
  (requires i < S.length s)
  (ensures
    S.length (rev_seq s) = S.length s /\
    S.index s i = S.index (rev_seq s) (S.length s-1-i))
  (decreases (i))=
  if s = S.empty then ()
  else if i = 0 then ()
  else lemma_rev_seq (S.slice s 1 (S.length s)) (i-1)

#restart-solver

let lemma_arithmetic1 (a b c d e:int) : Lemma
  ((a+b+c+d)+(e-d) = (a+c+e)+b) =
  ()

let lemma_arithmetic2 (a b c d:int) : Lemma
  (a+(b-c)+d = a + ((b+d)-c)) =
  ()

let lemma_arithmetic3 (a b c:int) : Lemma
  ((a+b)-c = (a-c)+b) =
  ()


let lemma_propagate_mul_mod (a b:nat) : Lemma
  (requires b > 0)
  (ensures (
    let open FStar.Mul in
    (2*a) % (2*b) = 2 * (a % b))) =
  let open FStar.Math.Lemmas in
  let open FStar.Mul in
  lemma_div_mod a b;
  lemma_div_mod (2*a) b;
  let (p,r) = ((a/b)*(2*b), 2*(a%b)) in
  assert (2*a = p + r);
  modulo_distributivity p r (2*b);
  multiple_modulo_lemma (a/b) (2*b);
  modulo_range_lemma a b;
  small_mod r (2*b)

#push-options "--max_fuel 2 --initial_fuel 2 --max_ifuel 1 --initial_ifuel 1 --z3rlimit 256" // strange that F* has so much trouble completing this induction
let recompose_pow2_assoc (n:pos) (a:nat) : Lemma
  (let open FStar.Mul in 2 * (pow2 (n-1) * a) = pow2 n * a) =
  ()


let rec lemma_propagate_pow_mod (a b n:nat) : Lemma
  (requires b > 0)
  (ensures (
    let open FStar.Mul in
    (pow2 n * a) % (pow2 n * b) = pow2 n * (a % b))) =
  let open FStar.Mul in
  let open FStar.Math.Lemmas in
  if n = 0 then ()
  else begin
    let res = (pow2 n * a) % (pow2 n * b) in
    lemma_propagate_mul_mod (pow2 (n-1) * a) (pow2 (n-1) * b);
    assert (res = 2 * ((pow2 (n-1) * a) % (pow2 (n-1) * b)));
    lemma_propagate_pow_mod a b (n-1);
    assert (res = 2 * (pow2 (n-1) * (a%b)));
    recompose_pow2_assoc n (a%b)
  end
#pop-options


#restart-solver
let lemma_modulo_shift_byte (a:nat) (i:pos) : Lemma
  (let open FStar.Mul in
  (pow2 8 * a) % (pow2 (8*i)) = pow2 8 * (a % pow2 (8*(i-1)))) =
  let sub = 8 `op_Multiply` (i-1) in
  FStar.Math.Lemmas.pow2_plus 8 sub;
  lemma_propagate_pow_mod a (pow2 sub) 8

let rec reveal_be_to_n_slice (b:bytes) (i j:nat) : Lemma
  (requires i < j /\ j <= S.length b)
  (ensures (
    let open FStar.Mul in
    let open FStar.Endianness in
    let h = U8.v (S.index b (j-1)) in
    be_to_n (S.slice b i j) = h + pow2 8 * be_to_n (S.slice b i (j - 1)))) =
  FStar.Endianness.reveal_be_to_n (S.slice b i j)

let rec lemma_correctness_slice_be_to_n (b:bytes) (i:nat) : Lemma
  (requires i <= S.length b)
  (ensures (
    let open FStar.Endianness in
    let open FStar.Mul in
    be_to_n b % pow2 (8 * i) =
    be_to_n (S.slice b (S.length b - i) (S.length b))))
  (decreases i) =
  let open FStar.Endianness in
  let open FStar.Math.Lemmas in
  let open FStar.Mul in
  if i = 0 then reveal_be_to_n S.empty
  else begin
    reveal_be_to_n b;
    let h = U8.v (S.index b (S.length b - 1)) in
    let l = S.slice b 0 (S.length b - 1) in
    let pow = pow2 (8*i) in
    //assert (be_to_n b = h + pow2 8 * be_to_n l);
    modulo_distributivity h (pow2 8 * be_to_n l) pow;
    pow2_le_compat (8*i) 8;
    small_mod h pow;
    //assert (be_to_n b % pow = (h + (pow2 8 * be_to_n l)%pow) % pow);
    lemma_modulo_shift_byte (be_to_n l) i;
    lemma_correctness_slice_be_to_n l (i-1);
    //assert (be_to_n b % pow = (h + pow2 8 * be_to_n (S.slice b (S.length b - i) (S.length b - 1))) % pow);
    reveal_be_to_n_slice b (S.length b - i) (S.length b);
    //assert (be_to_n b % pow = be_to_n (S.slice b (S.length b - i) (S.length b)) % pow);
    lemma_be_to_n_is_bounded (S.slice b (S.length b - i) (S.length b));
    FStar.Math.Lemmas.small_mod (be_to_n (S.slice b (S.length b - i) (S.length b))) pow
  end

open FStar.Mul

let rec index_be_to_n
  (b: bytes)
  (i: nat)
: Lemma
  (requires (
    i < S.length b
  ))
  (ensures (
    U8.v (FStar.Seq.index b i) == (FStar.Endianness.be_to_n b / pow2 (8 * (S.length b - 1 - i))) % pow2 8
  ))
  (decreases (S.length b))
= let open FStar.Endianness in
  reveal_be_to_n b;
  if i = S.length b - 1
  then ()
  else begin
    let l = S.length b in
    let l' = l - 1 in
    let b' = S.slice b 0 l' in
    index_be_to_n b' i;
    assert (FStar.Seq.index b i == FStar.Seq.index b' i);
    let open FStar.Math.Lemmas in
    let x = be_to_n b in
    let x' = be_to_n b' in
    assert (U8.v (FStar.Seq.index b i) == x' / pow2 (8 * (l' - 1 - i)) % pow2 8);
    let y = (U8.v (S.last b) + pow2 8 * x') / pow2 (8 * (l - 1 - i)) % pow2 8 in
    pow2_plus 8 (8 * (l' - 1 - i));
    division_multiplication_lemma (U8.v (S.last b) + pow2 8 * x') (pow2 8) (pow2 (8 * (l' - 1 - i)));
    assert (pow2 8 * x' == x' * pow2 8);
    division_addition_lemma (U8.v (S.last b)) (pow2 8) x';
    small_division_lemma_1 (U8.v (S.last b)) (pow2 8);
    assert (y == x' / pow2 (8 * (l' - 1 - i)) % pow2 8)
  end

let index_n_to_be
  (len: nat)
  (n: nat)
  (i: nat)
: Lemma
  (requires (
    i < len /\
    n < pow2 (8 * len)
  ))
  (ensures (
    U8.v (FStar.Seq.index (FStar.Endianness.n_to_be len n) i)) == (n / pow2 (8 * (len - 1 - i)) % pow2 8
  ))
= index_be_to_n (FStar.Endianness.n_to_be len n) i

let index_n_to_be_zero_left
  (len: nat)
  (n: nat)
  (j: nat)
  (i: nat)
: Lemma
  (requires (
    i < j /\
    j <= len /\
    n < pow2 (8 * (len - j))
  ))
  (ensures (
    pow2 (8 * (len - j)) <= pow2 (8 * len) /\
    U8.v (FStar.Seq.index (FStar.Endianness.n_to_be len n) i) == 0
  ))
= let open FStar.Math.Lemmas in
  pow2_le_compat (8 * len) (8 * (len - j));
  pow2_le_compat (8 * (len - 1 - i)) (8 * (len - j));
  small_division_lemma_1 n (pow2 (8 * (len - 1 - i)));
  index_n_to_be len n i

let index_n_to_be_zero_right
  (len: nat)
  (n: nat)
  (i: nat)
: Lemma
  (requires (
    i < len /\
    n < pow2 (8 * len) /\
    n % pow2 (8 * (len - i)) == 0
  ))
  (ensures (
    U8.v (FStar.Seq.index (FStar.Endianness.n_to_be len n) i) == 0
  ))
= index_n_to_be len n i;
  let open FStar.Math.Lemmas in
  modulo_division_lemma n (pow2 (8 * (len - 1 - i))) (pow2 8);
  pow2_plus (8 * (len - 1 - i)) 8
