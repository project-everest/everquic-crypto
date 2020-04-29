module QUIC.Impl.PacketNumber
open QUIC.Spec.PacketNumber

module U64 = FStar.UInt64
module U32 = FStar.UInt32
module HST = FStar.HyperStack.ST
module B = LowStar.Buffer
module HS = FStar.HyperStack
module Secret = QUIC.Secret.Int
module SecretBuffer = QUIC.Secret.Buffer
module LP = LowParse.Spec
module Seq = QUIC.Secret.Seq

friend QUIC.Spec.PacketNumber
module Spec = QUIC.Spec.PacketNumber

module Cast = FStar.Int.Cast
module U32 = FStar.UInt32
module U16 = FStar.UInt16
module U8 = FStar.UInt8

module E = LowParse.Endianness.BitFields

let be_to_n_4_eq
  (b: Seq.lseq U8.t 4)
: Lemma
  (E.be_to_n b ==
    U8.v (Seq.index b 3) + (256 `Prims.op_Multiply` (
    U8.v (Seq.index b 2) + (256 `Prims.op_Multiply` (
    U8.v (Seq.index b 1) + (256 `Prims.op_Multiply` (
    U8.v (Seq.index b 0)
  )))))))
= assert_norm (pow2 8 == 256);
  E.reveal_be_to_n b;
  let b3 = Seq.slice b 0 3 in
  E.reveal_be_to_n b3;
  let b2 = Seq.slice b3 0 2 in
  E.reveal_be_to_n b2;
  let b1 = Seq.slice b2 0 1 in
  E.reveal_be_to_n b1;
  E.reveal_be_to_n (Seq.slice b1 0 0)

#push-options "--z3rlimit 32"

let read_u32
  (b: B.buffer Secret.uint8)
: HST.Stack Secret.uint32
  (requires (fun h ->
    B.live h b /\
    4 <= B.length b
  ))
  (ensures (fun h res h' ->
    B.modifies B.loc_none h h' /\
    begin match LP.parse LP.parse_u32 (Seq.seq_reveal (B.as_seq h b)) with
    | Some (v, _) -> Secret.v res == U32.v v
    | None -> False
    end
  ))
= 
  let h = HST.get () in
  LP.parse_u32_spec (Seq.seq_reveal (B.as_seq h b));
  be_to_n_4_eq (Seq.slice (Seq.seq_reveal (B.as_seq h b)) 0 4);
  let b3 = B.index b 3ul in
  let b2 = B.index b 2ul in
  let b1 = B.index b 1ul in
  let b0 = B.index b 0ul in
  Secret.to_u32 b3 `Secret.add` (Secret.to_u32 256ul `Secret.mul` (
  Secret.to_u32 b2 `Secret.add` (Secret.to_u32 256ul `Secret.mul` (  
  Secret.to_u32 b1 `Secret.add` (Secret.to_u32 256ul `Secret.mul` (  
  Secret.to_u32 b0
  ))))))

#pop-options

module BF = LowParse.BitFields

[@"opaque_to_smt"]
let secrets_are_equal_32_2
  (x: Secret.uint32 { Secret.v x < pow2 2 })
  (y: Secret.uint32 { Secret.v y < pow2 2 })
: Tot (z: Secret.uint32 {
    Secret.v z == (if Secret.v x = Secret.v y then 1 else 0)
  })
= Secret.norm (Secret.secrets_are_equal 2 x y)

#push-options "--z3rlimit 16"

inline_for_extraction
noextract
let read_bounded_integer
  (pn_len: packet_number_length_t)
  (b: B.buffer Secret.uint8)
: HST.Stack Secret.uint32
  (requires (fun h ->
    B.live h b /\
    4 <= B.length b
  ))
  (ensures (fun h res h' ->
    B.modifies B.loc_none h h' /\
    begin match LP.parse (LP.parse_bounded_integer (Secret.v pn_len)) (Seq.seq_reveal (B.as_seq h b)) with
    | Some (v, _) -> Secret.v res == U32.v v
    | None -> False
    end
  ))
=
  let h = HST.get () in
  LP.parse_bounded_integer_spec (Secret.v pn_len) (Seq.seq_reveal (B.as_seq h b));
  LP.parse_u32_spec (Seq.seq_reveal (B.as_seq h b));
  E.bitfield_be_to_n_slice (Seq.slice (Seq.seq_reveal (B.as_seq h b)) 0 4) 0 (Secret.v pn_len);
  let x = read_u32 b in
  BF.get_bitfield_full #32 (Secret.v x);
  let pn_len_1 = Secret.to_u32 (pn_len `Secret.sub` Secret.to_u32 1ul) in
  ((pn_len_1 `secrets_are_equal_32_2` Secret.to_u32 0ul) `Secret.mul` Secret.get_bitfield x 24ul 32ul) `Secret.add`
  ((pn_len_1 `secrets_are_equal_32_2` Secret.to_u32 1ul) `Secret.mul` Secret.get_bitfield x 16ul 32ul) `Secret.add`
  ((pn_len_1 `secrets_are_equal_32_2` Secret.to_u32 2ul) `Secret.mul`
Secret.get_bitfield x 8ul 32ul) `Secret.add`
  ((pn_len_1 `secrets_are_equal_32_2` Secret.to_u32 3ul) `Secret.mul` x)

#pop-options

[@"opaque_to_smt"]
let secret_is_le_64
  (x: Secret.uint64)
  (y: Secret.uint64)
: Tot (z: Secret.uint64 { Secret.v z == (if Secret.v x <= Secret.v y then 1 else 0) })
= Secret.norm (Secret.secret_is_le 64 x y)

[@"opaque_to_smt"]
let secret_is_lt_64
  (x: Secret.uint64)
  (y: Secret.uint64)
: Tot (z: Secret.uint64 { Secret.v z == (if Secret.v x < Secret.v y then 1 else 0) })
= Secret.norm (Secret.secret_is_lt 64 x y)

module U = FStar.UInt

[@"opaque_to_smt"]
let secrets_are_equal_64_2
  (x: Secret.uint64 { Secret.v x < pow2 2 })
  (y: Secret.uint64 { Secret.v y < pow2 2 })
: Tot (z: Secret.uint64 {
    Secret.v z == (if Secret.v x = Secret.v y then 1 else 0)
  })
= Secret.norm (Secret.secrets_are_equal 2 x y)

#push-options "--z3rlimit 16"

[@"opaque_to_smt"]
let bound_npn
  (pn_len: packet_number_length_t)
: Tot (x: packet_number_t { Secret.v x == bound_npn' (Secret.v pn_len - 1) })
= let pn_len_1 = Secret.to_u64 (pn_len `Secret.sub` Secret.to_u32 1ul) in
  ((pn_len_1 `secrets_are_equal_64_2` Secret.to_u64 0ul) `Secret.mul` Secret.to_u64 256uL) `Secret.add`
  ((pn_len_1 `secrets_are_equal_64_2` Secret.to_u64 1ul) `Secret.mul` Secret.to_u64 65536uL) `Secret.add`
  ((pn_len_1 `secrets_are_equal_64_2` Secret.to_u64 2ul) `Secret.mul` Secret.to_u64 16777216uL) `Secret.add`
  ((pn_len_1 `secrets_are_equal_64_2` Secret.to_u64 3ul) `Secret.mul` Secret.to_u64 4294967296uL)

#pop-options

inline_for_extraction
let secret_bounded_integer (i: LP.integer_size) = (x: Secret.uint32 { LP.bounded_integer_prop i (U32.uint_to_t (Secret.v x)) })

#push-options "--max_fuel 2 --initial_fuel 2 --max_ifuel 1 --initial_ifuel 1 --z3rlimit 2048 --query_stats"

module U62 = QUIC.UInt62
module Lemmas = QUIC.Spec.PacketNumber.Lemmas

#restart-solver

[@"opaque_to_smt"]
inline_for_extraction
let expand_pn_aux
  (pn_len: packet_number_length_t)
  (last: last_packet_number_t)
  (npn: secret_bounded_integer (Secret.v pn_len))
: Tot (pn: Secret.uint64 { Secret.v pn == expand_pn' (Secret.v pn_len - 1) (Secret.v last) (Secret.v npn) })
= let open FStar.Mul in
  let open FStar.Math.Lemmas in
  let expected : U62.secret = last `Secret.add` Secret.to_u64 1uL in
  let bound = bound_npn pn_len in
  let bound_2 = bound `Secret.shift_right` 1ul in
  FStar.UInt.shift_right_value_lemma #64 (Secret.v bound) 1;
  assert (Secret.v bound_2 == Secret.v bound / 2);
  let candidate = Lemmas.replace_modulo expected (8 `Prims.op_Multiply` Secret.v pn_len) (bound `Secret.sub` Secret.to_u64 1uL) (Secret.to_u64 npn) in
  let bound_2_le_expected = bound_2 `secret_is_le_64` expected in
  let cond_1 =
    bound_2_le_expected `Secret.logand_one_bit`
    (candidate `secret_is_le_64` ((bound_2_le_expected `Secret.mul` expected) `Secret.sub` (bound_2_le_expected `Secret.mul` bound_2))) `Secret.logand_one_bit`
    (candidate `secret_is_lt_64` (Secret.to_u64 U62.bound `Secret.sub` bound))
  in
  assert (Secret.v cond_1 == (
    if
      Secret.v bound_2 <= Secret.v expected &&
      Secret.v candidate <= (Secret.v expected - Secret.v bound_2) &&
      Secret.v candidate < U62.v U62.bound - Secret.v bound
    then 1
    else 0
  ));
  let cond_2 =
    Secret.lognot_one_bit cond_1 `Secret.logand_one_bit`
    ((expected `Secret.add` bound_2) `secret_is_lt_64` candidate) `Secret.logand_one_bit`
    (bound `secret_is_le_64` candidate)
  in
  assert (Secret.v cond_2 == (
    if
      Secret.v cond_1 = 0 &&
      Secret.v expected + Secret.v bound_2 < Secret.v candidate &&
      Secret.v bound <= Secret.v candidate
    then 1
    else 0
  ));
  (candidate `Secret.add` (cond_1 `Secret.mul` bound)) `Secret.sub` (cond_2 `Secret.mul` bound)

[@"opaque_to_smt"]
let expand_pn
  (pn_len: packet_number_length_t)
  (last: last_packet_number_t)
  (npn: secret_bounded_integer (Secret.v pn_len))
: Tot (pn: packet_number_t { pn == synth_packet_number last pn_len (U32.uint_to_t (Secret.v npn)) })
= expand_pn_aux pn_len last npn

#pop-options

let read_packet_number
  last pn_len b
= let h = HST.get () in
  LP.parse_synth_eq (LP.lift_parser (parse_reduced_pn pn_len)) (synth_packet_number last pn_len) (Seq.seq_reveal (B.as_seq h b));
  let npn = read_bounded_integer pn_len b in
  expand_pn pn_len last npn

#push-options "--z3rlimit 32"

#restart-solver

[@"opaque_to_smt"]
let reduce_pn
  (pn_len: packet_number_length_t)
  (pn: packet_number_t)
: Tot (b: secret_bounded_integer (Secret.v pn_len) { Secret.v b == reduce_pn' (Secret.v pn_len - 1) (Secret.v pn) })
= let mask = bound_npn pn_len `Secret.sub` Secret.to_u64 1uL in
  Secret.logand_spec pn mask;
  Lemmas.logand_mask #64 (Secret.v pn) (8 `Prims.op_Multiply` Secret.v pn_len);
  Secret.to_u32 (pn `Secret.logand` mask)

#pop-options

let serialize_u32_spec
  (x: U32.t)
: Lemma
  (LP.serialize LP.serialize_u32 x == E.n_to_be 4 (U32.v x))
= LP.parse_u32_spec (E.n_to_be 4 (U32.v x));
  LP.parse_injective LP.parse_u32 (LP.serialize LP.serialize_u32 x) (E.n_to_be 4 (U32.v x))

#push-options "--z3rlimit 16"

let write_u32
  (x: Secret.uint32)
  (b: B.buffer Secret.uint8)
: HST.Stack unit
  (requires (fun h ->
    B.live h b /\
    4 <= B.length b
  ))
  (ensures (fun h _ h' ->
    let b' = B.gsub b 0ul 4ul in
    B.modifies (B.loc_buffer b') h h' /\
    Seq.seq_reveal (B.as_seq h' b') `Seq.equal` LP.serialize (LP.serialize_u32) (U32.uint_to_t (Secret.v x))
  ))
= serialize_u32_spec (U32.uint_to_t (Secret.v x));
  E.index_n_to_be 4 (Secret.v x) 0;
  E.index_n_to_be 4 (Secret.v x) 1;
  E.index_n_to_be 4 (Secret.v x) 2;
  E.index_n_to_be 4 (Secret.v x) 3;
  let b' = B.sub b 0ul 4ul in
  B.upd b' 0ul (Secret.to_u8 (x `Secret.shift_right` 24ul));
  B.upd b' 1ul (Secret.to_u8 (x `Secret.shift_right` 16ul));
  B.upd b' 2ul (Secret.to_u8 (x `Secret.shift_right` 8ul));
  B.upd b' 3ul (Secret.to_u8 x)

#pop-options

#push-options "--z3rlimit 256"

#restart-solver

inline_for_extraction
[@"opaque_to_smt"]
let set_left_bitfield_arg
  (pn_len: packet_number_length_t)
  (pn_len' : U32.t { 1 <= U32.v pn_len' /\ U32.v pn_len' <= 4 } )
  (x: Secret.uint32 {
    Secret.v pn_len == U32.v pn_len' ==> LP.bounded_integer_prop (Secret.v pn_len) (U32.uint_to_t (Secret.v x))
  })
  (mask: Secret.uint32 { Secret.v mask == pow2 (8 `Prims.op_Multiply` (U32.v pn_len')) - 1 })
: Tot (y: secret_bounded_integer (U32.v pn_len') {
    Secret.v pn_len == U32.v pn_len' ==> Secret.v y == Secret.v x
  })
=
  let f () : Lemma
    (requires (Secret.v pn_len == U32.v pn_len'))
    (ensures (
      Secret.v pn_len == U32.v pn_len' /\
      Secret.v x % pow2 (8 `Prims.op_Multiply` U32.v pn_len' ) == Secret.v x
    ))
  = LP.bounded_integer_prop_equiv (Secret.v pn_len) (U32.uint_to_t (Secret.v x));
    FStar.Math.Lemmas.small_mod (Secret.v x) (pow2 (8 `Prims.op_Multiply` U32.v pn_len'))
  in
  let g () : Lemma
    (Secret.v pn_len == U32.v pn_len' ==>
      Secret.v x % pow2 (8 `Prims.op_Multiply` U32.v pn_len' ) == Secret.v x
    )
  = Classical.move_requires f ()
  in
  g ();
  Lemmas.logand_mask #32 (Secret.v x) (8 `Prims.op_Multiply` U32.v pn_len');
  [@inline_let]
  let y = x `Secret.logand` mask in
  assert (Secret.v y == U.logand #32 (Secret.v x) (Secret.v mask));
  y

#pop-options

#push-options "--z3rlimit 256"

#restart-solver

inline_for_extraction
[@"opaque_to_smt"]
val set_left_bitfield_aux
  (pn_len: packet_number_length_t)
  (pn_len' : U32.t { 1 <= U32.v pn_len' /\ U32.v pn_len' <= 4 } )
  (before: Secret.uint32)
  (x: Secret.uint32 {
    Secret.v pn_len == U32.v pn_len' ==> LP.bounded_integer_prop (Secret.v pn_len) (U32.uint_to_t (Secret.v x))
  })
  (mask: Secret.uint32 { Secret.v mask == pow2 (8 `Prims.op_Multiply` (U32.v pn_len')) - 1 })
: Tot (after: Secret.uint32 { Secret.v after == (if Secret.v pn_len = U32.v pn_len' then 
BF.set_bitfield #32 (Secret.v before) (8 `Prims.op_Multiply` (4 - Secret.v pn_len)) 32 (Secret.v x <: nat) else 0) })

let set_left_bitfield_aux
  pn_len pn_len' before x mask
= 
  [@inline_let]
  let pn_len_1 = Secret.to_u32 (pn_len `Secret.sub` Secret.to_u32 1ul) in
  (pn_len_1 `secrets_are_equal_32_2` Secret.to_u32 (pn_len' `U32.sub` 1ul)) `Secret.mul` Secret.set_bitfield before (8ul `U32.mul` (4ul `U32.sub` pn_len')) 32ul (set_left_bitfield_arg pn_len pn_len' x mask)

#pop-options

#push-options "--z3rlimit 128"

#restart-solver

[@"opaque_to_smt"]
let set_left_bitfield
  (pn_len: packet_number_length_t)
  (before: Secret.uint32)
  (x: secret_bounded_integer (Secret.v pn_len))
: Tot (after: Secret.uint32 { Secret.v after = BF.set_bitfield #32 (Secret.v before) (8 `Prims.op_Multiply` (4 - Secret.v pn_len)) 32 (Secret.v x) })
=
  BF.set_bitfield_full #32 (Secret.v before) (Secret.v x);
  assert_norm (pow2 8 == 256);
  assert_norm (pow2 16 == 65536);
  assert_norm (pow2 24 == 16777216);
  [@inline_let]
  let pn_len_1 = Secret.to_u32 (pn_len `Secret.sub` Secret.to_u32 1ul) in
  set_left_bitfield_aux pn_len 1ul before x (Secret.to_u32 255ul) `Secret.add`
  set_left_bitfield_aux pn_len 2ul before x (Secret.to_u32 65535ul) `Secret.add`
  set_left_bitfield_aux pn_len 3ul before x (Secret.to_u32 16777215ul) `Secret.add`
  ((pn_len_1 `secrets_are_equal_32_2` Secret.to_u32 3ul) `Secret.mul` x)

#pop-options

#push-options "--z3rlimit 16"

#restart-solver

let set_left_bitfield_left
  (pn_len: packet_number_length_t)
  (before: Secret.uint32)
  (x: secret_bounded_integer (Secret.v pn_len))
: Lemma
  (Seq.slice (E.n_to_be 4 (Secret.v (set_left_bitfield pn_len before x))) 0 (Secret.v pn_len) == E.n_to_be (Secret.v pn_len) (Secret.v x))
=
  E.slice_n_to_be_bitfield 4 (Secret.v (set_left_bitfield pn_len before x)) 0 (Secret.v pn_len);
  BF.get_bitfield_set_bitfield_same #32 (Secret.v before) (8 `op_Multiply` (4 - Secret.v pn_len)) 32 (Secret.v x)

let set_left_bitfield_right
  (pn_len: packet_number_length_t)
  (before: Secret.uint32)
  (x: secret_bounded_integer (Secret.v pn_len))
: Lemma
  (Seq.slice (E.n_to_be 4 (Secret.v (set_left_bitfield pn_len before x))) (Secret.v pn_len) 4 == Seq.slice (E.n_to_be 4 (Secret.v before)) (Secret.v pn_len) 4)
= 
  E.slice_n_to_be_bitfield 4 (Secret.v (set_left_bitfield pn_len before x)) (Secret.v pn_len) 4;
  E.slice_n_to_be_bitfield 4 (Secret.v before) (Secret.v pn_len) 4;
  BF.get_bitfield_set_bitfield_other #32 (Secret.v before) (8 `op_Multiply` (4 - Secret.v pn_len)) 32 (Secret.v x) 0 (8 `op_Multiply` (4 - Secret.v pn_len))

#pop-options

#push-options "--z3rlimit 16"

let write_bounded_integer
  (pn_len: packet_number_length_t)
  (x: secret_bounded_integer (Secret.v pn_len))
  (b: B.buffer Secret.uint8)
: HST.Stack unit
  (requires (fun h ->
    B.live h b /\
    4 <= B.length b
  ))
  (ensures (fun h _ h' ->
    let b' = B.gsub b 0ul (U32.uint_to_t (Secret.v pn_len)) in
    B.modifies (B.loc_buffer b') h h' /\
    Seq.seq_reveal (B.as_seq h' b') `Seq.equal` LP.serialize (LP.serialize_bounded_integer (Secret.v pn_len)) (U32.uint_to_t (Secret.v x))
  ))
= 
  let h = HST.get () in
  let b' = B.sub b 0ul 4ul in
  let before = read_u32 b' in
  LP.parse_u32_spec (Seq.seq_reveal (B.as_seq h b'));
  LP.bounded_integer_prop_equiv (Secret.v pn_len) (U32.uint_to_t (Secret.v x));
  let after = set_left_bitfield pn_len before x in
  write_u32 after b';
  serialize_u32_spec (U32.uint_to_t (Secret.v after));
  LP.serialize_bounded_integer_spec (Secret.v pn_len) (U32.uint_to_t (Secret.v x));
  set_left_bitfield_left pn_len before x;
  set_left_bitfield_right pn_len before x;
  let h' = HST.get () in
  assert (Seq.slice (Seq.seq_reveal (B.as_seq h' b')) (Secret.v pn_len) 4 `Seq.equal` Seq.slice (Seq.seq_reveal (B.as_seq h b')) (Secret.v pn_len) 4);
  assert (Seq.seq_reveal (Seq.slice (B.as_seq h' b') (Secret.v pn_len) 4) `Seq.equal` Seq.slice (Seq.seq_reveal (B.as_seq h' b')) (Secret.v pn_len) 4);
  assert (Seq.seq_reveal (Seq.slice (B.as_seq h b') (Secret.v pn_len) 4) `Seq.equal` Seq.slice (Seq.seq_reveal (B.as_seq h b')) (Secret.v pn_len) 4);
  Seq.seq_reveal_inj (Seq.slice (B.as_seq h' b') (Secret.v pn_len) 4) (Seq.slice (B.as_seq h b') (Secret.v pn_len) 4);
  B.modifies_loc_buffer_from_to_intro b' 0ul (U32.uint_to_t (Secret.v pn_len)) B.loc_none h h'


#pop-options

let write_packet_number
  last pn_len pn b
= let h = HST.get () in
  LP.serialize_synth_eq
    (LP.lift_parser (parse_reduced_pn pn_len))
    (synth_packet_number last pn_len)
    (LP.lift_serializer (serialize_reduced_pn pn_len))
    (synth_packet_number_recip last pn_len)
    ()
    pn;
  let npn = reduce_pn pn_len pn in
  write_bounded_integer pn_len npn b
