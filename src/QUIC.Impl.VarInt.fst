module QUIC.Impl.VarInt
friend QUIC.Spec.VarInt

open LowParse.Spec.BoundedInt
open LowParse.Spec.BitFields

module HST = FStar.HyperStack.ST
module LL = LowParse.Low.BoundedInt
module LI = LowParse.Low.Int
module LC = LowParse.Low.Combinators

module Cast = FStar.Int.Cast
module U64 = FStar.UInt64
module U32 = FStar.UInt32
module U16 = FStar.UInt16
module U8 = FStar.UInt8

#push-options "--z3rlimit 128"

let validate_varint #rrel #rel sl pos =
  let h = HST.get () in
  [@inline_let]
  let _ =
    assert_norm (pow2 8 == 256);
    assert_norm (pow2 6 == 64);
    assert (pow2 62 == U64.v uint62_bound);
    assert_norm (pow2 24 == 16777216);
    assert_norm (pow2 32 == 4294967296);
    LL.valid_facts parse_varint h sl pos;
    parse_varint_eq (LL.bytes_of_slice_from h sl pos);
    LL.valid_facts parse_u8 h sl pos
  in
  let pos1 = LI.validate_u8 () sl pos in
  if pos1 `U32.gt` LL.validator_max_length
  then pos1
  else
    let b = LI.read_u8 sl pos in
    let kd = uint8.get_bitfield b 6 8 in
    let msb = Cast.uint8_to_uint64 (uint8.get_bitfield b 0 6) in
    if kd = 0uy
    then pos1
    else if kd = 1uy
    then begin
      [@inline_let]
      let _ =
        LL.valid_facts parse_u8 h sl pos1
      in
      let pos2 = LI.validate_u8 () sl pos1 in
      if pos2 `U32.gt` LL.validator_max_length
      then pos2
      else
        let lsb = LI.read_u8 sl pos1 in
        let z = synth_u14 msb lsb in
        if filter_u14 z
        then pos2
        else LL.validator_error_generic
    end else if kd = 2uy
    then begin
      [@inline_let]
      let _ =
        LL.valid_facts (parse_bounded_integer 3) h sl pos1
      in
      let pos2 = LL.validate_bounded_integer 3 sl pos1 in
      if pos2 `U32.gt` LL.validator_max_length
      then pos2
      else
        let lsb = LL.read_bounded_integer 3 sl pos1 in
        let z = synth_u30 msb lsb in
        if filter_u30 z
        then pos2
        else LL.validator_error_generic        
    end else begin
      [@inline_let]
      let _ =
        LL.valid_facts (parse_u32 `nondep_then` parse_bounded_integer 3) h sl pos1
      in
      let pos2 = LC.validate_nondep_then (LI.validate_u32 ()) (LL.validate_bounded_integer 3) sl pos1 in
      if pos2 `U32.gt` LL.validator_max_length
      then pos2
      else
        let pos_hi = LC.accessor_fst LL.parse_u32 () (LL.parse_bounded_integer 3) sl pos1 in
        let hi = LI.read_u32 sl pos_hi in
        let pos_lo = LC.accessor_snd LI.jump_u32 (LL.parse_bounded_integer 3) sl pos1 in
        let lo = LL.read_bounded_integer 3 sl pos_lo in
        let z = synth_u62 msb (hi, lo) in
        if filter_u62 z
        then pos2
        else LL.validator_error_generic
    end

let read_varint #rrel #rel sl pos =
  let h = HST.get () in
  [@inline_let]
  let _ =
    assert_norm (pow2 8 == 256);
    assert_norm (pow2 6 == 64);
    assert (pow2 62 == U64.v uint62_bound);
    assert_norm (pow2 24 == 16777216);
    assert_norm (pow2 32 == 4294967296);
    LL.valid_facts parse_varint h sl pos;
    parse_varint_eq (LL.bytes_of_slice_from h sl pos);
    LL.valid_facts parse_u8 h sl pos
  in
  let pos1 = LI.jump_u8 sl pos in
  let b = LI.read_u8 sl pos in
  let kd = uint8.get_bitfield b 6 8 in
  let msb = Cast.uint8_to_uint64 (uint8.get_bitfield b 0 6) in
  if kd = 0uy
  then msb
  else if kd = 1uy
  then begin
    [@inline_let]
    let _ =
      LL.valid_facts parse_u8 h sl pos1
    in
    let lsb = LI.read_u8 sl pos1 in
    synth_u14 msb lsb
  end else if kd = 2uy
  then begin
    [@inline_let]
    let _ =
      LL.valid_facts (parse_bounded_integer 3) h sl pos1
    in
    let lsb = LL.read_bounded_integer 3 sl pos1 in
    synth_u30 msb lsb
  end else begin
    [@inline_let]
    let _ =
      LL.valid_facts (parse_u32 `nondep_then` parse_bounded_integer 3) h sl pos1
    in
    let pos_hi = LC.accessor_fst LL.parse_u32 () (LL.parse_bounded_integer 3) sl pos1 in
    let hi = LI.read_u32 sl pos_hi in
    let pos_lo = LC.accessor_snd LI.jump_u32 (LL.parse_bounded_integer 3) sl pos1 in
    let lo = LL.read_bounded_integer 3 sl pos_lo in
    synth_u62 msb (hi, lo)
  end

let jump_varint #rrel #rel sl pos =
  let h = HST.get () in
  [@inline_let]
  let _ =
    assert_norm (pow2 8 == 256);
    assert_norm (pow2 6 == 64);
    assert (pow2 62 == U64.v uint62_bound);
    assert_norm (pow2 24 == 16777216);
    assert_norm (pow2 32 == 4294967296);
    LL.valid_facts parse_varint h sl pos;
    parse_varint_eq (LL.bytes_of_slice_from h sl pos);
    LL.valid_facts parse_u8 h sl pos
  in
  let pos1 = LI.jump_u8 sl pos in
  let b = LI.read_u8 sl pos in
  let kd = uint8.get_bitfield b 6 8 in
  let msb = Cast.uint8_to_uint64 (uint8.get_bitfield b 0 6) in
  if kd = 0uy
  then pos1
  else if kd = 1uy
  then begin
    [@inline_let]
    let _ =
      LL.valid_facts parse_u8 h sl pos1
    in
    LI.jump_u8 sl pos1
  end else if kd = 2uy
  then begin
    [@inline_let]
    let _ =
      LL.valid_facts (parse_bounded_integer 3) h sl pos1
    in
    LL.jump_bounded_integer 3 sl pos1
  end else begin
    [@inline_let]
    let _ =
      LL.valid_facts (parse_u32 `nondep_then` parse_bounded_integer 3) h sl pos1
    in
    LC.jump_nondep_then (LI.jump_u32) (LL.jump_bounded_integer 3) sl pos1
  end

module B = LowStar.Buffer

let seq_slice_i_j_k
  (#a: Type)
  (s: Seq.seq a)
  (i j k: nat)
: Lemma
  (requires (i <= j /\ j <= k /\ k <= Seq.length s))
  (ensures (Seq.slice s i k `Seq.equal` (Seq.slice s i j `Seq.append` Seq.slice s j k)))
= ()

let serialize_varint
  x #rrel #rel b pos
=
  assert_norm (pow2 8 == 256);
  assert_norm (pow2 6 == 64);
  assert (pow2 62 == U64.v uint62_bound);
  assert_norm (pow2 24 == 16777216);
  assert_norm (pow2 32 == 4294967296);
  let fb = get_first_byte x in
  let gpos' = Ghost.hide (pos `U32.add` U32.uint_to_t (Seq.length (serialize serialize_varint x))) in
  let len1 = LL.frame_serializer32 LI.serialize32_u8 fb b (Ghost.hide pos) gpos' pos in
  let pos1 = pos `U32.add` len1 in
  if x `U64.lt` 64uL
  then len1
  else begin
    let len2 =
      if x `U64.lt` 16384uL
      then
        LL.frame_serializer32 LI.serialize32_u8 (Cast.uint64_to_uint8 x) b (Ghost.hide pos) gpos' pos1
      else if x `U64.lt` 1073741824uL
      then
        LL.frame_serializer32 (LL.serialize32_bounded_integer_3 ()) (Cast.uint64_to_uint32 (x `U64.rem` 16777216uL)) b (Ghost.hide pos) gpos' pos1
      else
        LL.frame_serializer32 (LC.serialize32_nondep_then LI.serialize32_u32 (LL.serialize32_bounded_integer_3 ())) (Cast.uint64_to_uint32 (x `U64.div` 16777216uL), Cast.uint64_to_uint32 (x `U64.rem` 16777216uL)) b (Ghost.hide pos) gpos' pos1
    in
    let res = len1 `U32.add` len2 in
    let h' = HST.get () in
    seq_slice_i_j_k (B.as_seq h' b) (U32.v pos) (U32.v pos1) (U32.v pos + U32.v res);
    res
  end

#pop-options

let validate_bounded_varint
  min max
= 
  LC.validate_synth
    (LC.validate_filter
      validate_varint
      read_varint
      (varint_in_bounds (U32.v min) (U32.v max))
      (fun x -> Cast.uint32_to_uint64 min `U64.lte` x && x `U64.lte` Cast.uint32_to_uint64 max))
    (synth_bounded_varint (U32.v min) (U32.v max))
    ()

let read_bounded_varint
  min max
= LC.read_synth
    _
    (synth_bounded_varint min max)
    (fun x -> synth_bounded_varint min max x)
    (LC.read_filter
      read_varint
      (varint_in_bounds min max))
    ()

let jump_bounded_varint
  min max
= LC.jump_synth
    (LC.jump_filter
      jump_varint
      (varint_in_bounds min max))
    (synth_bounded_varint min max)
    ()

let serialize_bounded_varint
  min max
= LC.serialize32_synth
    (LC.serialize32_filter
      serialize_varint
      (varint_in_bounds min max))
    (synth_bounded_varint min max)
    (synth_bounded_varint_recip min max)
    (fun x -> synth_bounded_varint_recip min max x)
    ()

let varint_len_correct
  x
= ()

let bounded_varint_len_correct
  min max x
= serialize_synth_eq
    _
    (synth_bounded_varint min max)
    (QUIC.Spec.VarInt.serialize_varint `serialize_filter` varint_in_bounds min max)
    (synth_bounded_varint_recip min max)
    ()
    x;
  varint_len_correct (Cast.uint32_to_uint64 x)
