module QUIC.Parse.VarInt

open LowParse.Spec.BoundedInt
open LowParse.Spec.BitFields

inline_for_extraction
let parse_varint_payload_kind = {
  parser_kind_low = 0;
  parser_kind_high = Some 7;
  parser_kind_subkind = Some ParserStrong;
  parser_kind_metadata = None;
}

module Cast = FStar.Int.Cast
module U64 = FStar.UInt64
module U32 = FStar.UInt32
module U16 = FStar.UInt16
module U8 = FStar.UInt8

inline_for_extraction
let varint_msb_t = (x: U64.t { U64.v x < 64 })

#push-options "--z3rlimit 32"

inline_for_extraction
let synth_u14
  (msb: varint_msb_t)
  (lsb: U8.t)
: Tot varint_t
= [@inline_let] let _ =
    assert_norm (pow2 8 == 256);
    assert (pow2 62 == U64.v varint_bound)
  in
  (msb `U64.mul` 256uL) `U64.add` Cast.uint8_to_uint64 lsb  

let synth_u14_injective
  (msb: varint_msb_t)
: Lemma
  (synth_injective (synth_u14 msb))
  [SMTPat (synth_injective (synth_u14 msb))]
= ()

inline_for_extraction
let synth_u30
  (msb: varint_msb_t)
  (lsb: bounded_integer 3)
: Tot varint_t
= [@inline_let] let _ =
    assert_norm (pow2 8 == 256);
    assert (pow2 62 == U64.v varint_bound);
    assert_norm (pow2 24 == 16777216)
   in
   (msb `U64.mul` 16777216uL) `U64.add` Cast.uint32_to_uint64 lsb

let synth_u30_injective
  (msb: varint_msb_t)
: Lemma
  (synth_injective (synth_u30 msb))
  [SMTPat (synth_injective (synth_u30 msb))]
= ()

inline_for_extraction
let synth_u62
  (msb: varint_msb_t)
  (lsb: (U32.t & bounded_integer 3))
: Tot varint_t
= [@inline_let] let _ =
  assert_norm (pow2 8 == 256);
  assert (pow2 62 == U64.v varint_bound);
  assert_norm (pow2 24 == 16777216);
  assert_norm (pow2 32 == 4294967296)
  in
  match lsb with
  | (hi, lo) ->
  Cast.uint32_to_uint64 lo `U64.add` (16777216uL `U64.mul` (Cast.uint32_to_uint64 hi `U64.add` (4294967296uL `U64.mul` msb)))

let synth_u62_msb
  (msb: varint_msb_t)
  (lsb: (U32.t & bounded_integer 3))
: Lemma
  (U64.v (synth_u62 msb lsb) / 72057594037927936 == U64.v msb)
= ()

let synth_u62_injective
  (msb: varint_msb_t)
: Lemma
  (synth_injective (synth_u62 msb))
  [SMTPat (synth_injective (synth_u62 msb))]
= ()

inline_for_extraction
let filter_u14
  (y: varint_t)
: Tot bool
= 64uL `U64.lte` y

inline_for_extraction
let filter_u30
  (y: varint_t)
: Tot bool
= 16384uL `U64.lte` y

inline_for_extraction
let filter_u62
  (y: varint_t)
: Tot bool
= 1073741824uL `U64.lte` y
    
inline_for_extraction
let id_u14
  (y: parse_filter_refine filter_u14)
: Tot varint_t
= y

let parse_varint_payload_u14
  (msb: varint_msb_t)
: Tot (parser parse_varint_payload_kind varint_t)
= 
  weaken parse_varint_payload_kind
    (((parse_u8 `parse_synth` synth_u14 msb)
    `parse_filter` filter_u14)
    `parse_synth` id_u14)
    
inline_for_extraction
let id_u30
  (y: parse_filter_refine filter_u30)
: Tot varint_t
= y

let parse_varint_payload_u30
  (msb: varint_msb_t)
: Tot (parser parse_varint_payload_kind varint_t)
= 
  weaken parse_varint_payload_kind
    (((parse_bounded_integer 3 `parse_synth` synth_u30 msb)
    `parse_filter` filter_u30)
    `parse_synth` id_u30)

inline_for_extraction
let id_u62
  (y: parse_filter_refine filter_u62)
: Tot varint_t
= y

let p7 = parse_u32 `nondep_then` parse_bounded_integer 3

let parse_varint_payload_u62
  (msb: varint_msb_t)
: Tot (parser parse_varint_payload_kind varint_t)
= 
  weaken parse_varint_payload_kind
    ((((p7) `parse_synth` synth_u62 msb)
    `parse_filter` filter_u62)
    `parse_synth` id_u62)

let parse_varint_payload_14_interval
  (msb: varint_msb_t)
  (b: bytes)
: Lemma
  (requires (Some? (parse (parse_varint_payload_u14 msb) b)))
  (ensures (
    let Some (v, _) = parse (parse_varint_payload_u14 msb) b in
    64 <= U64.v v /\
    U64.v v < 16384 /\
    U64.v msb == U64.v v / 256
  ))
= 
   assert_norm (pow2 6 == 64);
   assert_norm (pow2 8 == 256);
   assert (pow2 62 == U64.v varint_bound);
   assert_norm (pow2 32 == 4294967296);
   assert_norm (pow2 24 == 16777216);
   parse_synth_eq parse_u8 (synth_u14 msb) b;
   parse_filter_eq (parse_u8 `parse_synth` (synth_u14 msb)) filter_u14 b;
   parse_synth_eq ((parse_u8 `parse_synth` (synth_u14 msb)) `parse_filter` filter_u14) id_u14 b

let parse_varint_payload_30_interval
  (msb: varint_msb_t)
  (b: bytes)
: Lemma
  (requires (Some? (parse (parse_varint_payload_u30 msb) b)))
  (ensures (
    let Some (v, _) = parse (parse_varint_payload_u30 msb) b in
    16384 <= U64.v v /\
    U64.v v < 1073741824 /\
    U64.v msb == U64.v v / 16777216
  ))
= 
    parse_synth_eq (parse_bounded_integer 3) (synth_u30 msb) b;
    parse_filter_eq (parse_bounded_integer 3 `parse_synth` (synth_u30 msb)) filter_u30 b;
    parse_synth_eq ((parse_bounded_integer 3 `parse_synth` (synth_u30 msb)) `parse_filter` filter_u30) (id_u30) b

let parse_varint_payload_62_interval
  (msb: varint_msb_t)
  (b: bytes)
: Lemma
  (requires (Some? (parse (parse_varint_payload_u62 msb) b)))
  (ensures (
    let Some (v, _) = parse (parse_varint_payload_u62 msb) b in
    1073741824 <= U64.v v /\
    U64.v msb == U64.v v / (72057594037927936)
  ))
= 
   assert_norm (pow2 6 == 64);
   assert_norm (pow2 8 == 256);
   assert (pow2 62 == U64.v varint_bound);
   assert_norm (pow2 32 == 4294967296);
   assert_norm (pow2 24 == 16777216);
   parse_synth_eq (p7) (synth_u62 msb) b;
   parse_filter_eq ((p7) `parse_synth` synth_u62 msb) filter_u62 b;
   parse_synth_eq (((p7) `parse_synth` (synth_u62 msb)) `parse_filter` filter_u62) (id_u62) b;
   let Some (v, _) = parse (parse_varint_payload_u62 msb) b in
   let Some (lsb, _) = parse (p7) b in
   synth_u62_msb msb lsb

let parse_varint_payload
  (x: U8.t)
: Tot (parser parse_varint_payload_kind varint_t)
= assert_norm (pow2 6 == 64);
  assert_norm (pow2 8 == 256);
  assert (pow2 62 == U64.v varint_bound);
  assert_norm (pow2 32 == 4294967296);
  assert_norm (pow2 24 == 16777216);
  let kd = uint8.get_bitfield x 6 8 in
  let msb : varint_msb_t = Cast.uint8_to_uint64 (uint8.get_bitfield x 0 6) in
  if kd = 0uy
  then weaken parse_varint_payload_kind (parse_ret msb)
  else if kd = 1uy
  then parse_varint_payload_u14 msb
  else if kd = 2uy
  then parse_varint_payload_u30 msb
  else parse_varint_payload_u62 msb

module BF = LowParse.BitFields

let parse_varint_payload_interval
  (tag: U8.t)
  (b: bytes)
: Lemma
  (requires (Some? (parse (parse_varint_payload tag) b)))
  (ensures (
    let Some (v, _) = parse (parse_varint_payload tag) b in
    let kd = uint8.get_bitfield tag 6 8 in
    let msb = uint8.get_bitfield tag 0 6 in
    (kd == 0uy \/ kd == 1uy \/ kd == 2uy \/ kd == 3uy) /\ (
    if kd = 0uy
    then U64.v v < 64 /\ U8.v msb = U64.v v
    else if kd = 1uy
    then 64 <= U64.v v /\ U64.v v < 16384 /\ U8.v msb == U64.v v / 256
    else if kd = 2uy
    then 16384 <= U64.v v /\ U64.v v < 1073741824 /\ U8.v msb == U64.v v / 16777216
    else 1073741824 <= U64.v v /\ U8.v msb == U64.v v / 72057594037927936
  )))
=
  assert_norm (pow2 6 == 64);
  assert_norm (pow2 8 == 256);
  assert (pow2 62 == U64.v varint_bound);
  assert_norm (pow2 32 == 4294967296);
  assert_norm (pow2 24 == 16777216);
  let Some (v, _) = parse (parse_varint_payload tag) b in
  let kd = uint8.get_bitfield tag 6 8 in
  assert (kd == 0uy \/ kd == 1uy \/ kd == 2uy \/ kd == 3uy);
  let msb8 = uint8.get_bitfield tag 0 6 in
  let msb = Cast.uint8_to_uint64 msb8 in
  if kd = 0uy
  then begin
    assert (U64.v v < 64);
    assert (U8.v msb8 == U64.v v)
  end
  else if kd = 1uy
  then begin
    parse_varint_payload_14_interval msb b
  end else if kd = 2uy
  then
    parse_varint_payload_30_interval msb b
  else
    parse_varint_payload_62_interval msb b

#pop-options

let parse_varint_payload_and_then_cases_injective : squash (and_then_cases_injective parse_varint_payload) =
  assert_norm (pow2 8 == 256);
  assert (pow2 62 == U64.v varint_bound);
  assert_norm (pow2 32 == 4294967296);
  assert_norm (pow2 24 == 16777216);
  and_then_cases_injective_intro parse_varint_payload (fun x1 x2 b1 b2 ->
    let msb1 = Cast.uint8_to_uint64 (uint8.get_bitfield x1 0 6) in
    let msb2 = Cast.uint8_to_uint64 (uint8.get_bitfield x2 0 6) in
    parse_varint_payload_interval x1 b1;
    parse_varint_payload_interval x2 b2;
    assert (uint8.v (uint8.get_bitfield x1 6 8) == uint8.v (uint8.get_bitfield x2 6 8));
    assert (uint8.v (uint8.get_bitfield x1 0 6) == uint8.v (uint8.get_bitfield x2 0 6));
    BF.get_bitfield_partition_2 6 (U8.v x1) (U8.v x2)
  )

let parse_varint =
  parse_u8 `and_then` parse_varint_payload

let parse_varint_eq_aux
  (b: bytes)
: Lemma
  (pow2 8 == 256 /\ pow2 62 == U64.v varint_bound /\ pow2 24 == 16777216 /\ pow2 32 == 4294967296 /\
  parse parse_varint b == (match parse parse_u8 b with
  | None -> None
  | Some (hd, consumed) ->
    let b' = Seq.slice b consumed (Seq.length b) in
    match parse (parse_varint_payload hd) b' with
    | None -> None
    | Some (res, consumed') -> Some (res, consumed + consumed')
  ))
= assert_norm (pow2 8 == 256);
  assert (pow2 62 == U64.v varint_bound);
  assert_norm (pow2 24 == 16777216);
  assert_norm (pow2 32 == 4294967296);
  and_then_eq parse_u8 parse_varint_payload b

#push-options "--z3rlimit 128"

let parse_varint'
  (b: bytes)
: GTot (option (varint_t & consumed_length b))
= assert_norm (pow2 8 == 256);
  assert_norm (pow2 6 == 64);
  assert (pow2 62 == U64.v varint_bound);
  assert_norm (pow2 24 == 16777216);
  assert_norm (pow2 32 == 4294967296);
  match parse parse_u8 b with
  | None -> None
  | Some (hd, consumed) ->
    let tag = uint8.get_bitfield hd 6 8 in
    let msb = Cast.uint8_to_uint64 (uint8.get_bitfield hd 0 6) in
    let b' = Seq.slice b consumed (Seq.length b) in
    if tag = 0uy
    then
      Some ((msb <: varint_t), consumed)
    else if tag = 1uy
    then begin match parse parse_u8 b' with
    | None -> None
    | Some (lsb, consumed') ->
      let v : varint_t = (msb `U64.mul` 256uL) `U64.add` Cast.uint8_to_uint64 lsb in
      if 64uL `U64.lte` v
      then Some (v, consumed + consumed')
      else None
      end
    else if tag = 2uy
    then begin match parse (parse_bounded_integer 3) b' with
    | None -> None
    | Some (lsb, consumed') ->
      let v : varint_t =
        (msb `U64.mul` 16777216uL) `U64.add` Cast.uint32_to_uint64 lsb
      in
      if 16384uL `U64.lte` v
      then Some (v, consumed + consumed')
      else None
    end else begin match parse (parse_u32 `nondep_then` parse_bounded_integer 3) b' with
    | None -> None
    | Some ((hi, lo), consumed') ->
      let v : varint_t =
        Cast.uint32_to_uint64 lo `U64.add` (16777216uL `U64.mul` (Cast.uint32_to_uint64 hi `U64.add` (4294967296uL `U64.mul` msb)))
      in
      if 1073741824uL `U64.lte` v
      then Some (v, consumed + consumed')
      else None
    end

let parse_varint_eq
  (b: bytes)
: Lemma
  (pow2 8 == 256 /\ pow2 62 == U64.v varint_bound /\ pow2 24 == 16777216 /\ pow2 32 == 4294967296 /\
  parse parse_varint b == parse_varint' b)
= assert_norm (pow2 8 == 256);
  assert_norm (pow2 6 == 64);
  assert (pow2 62 == U64.v varint_bound);
  assert_norm (pow2 24 == 16777216);
  assert_norm (pow2 32 == 4294967296);
  parse_varint_eq_aux b;
  match parse parse_u8 b with
  | None -> ()
  | Some (hd, consumed) ->
    let tag = uint8.get_bitfield hd 6 8 in
    let msb8 = uint8.get_bitfield hd 0 6 in
    let msb = Cast.uint8_to_uint64 msb8 in
    let b' = Seq.slice b consumed (Seq.length b) in
    assert (tag == 0uy \/ tag == 1uy \/ tag == 2uy \/ tag == 3uy);
    if tag = 0uy
    then ()
    else if tag = 1uy
    then begin
      parse_synth_eq parse_u8 (synth_u14 msb) b';
      parse_filter_eq (parse_u8 `parse_synth` (synth_u14 msb)) filter_u14 b';
      parse_synth_eq ((parse_u8 `parse_synth` (synth_u14 msb)) `parse_filter` filter_u14) id_u14 b'
    end else if tag = 2uy
    then begin
      parse_synth_eq (parse_bounded_integer 3) (synth_u30 msb) b';
      parse_filter_eq (parse_bounded_integer 3 `parse_synth` (synth_u30 msb)) filter_u30 b';
      parse_synth_eq ((parse_bounded_integer 3 `parse_synth` (synth_u30 msb)) `parse_filter` filter_u30) id_u30 b'
    end else begin
      parse_synth_eq (p7) (synth_u62 msb) b';
      parse_filter_eq (p7 `parse_synth` (synth_u62 msb)) filter_u62 b';
      parse_synth_eq ((p7 `parse_synth` (synth_u62 msb)) `parse_filter` filter_u62) id_u62 b'
    end

#pop-options

inline_for_extraction
let get_tag
  (x: varint_t)
: Tot (bitfield uint8 2)
= if x `U64.lt` 64uL
  then 0uy
  else if x `U64.lt` 16384uL
  then 1uy
  else if x `U64.lt` 1073741824uL
  then 2uy
  else 3uy

inline_for_extraction
let get_msb
  (x: varint_t)
: Tot varint_msb_t
= if x `U64.lt` 64uL
  then x
  else if x `U64.lt` 16384uL
  then (x `U64.div` 256uL)
  else if x `U64.lt` 1073741824uL
  then (x `U64.div` 16777216uL)
  else (x `U64.div` 72057594037927936uL)

inline_for_extraction
let get_first_byte
  (x: varint_t)
: Tot U8.t
= uint8.set_bitfield (uint8.set_bitfield 0uy 0 6 (Cast.uint64_to_uint8 (get_msb x))) 6 8 (get_tag x)

#push-options "--z3rlimit 16"

let serialize_varint_payload
  (x: varint_t)
: GTot bytes
=
  assert_norm (pow2 8 == 256);
  assert_norm (pow2 6 == 64);
  assert (pow2 62 == U64.v varint_bound);
  assert_norm (pow2 24 == 16777216);
  assert_norm (pow2 32 == 4294967296);
  if x `U64.lt` 64uL
  then Seq.empty
  else if x `U64.lt` 16384uL
  then serialize serialize_u8 (Cast.uint64_to_uint8 x)
  else if x `U64.lt` 1073741824uL
  then serialize (serialize_bounded_integer 3) (Cast.uint64_to_uint32 (x `U64.rem` 16777216uL))
  else serialize (serialize_u32 `serialize_nondep_then` serialize_bounded_integer 3) (Cast.uint64_to_uint32 (x `U64.div` 16777216uL), Cast.uint64_to_uint32 (x `U64.rem` 16777216uL))

let serialize_varint'
  (x: varint_t)
: GTot bytes
= serialize serialize_u8 (get_first_byte x) `Seq.append` serialize_varint_payload x

#pop-options

#push-options "--z3rlimit 1024"

let serialize_varint_correct
  (x: varint_t)
: Lemma
  (let y = serialize_varint' x in
    parse_varint' y == Some (x, Seq.length y)
  )
=
  assert_norm (pow2 8 == 256);
  assert_norm (pow2 6 == 64);
  assert (pow2 62 == U64.v varint_bound);
  assert_norm (pow2 24 == 16777216);
  assert_norm (pow2 32 == 4294967296);
  let y = serialize_varint' x in
  let z = get_first_byte x in
  let hd = serialize serialize_u8 z in
  assert (parse parse_u8 hd == Some (z, Seq.length hd));
  assert (Seq.slice hd 0 (Seq.length hd) `Seq.equal` Seq.slice y 0 (Seq.length hd));
  let tl = serialize_varint_payload x in
  assert (Seq.slice y (Seq.length hd) (Seq.length y) `Seq.equal` tl);
  parse_strong_prefix parse_u8 hd y;
  let tg = get_tag x in
  assert (uint8.get_bitfield z 6 8 == tg);
  if tg = 0uy
  then begin
    assert (x `U64.lt` 64uL);
    assert (U64.v x == U8.v (uint8.get_bitfield z 0 6));
    assert (x == Cast.uint8_to_uint64 (uint8.get_bitfield z 0 6));
    assert (y `Seq.equal` hd)
  end else if tg = 1uy
  then begin
    assert (64uL `U64.lte` x /\ x `U64.lt` 16384uL);
    let x' = Cast.uint64_to_uint8 x in
    assert (parse parse_u8 tl == Some (x', Seq.length tl));
    assert (U8.v (uint8.get_bitfield z 0 6) == U64.v x / 256);
    assert (U64.v x == (U8.v (uint8.get_bitfield z 0 6) `Prims.op_Multiply` 256) + U8.v x')
  end else if tg = 2uy
  then begin
    assert (16384uL `U64.lte` x /\ x `U64.lt` 1073741824uL);
    let x' : bounded_integer 3 = Cast.uint64_to_uint32 (x `U64.rem` 16777216uL) in
    assert (parse (parse_bounded_integer 3) tl == Some (x', Seq.length tl));
    assert (U8.v (uint8.get_bitfield z 0 6) == U64.v x / 16777216);
    assert (U64.v x == (U8.v (uint8.get_bitfield z 0 6) `Prims.op_Multiply` 16777216) + U32.v x')
  end else begin
    assert (1073741824uL `U64.lte` x);
    let lo : bounded_integer 3 = Cast.uint64_to_uint32 (x `U64.rem` 16777216uL) in
    let hi = Cast.uint64_to_uint32 (x `U64.div` 16777216uL) in
    assert (U8.v (uint8.get_bitfield z 0 6) == U64.v x / 72057594037927936);
    assert (U64.v x == U32.v lo + (16777216 `Prims.op_Multiply` (U32.v hi + (4294967296 `Prims.op_Multiply` U8.v (uint8.get_bitfield z 0 6)))))
  end

#pop-options

let serialize_varint =
  Classical.forall_intro parse_varint_eq;
  Classical.forall_intro serialize_varint_correct;
  serialize_varint'

let varint_in_bounds
  (min: nat)
  (max: nat { min <= max /\ max < 4294967296 })
  (x: varint_t)
: GTot bool
= min <= U64.v x && U64.v x <= max

inline_for_extraction
noextract
let synth_bounded_varint
  (min: nat)
  (max: nat { min <= max /\ max < 4294967296 })
  (x: parse_filter_refine (varint_in_bounds min max))
: Tot (bounded_int32 min max)
= Cast.uint64_to_uint32 x

let parse_bounded_varint min max =
  (parse_varint `parse_filter` varint_in_bounds min max) `parse_synth` synth_bounded_varint min max

inline_for_extraction
noextract
let synth_bounded_varint_recip
  (min: nat)
  (max: nat { min <= max /\ max < 4294967296 })
  (x: bounded_int32 min max)
: Tot (parse_filter_refine (varint_in_bounds min max))
= Cast.uint32_to_uint64 x

let serialize_bounded_varint min max =
  serialize_synth
    _
    (synth_bounded_varint min max)
    (serialize_varint `serialize_filter` varint_in_bounds min max)
    (synth_bounded_varint_recip min max)
    ()

module HST = FStar.HyperStack.ST
module LL = LowParse.Low.BoundedInt
module LI = LowParse.Low.Int
module LC = LowParse.Low.Combinators

#push-options "--z3rlimit 128"

let validate_varint #rrel #rel sl pos =
  let h = HST.get () in
  [@inline_let]
  let _ =
    assert_norm (pow2 8 == 256);
    assert_norm (pow2 6 == 64);
    assert (pow2 62 == U64.v varint_bound);
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
    assert (pow2 62 == U64.v varint_bound);
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
    assert (pow2 62 == U64.v varint_bound);
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

let serialize_varint_impl
  x #rrel #rel b pos
=
  assert_norm (pow2 8 == 256);
  assert_norm (pow2 6 == 64);
  assert (pow2 62 == U64.v varint_bound);
  assert_norm (pow2 24 == 16777216);
  assert_norm (pow2 32 == 4294967296);
  let fb = get_first_byte x in
  let h0 = HST.get () in
  LL.writable_weaken b (U32.v pos) (U32.v pos + Seq.length (serialize serialize_varint x)) h0 (U32.v pos) (U32.v pos + Seq.length (serialize serialize_u8 fb));
  let len1 = LI.serialize32_u8 fb b pos in
  let pos1 = pos `U32.add` len1 in
  let h1 = HST.get () in
  B.loc_includes_loc_buffer_from_to b pos (pos `U32.add` U32.uint_to_t (Seq.length (serialize serialize_varint x))) pos pos1;
  LL.writable_modifies b (U32.v pos) (U32.v pos + Seq.length (serialize serialize_varint x)) h0 B.loc_none h1;
  if x `U64.lt` 64uL
  then len1
  else begin
    LL.writable_weaken b (U32.v pos) (U32.v pos + Seq.length (serialize serialize_varint x)) h1 (U32.v pos1) (U32.v pos1 + Seq.length (serialize_varint_payload x));
    let len2 =
      if x `U64.lt` 16384uL
      then
        LI.serialize32_u8 (Cast.uint64_to_uint8 x) b pos1
      else if x `U64.lt` 1073741824uL
      then
        LL.serialize32_bounded_integer_3 () (Cast.uint64_to_uint32 (x `U64.rem` 16777216uL)) b pos1
      else
        LC.serialize32_nondep_then LI.serialize32_u32 (LL.serialize32_bounded_integer_3 ()) (Cast.uint64_to_uint32 (x `U64.div` 16777216uL), Cast.uint64_to_uint32 (x `U64.rem` 16777216uL)) b pos1
    in
    let h2 = HST.get () in
    let res = len1 `U32.add` len2 in
    B.loc_includes_loc_buffer_from_to b pos (pos `U32.add` res) pos1 (pos1 `U32.add` len2);
    B.loc_disjoint_loc_buffer_from_to b pos pos1 pos1 (pos1 `U32.add` len2);
    B.modifies_buffer_from_to_elim b pos pos1 (B.loc_buffer_from_to b pos1 (pos1 `U32.add` len2)) h1 h2;
    assert (Seq.length (serialize serialize_varint x) == U32.v res);
    assert (B.modifies (B.loc_buffer_from_to b pos (pos `U32.add` res)) h0 h2);
    seq_slice_i_j_k (B.as_seq h2 b) (U32.v pos) (U32.v pos1) (U32.v pos + U32.v res);
    assert (Seq.slice (B.as_seq h2 b) (U32.v pos) (U32.v pos + U32.v res) `Seq.equal` serialize serialize_varint x);
    res
  end

#pop-options
