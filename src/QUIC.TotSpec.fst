module QUIC.TotSpec

friend QUIC.Spec
friend QUIC.Spec.Header
friend QUIC.Spec.Header.Parse
friend QUIC.Spec.Header.Public
friend QUIC.Spec.PacketNumber
friend QUIC.Spec.VarInt

module PN = QUIC.Spec.PacketNumber
module VI = QUIC.Spec.VarInt
module Public = QUIC.Spec.Header.Public
module Parse = QUIC.Spec.Header.Parse
module Header = QUIC.Spec.Header
module Lemmas = QUIC.Spec.Lemmas
module Spec = QUIC.Spec

module LP = LowParse.SLow
module LPB = LowParse.SLow.BitSum

module U8 = FStar.UInt8
module U62 = QUIC.UInt62
module U64 = FStar.UInt64
module BF = LowParse.BitFields
module B32 = LowParse.Bytes32
module Cast = FStar.Int.Cast
module U32 = FStar.UInt32
module Seq = QUIC.Secret.Seq

#push-options "--z3rlimit 128"

let parse32_varint'
  (b: B32.bytes)
: Tot (option (U62.t & U32.t))
= assert_norm (pow2 8 == 256);
  assert_norm (pow2 6 == 64);
  assert (pow2 62 == U64.v U62.bound);
  assert_norm (pow2 24 == 16777216);
  assert_norm (pow2 32 == 4294967296);
  match LP.parse32_u8 b with
  | None -> None
  | Some (hd, consumed) ->
    let tag = BF.uint8.BF.get_bitfield hd 6 8 in
    let msb = Cast.uint8_to_uint64 (BF.uint8.BF.get_bitfield hd 0 6) in
    let b' = B32.slice b consumed (B32.len b) in
    if tag = 0uy
    then
      Some ((msb <: U62.t), consumed)
    else if tag = 1uy
    then begin match LP.parse32_u8 b' with
    | None -> None
    | Some (lsb, consumed') ->
      let v : U62.t = (msb `U64.mul` 256uL) `U64.add` Cast.uint8_to_uint64 lsb in
      if 64uL `U64.lte` v
      then Some (v, consumed `U32.add` consumed')
      else None
      end
    else if tag = 2uy
    then begin match (LP.parse32_bounded_integer 3) b' with
    | None -> None
    | Some (lsb, consumed') ->
      let v : U62.t =
        (msb `U64.mul` 16777216uL) `U64.add` Cast.uint32_to_uint64 lsb
      in
      if 16384uL `U64.lte` v
      then Some (v, consumed `U32.add` consumed')
      else None
    end else begin match (LP.parse32_u32 `LP.parse32_nondep_then` LP.parse32_bounded_integer 3) b' with
    | None -> None
    | Some ((hi, lo), consumed') ->
      let v : U62.t =
        Cast.uint32_to_uint64 lo `U64.add` (16777216uL `U64.mul` (Cast.uint32_to_uint64 hi `U64.add` (4294967296uL `U64.mul` msb)))
      in
      if 1073741824uL `U64.lte` v
      then Some (v, consumed `U32.add` consumed')
      else None
    end

let parse32_varint'_correct
  (input: B32.bytes)
: Lemma
  (LP.parser32_correct VI.parse_varint input (parse32_varint' input))
= VI.parse_varint_eq (B32.reveal input)

#pop-options

let parse32_varint
: LP.parser32 VI.parse_varint
= fun input ->
    parse32_varint'_correct input; 
    parse32_varint' input

let parse32_bounded_varint
  (min: U32.t)
  (max: U32.t { U32.v min <= U32.v max })
: Tot (LP.parser32 (VI.parse_bounded_varint (U32.v min) (U32.v max)))
= LP.parse32_synth'
   (VI.parse_varint `LP.parse_filter` VI.varint_in_bounds (U32.v min) (U32.v max))
   (VI.synth_bounded_varint (U32.v min) (U32.v max))
   (LP.parse32_filter
     parse32_varint
     (VI.varint_in_bounds (U32.v min) (U32.v max))
     (fun x -> Cast.uint32_to_uint64 min `U64.lte` x && x `U64.lte` Cast.uint32_to_uint64 max)
   )
   ()

let serialize32_varint_payload
  (x: U62.t)
: Tot B32.bytes
=
  assert_norm (pow2 8 == 256);
  assert_norm (pow2 6 == 64);
  assert (pow2 62 == U64.v U62.bound);
  assert_norm (pow2 24 == 16777216);
  assert_norm (pow2 32 == 4294967296);
  if x `U64.lt` 64uL
  then B32.empty_bytes
  else if x `U64.lt` 16384uL
  then LP.serialize32_u8 (Cast.uint64_to_uint8 x)
  else if x `U64.lt` 1073741824uL
  then (LP.serialize32_bounded_integer 3) (Cast.uint64_to_uint32 (x `U64.rem` 16777216uL))
  else (LP.serialize32_u32 `LP.serialize32_nondep_then` LP.serialize32_bounded_integer 3) (Cast.uint64_to_uint32 (x `U64.div` 16777216uL), Cast.uint64_to_uint32 (x `U64.rem` 16777216uL))

#push-options "--z3rlimit 16"

let serialize32_varint
  : LP.serializer32 VI.serialize_varint
= fun x ->
  LP.serialize32_u8 (VI.get_first_byte x) `B32.append` serialize32_varint_payload x

let serialize32_bounded_varint
  (min: nat)
  (max: nat { min <= max /\ max < 4294967296 })
: Tot (LP.serializer32 (VI.serialize_bounded_varint min max))
= LP.serialize32_synth
   (VI.parse_varint `LP.parse_filter` VI.varint_in_bounds (min) (max))
   (VI.synth_bounded_varint (min) (max))
   (VI.serialize_varint `LP.serialize_filter` VI.varint_in_bounds min max)
   (serialize32_varint `LP.serialize32_filter` VI.varint_in_bounds min max)
   (VI.synth_bounded_varint_recip min max)
   (fun x -> VI.synth_bounded_varint_recip min max x)
   ()

#pop-options
    
(* Packet number. *)

module Declassify = Lib.RawIntTypes (* this spec is only for proof purposes, so we do not care about preserving secrets/constant-time execution *)

#push-options "--z3rlimit 16"

let synth_packet_number'
  (last: PN.last_packet_number_t)
  (pn_len: PN.packet_number_length_t)
  (npn: LP.bounded_integer (Secret.v pn_len))
: Tot (pn: PN.packet_number_t' last pn_len { pn == PN.synth_packet_number last pn_len npn })
= Secret.to_u64 (U64.uint_to_t (PN.expand_pn' (Declassify.uint_to_nat pn_len - 1) (Declassify.uint_to_nat last) (U32.v npn)))

#pop-options

let parse32_reduced_pn
  (pn_len: PN.packet_number_length_t)
: Tot (LP.parser32 (PN.parse_reduced_pn pn_len ()))
= LP.parse32_weaken
    PN.parse_packet_number_kind
    (LP.parse32_bounded_integer (Declassify.uint_to_nat pn_len))

let parse32_packet_number
  (last: PN.last_packet_number_t)
  (pn_len: PN.packet_number_length_t)
: Tot (LP.parser32 (PN.parse_packet_number last pn_len))
= LP.parse32_synth
    _
    (PN.synth_packet_number last pn_len)
    (synth_packet_number' last pn_len)
    (LP.lift_parser32 (PN.parse_reduced_pn pn_len) (parse32_reduced_pn pn_len))
    ()

let serialize32_reduced_pn
  (pn_len: PN.packet_number_length_t)
: Tot (LP.serializer32 (PN.serialize_reduced_pn pn_len ()))
= LP.serialize32_weaken
    PN.parse_packet_number_kind
    (LP.serialize32_bounded_integer (Declassify.uint_to_nat pn_len))

let synth_packet_number_recip'
  (last: PN.last_packet_number_t)
  (pn_len: PN.packet_number_length_t)
  (pn: PN.packet_number_t' last pn_len)
: Tot (npn: LP.bounded_integer (Secret.v pn_len)  { npn == PN.synth_packet_number_recip last pn_len pn })
= U32.uint_to_t (PN.reduce_pn' (Declassify.uint_to_nat pn_len - 1) (Declassify.uint_to_nat pn))

let serialize32_packet_number
  (last: PN.last_packet_number_t)
  (pn_len: PN.packet_number_length_t)
: Tot (LP.serializer32 (PN.serialize_packet_number last pn_len))
= LP.serialize32_synth
    (LP.lift_parser (PN.parse_reduced_pn pn_len))
    (PN.synth_packet_number last pn_len)
    (LP.lift_serializer #_ #_ #(PN.parse_reduced_pn pn_len) (PN.serialize_reduced_pn pn_len))
    (LP.lift_serializer32 #PN.parse_packet_number_kind #(LP.bounded_integer (Declassify.uint_to_nat pn_len)) (PN.parse_reduced_pn pn_len) (PN.serialize_reduced_pn pn_len) (serialize32_reduced_pn pn_len))
    (PN.synth_packet_number_recip last pn_len)
    (synth_packet_number_recip' last pn_len)
    ()

(* Parsing the public header *)

let parse32_common_long : LP.parser32 Public.parse_common_long =
  LP.parse32_u32 `LP.parse32_nondep_then` (
    LP.parse32_bounded_vlbytes 0 0ul 20 20ul `LP.parse32_nondep_then`
    LP.parse32_bounded_vlbytes 0 0ul 20 20ul
  )

let parse32_payload_and_pn_length : LP.parser32 Public.parse_payload_and_pn_length =
  LP.parse32_filter
    parse32_varint
    Public.payload_and_pn_length_prop
    (fun x -> Public.payload_and_pn_length_prop x)

let parse32_long_zero_rtt_body : LP.parser32 Public.parse_long_zero_rtt_body =
  parse32_common_long `LP.parse32_nondep_then` parse32_payload_and_pn_length

let parse32_long_handshake_body : LP.parser32 Public.parse_long_handshake_body =
  parse32_common_long `LP.parse32_nondep_then` parse32_payload_and_pn_length

let parse32_long_initial_body : LP.parser32 Public.parse_long_initial_body =
    parse32_common_long `LP.parse32_nondep_then` (
      LP.parse32_bounded_vlgenbytes 0 0ul token_max_len (U32.uint_to_t token_max_len) (parse32_bounded_varint 0ul (U32.uint_to_t token_max_len)) `LP.parse32_nondep_then`
      parse32_payload_and_pn_length
    )

let parse32_long_retry_body : LP.parser32 Public.parse_long_retry_body =
  parse32_common_long `LP.parse32_nondep_then` LP.parse32_bounded_vlbytes 0 0ul 20 20ul  

#push-options "--z3rlimit 32 --max_fuel 8 --max_ifuel 8 --initial_fuel 8 --initial_ifuel 8"

let parse32_header_body
  (short_dcid_len: short_dcid_len_t)
  (x: LPB.bitsum'_key_type Public.first_byte)
: Tot (LP.parser32 (dsnd (Public.parse_header_body short_dcid_len x)))
= match x with
  | (| Public.Short, (| (), () |) |) ->
    LP.parse32_weaken (LP.strong_parser_kind 0 20 None) (LP.parse32_flbytes (U32.v short_dcid_len) short_dcid_len)
  | (| Public.Long, (| (), (| Public.Initial, () |) |) |) ->
    parse32_long_initial_body
  | (| Public.Long, (| (), (| Public.ZeroRTT, () |) |) |) ->
    parse32_long_zero_rtt_body
  | (| Public.Long, (| (), (| Public.Handshake, () |) |) |) ->
    parse32_long_handshake_body
  | (| Public.Long, (| (), (| Public.Retry, () |) |) |) ->
    parse32_long_retry_body

#pop-options

let parse32_public_header
  (short_dcid_len: short_dcid_len_t)
: Tot (LP.parser32 (Public.parse_header short_dcid_len))
= LPB.parse32_bitsum
    Public.first_byte
    (Public.first_byte_of_header short_dcid_len)
    (Public.header_body_type short_dcid_len)
    (Public.header_synth short_dcid_len)
    LP.parse32_u8
    (Public.parse_header_body short_dcid_len)
    (parse32_header_body short_dcid_len)

let serialize32_common_long : LP.serializer32 Public.serialize_common_long =
  LP.serialize32_u32 `LP.serialize32_nondep_then` (
    LP.serialize32_bounded_vlbytes 0 20 `LP.serialize32_nondep_then`
    LP.serialize32_bounded_vlbytes 0 20
  )

let serialize32_payload_and_pn_length : LP.serializer32 Public.serialize_payload_and_pn_length =
  LP.serialize32_filter
    serialize32_varint
    Public.payload_and_pn_length_prop

let serialize32_long_zero_rtt_body : LP.serializer32 Public.serialize_long_zero_rtt_body =
  serialize32_common_long `LP.serialize32_nondep_then` serialize32_payload_and_pn_length

let serialize32_long_handshake_body : LP.serializer32 Public.serialize_long_handshake_body =
  serialize32_common_long `LP.serialize32_nondep_then` serialize32_payload_and_pn_length

let serialize32_long_initial_body : LP.serializer32 Public.serialize_long_initial_body =
    serialize32_common_long `LP.serialize32_nondep_then` (
      LP.serialize32_bounded_vlgenbytes 0 token_max_len (serialize32_bounded_varint 0 (token_max_len)) `LP.serialize32_nondep_then`
      serialize32_payload_and_pn_length
    )

let serialize32_long_retry_body : LP.serializer32 Public.serialize_long_retry_body =
  serialize32_common_long `LP.serialize32_nondep_then` LP.serialize32_bounded_vlbytes 0 20  

#push-options "--z3rlimit 32 --max_fuel 8 --max_ifuel 8 --initial_fuel 8 --initial_ifuel 8"

let serialize32_header_body
  (short_dcid_len: short_dcid_len_t)
  (x: LPB.bitsum'_key_type Public.first_byte)
: Tot (LP.serializer32 (Public.serialize_header_body short_dcid_len x))
= match x with
  | (| Public.Short, (| (), () |) |) ->
    LP.serialize32_weaken (LP.strong_parser_kind 0 20 None) (LP.serialize32_flbytes (U32.v short_dcid_len))
  | (| Public.Long, (| (), (| Public.Initial, () |) |) |) ->
    serialize32_long_initial_body
  | (| Public.Long, (| (), (| Public.ZeroRTT, () |) |) |) ->
    serialize32_long_zero_rtt_body
  | (| Public.Long, (| (), (| Public.Handshake, () |) |) |) ->
    serialize32_long_handshake_body
  | (| Public.Long, (| (), (| Public.Retry, () |) |) |) ->
    serialize32_long_retry_body

#pop-options

let serialize32_public_header
  (short_dcid_len: short_dcid_len_t)
: Tot (LP.serializer32 (Public.serialize_header short_dcid_len))
= LPB.serialize32_bitsum
    Public.first_byte
    (Public.first_byte_of_header short_dcid_len)
    (Public.header_body_type short_dcid_len)
    (Public.header_synth short_dcid_len)
    LP.serialize32_u8
    #(Public.parse_header_body short_dcid_len)
    (Public.serialize_header_body short_dcid_len)
    (serialize32_header_body short_dcid_len)
    ()

#push-options "--z3rlimit 64"

let lp_parse32_header
  (short_dcid_len: short_dcid_len_t)
  (last: PN.last_packet_number_t)
: Tot (LP.parser32 (Parse.lp_parse_header short_dcid_len last))
= fun x ->
  Parse.lp_parse_header_eq short_dcid_len last (B32.reveal x); ((
  match parse32_public_header short_dcid_len x with
  | None -> None
  | Some (ph, consumed) ->
    if Public.is_retry ph
    then Some (Parse.synth_header short_dcid_len last (| ph, () |), consumed)
    else begin
      LP.parser32_consumes (parse32_public_header short_dcid_len) x;
      assert (U32.v consumed <= B32.length x);
      match parse32_packet_number last (Parse.get_pn_length ph) (B32.slice x consumed (B32.len x)) with
      | None -> None
      | Some (pn, consumed') ->
        Some (Parse.synth_header short_dcid_len last (| ph, pn |), consumed `U32.add` consumed')
    end
  ) <: (y: _ { LP.parser32_correct (Parse.lp_parse_header short_dcid_len last) x y } ))

#pop-options

let mk_short_protected_bits
  (reserved_bits: bitfield 2)
  (key_phase: bool)
  (pnl: PN.packet_number_length_t)
: Tot (y: bitfield 5 { y == Parse.mk_short_protected_bits reserved_bits key_phase pnl })
= BF.set_bitfield_bound #8 0 5 0 2 (Secret.v pnl - 1);
  BF.set_bitfield_bound #8 (BF.set_bitfield #8 0 0 2 (Secret.v pnl - 1)) 5 2 3 (if key_phase then 1 else 0);
  BF.set_bitfield_bound #8 (BF.set_bitfield #8 (BF.set_bitfield #8 0 0 2 (Secret.v pnl - 1)) 2 3 (if key_phase then 1 else 0)) 5 3 5 (U8.v reserved_bits);
  BF.uint8.BF.set_bitfield (BF.uint8.BF.set_bitfield (BF.uint8.BF.set_bitfield 0uy 0 2 (Declassify.u8_to_UInt8 (Secret.cast_down Secret.U8 (pnl `Secret.sub` Secret.to_u32 1ul)))) 2 3 (if key_phase then 1uy else 0uy)) 3 5 reserved_bits

let mk_long_protected_bits
  (reserved_bits: bitfield 2)
  (pnl: PN.packet_number_length_t)
: Tot (y: bitfield 4 { y == Parse.mk_long_protected_bits reserved_bits pnl })
= BF.set_bitfield_bound #8 0 4 0 2 (Secret.v pnl - 1);
  BF.set_bitfield_bound #8 (BF.set_bitfield #8 0 0 2 (Secret.v pnl - 1)) 4 2 4 (U8.v reserved_bits);
  BF.uint8.BF.set_bitfield (BF.uint8.BF.set_bitfield 0uy 0 2
    (Declassify.u8_to_UInt8 (Secret.cast_down Secret.U8 (pnl `Secret.sub` Secret.to_u32 1ul)))
  ) 2 4 reserved_bits

let synth_header_recip
  (short_dcid_len: short_dcid_len_t)
  (last: PN.last_packet_number_t)
  (x: Parse.header' short_dcid_len last)
: Tot (y: dtuple2 (Public.header' short_dcid_len) (Parse.packet_number_opt short_dcid_len last) { y == Parse.synth_header_recip short_dcid_len last x })
= match x with
  | MShort rb spin key_phase dcid pnl pn ->
    Parse.mk_short_protected_bits_correct rb key_phase pnl;
    (| Public.PShort (mk_short_protected_bits rb key_phase pnl) spin dcid, pn |)
  | MLong version dcid scid spec ->
    begin match spec with
    | MRetry unused odcid ->
      (| Public.PLong unused version dcid scid (Public.PRetry odcid), () |)
    | MInitial rb token payload_and_pn_length pnl pn ->
      Parse.mk_long_protected_bits_correct rb pnl;
      (| Public.PLong (mk_long_protected_bits rb pnl) version dcid scid (Public.PInitial token payload_and_pn_length), pn |)
    | MHandshake rb payload_and_pn_length pnl pn ->
      Parse.mk_long_protected_bits_correct rb pnl;
      (| Public.PLong (mk_long_protected_bits rb pnl) version dcid scid (Public.PHandshake payload_and_pn_length), pn |)
    | MZeroRTT rb payload_and_pn_length pnl pn ->
      Parse.mk_long_protected_bits_correct rb pnl;
      (| Public.PLong (mk_long_protected_bits rb pnl) version dcid scid (Public.PZeroRTT payload_and_pn_length), pn |)
    end

#push-options "--z3rlimit 128"

#restart-solver

let serialize32_header
  (short_dcid_len: short_dcid_len_t)
  (last: PN.last_packet_number_t)
: Tot (LP.serializer32 (Parse.serialize_header short_dcid_len last))
= fun h ->
  Parse.serialize_header_eq short_dcid_len last h;
    let (| ph, pn |) = synth_header_recip short_dcid_len last h in
    serialize32_public_header short_dcid_len ph `B32.append`
    (if is_retry h
     then B32.empty_bytes
     else serialize32_packet_number last (pn_length h) pn)

#pop-options

#push-options "--z3rlimit 16"

[@"opaque_to_smt"]
let parse_header
  (cid_len: nat { cid_len <= 20 })
  (last: nat { last + 1 < pow2 62 })
  (b:bytes)
: Tot (r: Parse.h_result { r == Parse.parse_header cid_len last b })
= match LP.parse_tot_seq_of_parser32 (lp_parse32_header (U32.uint_to_t cid_len) (Secret.to_u64 (U64.uint_to_t last))) b with
  | None -> Parse.H_Failure
  | Some (h, consumed) -> Parse.H_Success h (Seq.slice b consumed (Seq.length b))

#pop-options

[@"opaque_to_smt"]
let last_packet_number
  (h: header)
: Tot (y: PN.last_packet_number_t { y == Parse.last_packet_number h })
= if is_retry h then Secret.to_u64 0uL else let pn = packet_number h in
  if Declassify.uint_to_nat pn = 0 then Secret.to_u64 0uL else pn `Secret.sub` Secret.to_u64 1uL

[@"opaque_to_smt"]
let format_header
  (h: header)
: Tot (y: bytes { y == Parse.format_header h })
=
  Parse.in_window_last_packet_number h;
  LP.serialize_tot_seq_of_serializer32 (serialize32_header (U32.uint_to_t (dcid_len h)) (last_packet_number h)) h

(* header protection *)

[@"opaque_to_smt"]
irreducible
let rec seq_reveal'
  (x: Seq.seq Secret.uint8)
  (accu: Seq.seq byte)
: Tot (y: Seq.seq byte { y `Seq.equal` (accu `Seq.append` Seq.seq_reveal x) })
  (decreases (Seq.length x))
= if Seq.length x = 0
  then accu
  else (seq_reveal' (Seq.slice x 1 (Seq.length x)) (Seq.append accu (Seq.create 1 (Declassify.u8_to_UInt8 (Seq.index x 0)))) <: Seq.seq byte)

[@"opaque_to_smt"]
inline_for_extraction
let seq_reveal
  (x: Seq.seq Secret.uint8)
: Tot (y: Seq.seq byte { y `Seq.equal` Seq.seq_reveal x })
= seq_reveal' x Seq.empty

[@"opaque_to_smt"]
let block_of_sample
  (a: Cipher.cipher_alg)
  (k: Cipher.key a)
  (sample: Seq.lseq Secret.uint8 16)
: Tot (y: Seq.lseq Secret.uint8 16 { y == Header.block_of_sample a k sample })
=
  let open FStar.Mul in
  let ctr, iv = match a with
    | Cipher.CHACHA20 ->
        let ctr_bytes, iv = Seq.split sample 4 in
        FStar.Endianness.lemma_le_to_n_is_bounded (Seq.seq_reveal ctr_bytes);
        assert_norm (pow2 (8 * 4) = pow2 32);
        FStar.Endianness.le_to_n (seq_reveal ctr_bytes), iv
    | _ ->
        let iv, ctr_bytes = Seq.split sample 12 in
        FStar.Endianness.lemma_be_to_n_is_bounded (Seq.seq_reveal ctr_bytes);
        assert_norm (pow2 (8 * 4) = pow2 32);
        FStar.Endianness.be_to_n (seq_reveal ctr_bytes), iv
  in
  (Seq.slice (Cipher.ctr_block a k iv ctr) 0 16)

#push-options "--z3rlimit 16"

[@"opaque_to_smt"]
let pn_offset
  (h: header { ~ (is_retry h) })
: Tot (y: nat { y == Parse.pn_offset h })
= let cid_len = U32.uint_to_t (dcid_len h) in
  let last = last_packet_number h in
  let (| ph, _ |) = synth_header_recip cid_len last h in
  Seq.length (LP.serialize_tot_seq_of_serializer32 (serialize32_public_header cid_len) ph)

let header_encrypt
  (a:ea)
  (hpk: Cipher.key (AEAD.cipher_alg_of_supported_alg a))
  (h: header)
  (c: cbytes' (is_retry h))
: Tot (b: bytes { b == Header.header_encrypt a hpk h c })
=
  assert_norm(max_cipher_length < pow2 62);
  let r = format_header h `Seq.append` c in
  if is_retry h
  then
    r
  else
    let pn_offset = pn_offset h in
    let pn_len = Declassify.uint_to_nat (pn_length h) - 1 in
    let sample = Seq.seq_hide (Seq.slice c (3-pn_len) (19-pn_len)) in
    let mask = seq_reveal (block_of_sample (AEAD.cipher_alg_of_supported_alg a) hpk sample) in
    let pnmask = Lemmas.and_inplace (Seq.slice mask 1 (pn_len + 2)) (Header.pn_sizemask pn_len) 0 in
    let f = Seq.index r 0 in
    let protected_bits = if MShort? h then 5 else 4 in
    let f' = BF.set_bitfield (U8.v f) 0 protected_bits (BF.get_bitfield (U8.v f `FStar.UInt.logxor` U8.v (Seq.index mask 0)) 0 protected_bits) in
    let r = Lemmas.xor_inplace r pnmask pn_offset in
    let r = Seq.cons (U8.uint_to_t f') (Seq.slice r 1 (Seq.length r)) in
    r

[@"opaque_to_smt"]
let putative_pn_offset
  (cid_len: nat)
  (x: bytes)
: Tot (y: option nat { y == Parse.putative_pn_offset cid_len x })
= if cid_len > 20
  then None
  else
    match LP.parse_tot_seq_of_parser32 (parse32_public_header (U32.uint_to_t cid_len)) x with
    | None -> None
    | Some (_, consumed) ->
      LP.parser_kind_prop_equiv (Public.parse_header_kind (U32.uint_to_t cid_len)) (Public.parse_header (U32.uint_to_t cid_len));
      Some (consumed <: nat)

[@"opaque_to_smt"]
let header_decrypt_aux
  (a:ea)
  (hpk: Cipher.key (AEAD.cipher_alg_of_supported_alg a))
  (cid_len: nat { cid_len <= 20 })
  (packet: packet)
: Tot (y: option Header.header_decrypt_aux_t { y == Header.header_decrypt_aux a hpk cid_len packet })
= let open FStar.Math.Lemmas in
  if Seq.length packet = 0
  then None
  else
    let f = Seq.index packet 0 in
    let is_short = (BF.get_bitfield (U8.v f) 7 8 = 0) in
    let is_retry = not is_short && BF.get_bitfield (U8.v f) 4 6 = 3 in
    if is_retry
    then
      Some ({
        Header.is_short = is_short;
        Header.is_retry = is_retry;
        Header.packet = packet;
        Header.pn_offset = ();
        Header.pn_len = ();
      })
    else
      match putative_pn_offset cid_len packet with
      | None -> None
      | Some pn_offset ->
        let sample_offset = pn_offset + 4 in
        if sample_offset + 16 > Seq.length packet
        then None
        else begin
          let sample = Seq.seq_hide (Seq.slice packet sample_offset (sample_offset+16)) in
          let mask = seq_reveal (block_of_sample (AEAD.cipher_alg_of_supported_alg a) hpk sample) in
          (* mask the least significant bits of the first byte *)
          let protected_bits = if is_short then 5 else 4 in
          let f' = BF.set_bitfield (U8.v f) 0 protected_bits (BF.get_bitfield (U8.v f `FStar.UInt.logxor` U8.v (Seq.index mask 0)) 0 protected_bits) in
          let packet' = Seq.cons (U8.uint_to_t f') (Seq.slice packet 1 (Seq.length packet)) in
          (* now the packet number length is available, so mask the packet number *)
          let pn_len = BF.get_bitfield f' 0 2 in
          let pnmask = Lemmas.and_inplace (Seq.slice mask 1 (pn_len + 2)) (Header.pn_sizemask pn_len) 0 in
          let packet'' = Lemmas.xor_inplace packet' pnmask pn_offset in
          Some ({
            Header.is_short = is_short;
            Header.is_retry = is_retry;
            Header.packet = packet'';
            Header.pn_offset = pn_offset;
            Header.pn_len = pn_len;
          })
        end

#pop-options

#push-options "--z3rlimit 32"

#restart-solver

[@"opaque_to_smt"]
let header_decrypt
  (a:ea)
  (hpk: Cipher.key (AEAD.cipher_alg_of_supported_alg a))
  (cid_len: nat { cid_len <= 20 })
  (last: nat { last + 1 < pow2 62 })
  (packet: packet)
: Tot (r: Header.h_result { r == Header.header_decrypt a hpk cid_len last packet })
=
  let open FStar.Math.Lemmas in
  if Seq.length packet = 0
  then Header.H_Failure
  else
    match header_decrypt_aux a hpk cid_len packet with
    | None -> Header.H_Failure
    | Some r ->
      let packet'' = r.Header.packet in
      begin match parse_header cid_len last packet'' with
      | Parse.H_Failure -> Header.H_Failure
      | Parse.H_Success h rem' ->
        Header.header_decrypt_aux_post_parse a hpk cid_len last packet;
        if is_retry h
        then
          Header.H_Success h Seq.empty rem'
        else
          let clen = if has_payload_length h then Declassify.uint_to_nat (payload_length h) else Seq.length rem' in
          assert_norm (16 < max_cipher_length - 1);
          (* payload_length is secret, so, to stay constant-time, we
          must not check for failure. Instead, we compute some length
          that might be garbage if bounds on payload_length do not hold. *)
          let clen = Header.max (Header.min (Header.min clen (Seq.length rem')) (max_cipher_length - 1)) 16 in
          assert (clen < max_cipher_length);
          assert (clen <= Seq.length rem');
          assert (16 <= clen);
          let c = Seq.slice rem' 0 clen in
          let rem = Seq.slice rem' clen (Seq.length rem') in
          Header.H_Success h c rem
      end

#pop-options

(* header and packet protection *)

[@"opaque_to_smt"]
let iv_for_encrypt_decrypt
  (a: ea)
  (siv: Spec.iv_t a)
  (h: header { ~ (is_retry h) })
: Tot (y: Spec.iv_t a { y == Spec.iv_for_encrypt_decrypt a siv h })
=
  let pn_len = Declassify.uint_to_nat (pn_length h) - 1 in
  let seqn = packet_number h in
  let _ = assert_norm(pow2 62 < pow2 (8 `op_Multiply` 12)) in
  let pnb = FStar.Endianness.n_to_be 12 (Declassify.uint_to_nat seqn) in
  Seq.seq_hide #Secret.U8 (Lemmas.xor_inplace pnb (seq_reveal siv) 0)

#push-options "--z3rlimit 16"

[@"opaque_to_smt"]
let payload_encrypt
  (a: ea)
  (k: AEAD.kv a)
  (siv: Spec.iv_t a)
  (h: header { ~ (is_retry h) })
  (plain: pbytes)
: Tot (y: bytes { y == Spec.payload_encrypt a k siv h plain })
=
  let aad = format_header h in
  let iv = iv_for_encrypt_decrypt a siv h in
  seq_reveal (AEAD.encrypt #a k iv (Seq.seq_hide aad) (Seq.seq_hide plain))

let encrypt
  a k siv hpk h plain
=
  let cipher =
    if is_retry h
    then plain
    else payload_encrypt a k siv h plain
  in
  header_encrypt a hpk h cipher

[@"opaque_to_smt"]
let payload_decrypt
  (a: ea)
  (k: AEAD.kv a)
  (siv: Spec.iv_t a)
  (h: header { ~ (is_retry h) })
  (c: Seq.seq Secret.uint8 { 16 <= Seq.length c /\ Seq.length c < max_cipher_length })
: Tot (y: option (AEAD.decrypted c) { y == Spec.payload_decrypt a k siv h c })
= 
  let iv = iv_for_encrypt_decrypt a siv h in
  let aad = format_header h in
  AEAD.decrypt #a k iv (Seq.seq_hide aad) c

let decrypt
  a k siv hpk last cid_len packet
=
  let open FStar.Math.Lemmas in
  let open FStar.Endianness in
  match header_decrypt a hpk cid_len last packet with
  | Header.H_Failure -> Spec.Failure
  | Header.H_Success h c rem ->
    if is_retry h
    then Spec.Success h c rem
    else
      match payload_decrypt a k siv h (Seq.seq_hide c) with
      | None -> Spec.Failure
      | Some plain -> Spec.Success h (seq_reveal plain) rem

#pop-options
