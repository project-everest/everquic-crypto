module QUIC.Impl.Header
friend QUIC.Spec.Header

open QUIC.Impl.Base
open QUIC.Spec.Header

open QUIC.Impl.PacketNumber

open FStar.HyperStack.ST

open LowParse.Spec.Int
open LowParse.Spec.BitSum

open LowParse.Spec.BoundedInt

module U64 = FStar.UInt64
module U32 = FStar.UInt32
module U16 = FStar.UInt16
module U8 = FStar.UInt8

module FB = FStar.Bytes
open LowParse.Spec.Bytes

module LC = LowParse.Low.Combinators
module LB = LowParse.Low.Bytes
module LI = LowParse.Low.BoundedInt
module LJ = LowParse.Low.Int
module LL = LowParse.Low.BitSum

open QUIC.Impl.VarInt

inline_for_extraction
let validate_common_long : LC.validator parse_common_long =
  LB.validate_u32 () `LC.validate_nondep_then` (LB.validate_bounded_vlbytes 0 20 `LC.validate_nondep_then` LB.validate_bounded_vlbytes 0 20)

inline_for_extraction
noextract
let validate_payload_length_pn
  (last: last_packet_number_t)
  (pn_length: packet_number_length_t)
: Tot (LC.validator (parse_payload_length_pn last pn_length))
= validate_varint `LC.validate_nondep_then` validate_packet_number last pn_length

#push-options "--z3rlimit 64 --max_fuel 8 --max_ifuel 8 --initial_fuel 8 --initial_ifuel 8"

[@filter_bitsum'_t_attr]
inline_for_extraction
noextract
let validate_header_body_cases
  (short_dcid_len: short_dcid_len_t)
  (last: last_packet_number_t)
  (k' : bitsum'_key_type first_byte)
: Tot (LC.validator (dsnd (parse_header_body short_dcid_len last k')))
= match coerce (bitsum'_key_type first_byte) k' with
  | (| Short, (| (), (| (), (| pn_length, () |) |) |) |) ->
    LC.validate_weaken (strong_parser_kind 0 20 None) (LB.validate_flbytes (U32.v short_dcid_len) short_dcid_len) () `LC.validate_nondep_then` validate_packet_number last pn_length
  | (| Long, (| (), (| Initial, (| (), (| pn_length, () |) |) |) |) |) ->
    validate_common_long `LC.validate_nondep_then` (LB.validate_bounded_vlgenbytes 0 0ul token_max_len (U32.uint_to_t token_max_len) (validate_bounded_varint 0ul (U32.uint_to_t token_max_len)) (read_bounded_varint 0 token_max_len) `LC.validate_nondep_then` validate_payload_length_pn last pn_length)
  | (| Long, (| (), (| ZeroRTT, (| (), (| pn_length, () |) |) |) |) |) ->
    validate_common_long `LC.validate_nondep_then` validate_payload_length_pn last pn_length
  | (| Long, (| (), (| Handshake, (| (), (| pn_length, () |) |) |) |) |) ->
    validate_common_long `LC.validate_nondep_then` validate_payload_length_pn last pn_length
  | (| Long, (| (), (| Retry, () |) |) |) ->
    validate_common_long `LC.validate_nondep_then` LB.validate_bounded_vlbytes 0 20

#pop-options

let filter_first_byte'
: (filter_bitsum'_t first_byte)
= norm [primops; iota; zeta; delta_attr [`%filter_bitsum'_t_attr]]
  (mk_filter_bitsum'_t' first_byte)

inline_for_extraction
let filter_first_byte
  (short_dcid_len: short_dcid_len_t)
  (last: last_packet_number_t)
: Tot (filter_bitsum'_t first_byte)
= coerce (filter_bitsum'_t first_byte) filter_first_byte'

inline_for_extraction
noextract
let mk_validate_header_body_cases'
: LL.validate_bitsum_cases_t first_byte
= norm [primops; iota; zeta; delta_attr [`%filter_bitsum'_t_attr]]
  (LL.mk_validate_bitsum_cases_t' first_byte)

inline_for_extraction
noextract
let mk_validate_header_body_cases
  (short_dcid_len: short_dcid_len_t)
  (last: last_packet_number_t)
: LL.validate_bitsum_cases_t first_byte
= coerce (LL.validate_bitsum_cases_t first_byte) mk_validate_header_body_cases' 

let validate_header
  (short_dcid_len: short_dcid_len_t)
  (last: last_packet_number_t)
: Tot (LL.validator (lp_parse_header short_dcid_len last))
= LL.validate_bitsum
    first_byte
    (first_byte_of_header short_dcid_len last)
    (header_body_type short_dcid_len last)
    (header_synth short_dcid_len last)
    (LJ.validate_u8 ())
    LJ.read_u8
    (filter_first_byte short_dcid_len last)
    (parse_header_body short_dcid_len last)
    (validate_header_body_cases short_dcid_len last)
    (mk_validate_header_body_cases short_dcid_len last)


module Impl = QUIC.Impl.Base

inline_for_extraction
noextract
let destr_first_byte
: (destr_bitsum'_t first_byte)
= norm [primops; iota; zeta; delta_attr [`%filter_bitsum'_t_attr]]
  (mk_destr_bitsum'_t first_byte)

inline_for_extraction
noextract
let read_header_body_t
  (sl: LL.slice (B.trivial_preorder _) (B.trivial_preorder _))
  (cid_len: U32.t { U32.v cid_len < 20 } )
  (last: uint62_t { U64.v last + 1 < pow2 62 })
  (tg: bitsum'_type first_byte)
: Tot (Type u#0)
= (len: U32.t) ->
  HST.Stack Impl.header
  (requires (fun h ->
    let p = dsnd (parse_header_body cid_len last (bitsum'_key_of_t first_byte tg)) in
    LL.valid_pos (lp_parse_header cid_len last) h sl 0ul len /\
    1 <= U32.v sl.LL.len /\
    LL.valid_pos p h sl 1ul len /\
    LL.contents (lp_parse_header cid_len last) h sl 0ul == (header_synth cid_len last).f tg (LL.contents p h sl 1ul)
  ))
  (ensures (fun h x h' ->
    B.modifies B.loc_none h h' /\
    begin
      let hd = LL.contents (lp_parse_header cid_len last) h sl 0ul in
      Impl.header_live x h' /\
      LL.loc_slice_from_to sl 0ul len `B.loc_includes` Impl.header_footprint x /\
      Impl.g_header x h' == hd
    end
  ))

module BF = LowParse.BitFields

#push-options "--z3rlimit 64 --z3cliopt smt.arith.nl=false --using_facts_from '*,-FStar.Int.Cast' --query_stats --max_fuel 9 --initial_fuel 9 --max_ifuel 9 --initial_ifuel 9 --query_stats"

let read_header_body_short
  (sl: LL.slice (B.trivial_preorder _) (B.trivial_preorder _))
  (cid_len: U32.t { U32.v cid_len < 20 } )
  (last: uint62_t { U64.v last + 1 < pow2 62 })
  (spin: BF.bitfield uint8 1)
  (key_phase: BF.bitfield uint8 1)
  (pn_length: packet_number_length_t)
: Tot (read_header_body_t sl cid_len last (| Short, (| (), (spin, (| (), (key_phase, (| pn_length, () |) ) |) ) |) |) )
= fun len ->
    let h0 = HST.get () in
    assert_norm (bitsum'_key_of_t first_byte (| Short, (| (), (spin, (| (), (key_phase, (| pn_length, () |) ) |) ) |) |) == (| Short, (| (), (| (), (| pn_length, () |) |) |) |) );
    LL.valid_nondep_then h0 (weaken (strong_parser_kind 0 20 None) (parse_flbytes (U32.v cid_len))) (parse_packet_number last pn_length) sl 1ul;
    LL.valid_weaken (strong_parser_kind 0 20 None) (parse_flbytes (U32.v cid_len)) h0 sl 1ul;
    LB.valid_flbytes_elim h0 (U32.v cid_len) sl 1ul;
    let pos = LB.jump_flbytes (U32.v cid_len) cid_len sl 1ul in
    let dcid = B.sub sl.LL.base 1ul (pos `U32.sub` 1ul) in
    let pn = read_packet_number last pn_length sl pos in
    Impl.BShort (spin = 1uy) (key_phase = 1uy) dcid cid_len pn pn_length

#pop-options

#push-options "--z3rlimit 128 --z3cliopt smt.arith.nl=false --using_facts_from '*,-FStar.Int.Cast' --query_stats --max_fuel 9 --initial_fuel 9 --max_ifuel 9 --initial_ifuel 9 --query_stats"

#restart-solver

let read_header_body_long_retry
  (sl: LL.slice (B.trivial_preorder _) (B.trivial_preorder _))
  (cid_len: U32.t { U32.v cid_len < 20 } )
  (last: uint62_t { U64.v last + 1 < pow2 62 })
  (unused: BF.bitfield uint8 4)
: Tot (read_header_body_t sl cid_len last (| Long, (| (), (| Retry, (unused, ()) |) |) |) )
= fun len ->
    let h0 = HST.get () in
    assert_norm (bitsum'_key_of_t first_byte (| Long, (| (), (| Retry, (unused, ()) |) |) |)  == (| Long, (| (), (| Retry, () |) |) |) );
    LL.valid_nondep_then h0 parse_common_long (parse_bounded_vlbytes 0 20) sl 1ul;
    LL.valid_nondep_then h0 parse_u32 (parse_bounded_vlbytes 0 20 `nondep_then` parse_bounded_vlbytes 0 20) sl 1ul;
    let version = LJ.read_u32 sl 1ul in
    let pos1 = LJ.jump_u32 sl 1ul in
    LL.valid_nondep_then h0 (parse_bounded_vlbytes 0 20) (parse_bounded_vlbytes 0 20) sl pos1;
    let dcid = LB.get_vlbytes_contents 0 20 sl pos1 in
    let dcid_len = LB.bounded_vlbytes_payload_length 0 20 sl pos1 in
    let pos2 = LB.jump_bounded_vlbytes 0 20 sl pos1 in
    let scid = LB.get_vlbytes_contents 0 20 sl pos2 in
    let scid_len = LB.bounded_vlbytes_payload_length 0 20 sl pos2 in
    let pos3 = LB.jump_bounded_vlbytes 0 20 sl pos2 in
    let odcid = LB.get_vlbytes_contents 0 20 sl pos3 in
    let odcid_len = LB.bounded_vlbytes_payload_length 0 20 sl pos3 in
    let spec = Impl.BRetry unused odcid odcid_len in
    Impl.BLong version dcid dcid_len scid scid_len spec

#pop-options

#push-options "--z3rlimit 512 --z3cliopt smt.arith.nl=false --using_facts_from '*,-FStar.Int.Cast' --query_stats --max_fuel 9 --initial_fuel 9 --max_ifuel 9 --initial_ifuel 9 --query_stats"

#restart-solver

let read_header_body_long_initial
  (sl: LL.slice (B.trivial_preorder _) (B.trivial_preorder _))
  (cid_len: U32.t { U32.v cid_len < 20 } )
  (last: uint62_t { U64.v last + 1 < pow2 62 })
  (pn_length: packet_number_length_t)
: Tot (read_header_body_t sl cid_len last (| Long, (| (), (| Initial, (| (), (| pn_length, () |) |) |) |) |) )
= fun len ->
    let h0 = HST.get () in
    assert_norm (bitsum'_key_of_t first_byte (| Long, (| (), (| Initial, (| (), (| pn_length, () |) |) |) |) |) == (| Long, (| (), (| Initial, (| (), (| pn_length, () |) |) |) |) |) );
    LL.valid_nondep_then h0 parse_common_long (parse_bounded_vlgenbytes 0 token_max_len (parse_bounded_varint 0 token_max_len) `nondep_then` parse_payload_length_pn last pn_length) sl 1ul;
    LL.valid_nondep_then h0 parse_u32 (parse_bounded_vlbytes 0 20 `nondep_then` parse_bounded_vlbytes 0 20) sl 1ul;
    let version = LJ.read_u32 sl 1ul in
    let pos1 = LJ.jump_u32 sl 1ul in
    LL.valid_nondep_then h0 (parse_bounded_vlbytes 0 20) (parse_bounded_vlbytes 0 20) sl pos1;
    let dcid = LB.get_vlbytes_contents 0 20 sl pos1 in
    let dcid_len = LB.bounded_vlbytes_payload_length 0 20 sl pos1 in
    let pos2 = LB.jump_bounded_vlbytes 0 20 sl pos1 in
    let scid = LB.get_vlbytes_contents 0 20 sl pos2 in
    let scid_len = LB.bounded_vlbytes_payload_length 0 20 sl pos2 in
    let pos3 = LB.jump_bounded_vlbytes 0 20 sl pos2 in
    LL.valid_nondep_then h0 (parse_bounded_vlgenbytes 0 token_max_len (parse_bounded_varint 0 token_max_len)) (parse_payload_length_pn last pn_length) sl pos3;
    let token = LB.get_bounded_vlgenbytes_contents 0 token_max_len (read_bounded_varint 0 token_max_len) (jump_bounded_varint 0 token_max_len) sl pos3 in
    let token_len = LB.bounded_vlgenbytes_payload_length 0 token_max_len (read_bounded_varint 0 token_max_len) sl pos3 in
    let pos4 = LB.jump_bounded_vlgenbytes 0 token_max_len (jump_bounded_varint 0 token_max_len) (read_bounded_varint 0 token_max_len) sl pos3 in
    LL.valid_nondep_then h0 parse_varint (parse_packet_number last pn_length) sl pos4;
    let payload_length = read_varint sl pos4 in
    let pos5 = jump_varint sl pos4 in
    let pn = read_packet_number last pn_length sl pos5 in
//    assert (LL.loc_slice_from_to sl 0ul len `B.loc_includes` B.loc_buffer token);
    let spec = Impl.BInitial payload_length pn pn_length token token_len in
    Impl.BLong version dcid dcid_len scid scid_len spec

#pop-options

#push-options "--z3rlimit 256 --z3cliopt smt.arith.nl=false --using_facts_from '*,-FStar.Int.Cast' --query_stats --max_fuel 9 --initial_fuel 9 --max_ifuel 9 --initial_ifuel 9 --query_stats"

#restart-solver

let read_header_body_long_handshake
  (sl: LL.slice (B.trivial_preorder _) (B.trivial_preorder _))
  (cid_len: U32.t { U32.v cid_len < 20 } )
  (last: uint62_t { U64.v last + 1 < pow2 62 })
  (pn_length: packet_number_length_t)
: Tot (read_header_body_t sl cid_len last (| Long, (| (), (| Handshake, (| (), (| pn_length, () |) |) |) |) |) )
= fun len ->
    let h0 = HST.get () in
    assert_norm (bitsum'_key_of_t first_byte (| Long, (| (), (| Handshake, (| (), (| pn_length, () |) |) |) |) |) == (| Long, (| (), (| Handshake, (| (), (| pn_length, () |) |) |) |) |) );
    LL.valid_nondep_then h0 parse_common_long (parse_payload_length_pn last pn_length) sl 1ul;
    LL.valid_nondep_then h0 parse_u32 (parse_bounded_vlbytes 0 20 `nondep_then` parse_bounded_vlbytes 0 20) sl 1ul;
    let version = LJ.read_u32 sl 1ul in
    let pos1 = LJ.jump_u32 sl 1ul in
    LL.valid_nondep_then h0 (parse_bounded_vlbytes 0 20) (parse_bounded_vlbytes 0 20) sl pos1;
    let dcid = LB.get_vlbytes_contents 0 20 sl pos1 in
    let dcid_len = LB.bounded_vlbytes_payload_length 0 20 sl pos1 in
    let pos2 = LB.jump_bounded_vlbytes 0 20 sl pos1 in
    let scid = LB.get_vlbytes_contents 0 20 sl pos2 in
    let scid_len = LB.bounded_vlbytes_payload_length 0 20 sl pos2 in
    let pos3 = LB.jump_bounded_vlbytes 0 20 sl pos2 in
    LL.valid_nondep_then h0 parse_varint (parse_packet_number last pn_length) sl pos3;
    let payload_length = read_varint sl pos3 in
    let pos4 = jump_varint sl pos3 in
    let pn = read_packet_number last pn_length sl pos4 in
    let spec = Impl.BHandshake payload_length pn pn_length in
    Impl.BLong version dcid dcid_len scid scid_len spec

#restart-solver

let read_header_body_long_ZeroRTT
  (sl: LL.slice (B.trivial_preorder _) (B.trivial_preorder _))
  (cid_len: U32.t { U32.v cid_len < 20 } )
  (last: uint62_t { U64.v last + 1 < pow2 62 })
  (pn_length: packet_number_length_t)
: Tot (read_header_body_t sl cid_len last (| Long, (| (), (| ZeroRTT, (| (), (| pn_length, () |) |) |) |) |) )
= fun len ->
    let h0 = HST.get () in
    assert_norm (bitsum'_key_of_t first_byte (| Long, (| (), (| ZeroRTT, (| (), (| pn_length, () |) |) |) |) |) == (| Long, (| (), (| ZeroRTT, (| (), (| pn_length, () |) |) |) |) |) );
    LL.valid_nondep_then h0 parse_common_long (parse_payload_length_pn last pn_length) sl 1ul;
    LL.valid_nondep_then h0 parse_u32 (parse_bounded_vlbytes 0 20 `nondep_then` parse_bounded_vlbytes 0 20) sl 1ul;
    let version = LJ.read_u32 sl 1ul in
    let pos1 = LJ.jump_u32 sl 1ul in
    LL.valid_nondep_then h0 (parse_bounded_vlbytes 0 20) (parse_bounded_vlbytes 0 20) sl pos1;
    let dcid = LB.get_vlbytes_contents 0 20 sl pos1 in
    let dcid_len = LB.bounded_vlbytes_payload_length 0 20 sl pos1 in
    let pos2 = LB.jump_bounded_vlbytes 0 20 sl pos1 in
    let scid = LB.get_vlbytes_contents 0 20 sl pos2 in
    let scid_len = LB.bounded_vlbytes_payload_length 0 20 sl pos2 in
    let pos3 = LB.jump_bounded_vlbytes 0 20 sl pos2 in
    LL.valid_nondep_then h0 parse_varint (parse_packet_number last pn_length) sl pos3;
    let payload_length = read_varint sl pos3 in
    let pos4 = jump_varint sl pos3 in
    let pn = read_packet_number last pn_length sl pos4 in
    let spec = Impl.BZeroRTT payload_length pn pn_length in
    Impl.BLong version dcid dcid_len scid scid_len spec

inline_for_extraction
noextract
let read_header_body
  (sl: LL.slice (B.trivial_preorder _) (B.trivial_preorder _))
  (cid_len: U32.t { U32.v cid_len < 20 } )
  (last: uint62_t { U64.v last + 1 < pow2 62 })
  (tg: bitsum'_type first_byte)
: Tot (read_header_body_t sl cid_len last tg)
= fun len ->
  let h0 = HST.get () in
  match tg with
  | (| Short, (| (), (spin, (| (), (key_phase, (| pn_length, () |) ) |) ) |) |) ->
    read_header_body_short sl cid_len last spin key_phase pn_length len
  | (| Long, (| (), (| Retry, (unused, ()) |) |) |) ->
    read_header_body_long_retry sl cid_len last unused len
  | (| Long, (| (), (| Initial, (| (), (| pn_length, () |) |) |) |) |) ->
    read_header_body_long_initial sl cid_len last pn_length len
  | (| Long, (| (), (| Handshake, (| (), (| pn_length, () |) |) |) |) |) ->
    read_header_body_long_handshake sl cid_len last pn_length len
  | (| Long, (| (), (| ZeroRTT, (| (), (| pn_length, () |) |) |) |) |) ->
    read_header_body_long_ZeroRTT sl cid_len last pn_length len

#pop-options

#restart-solver

#push-options "--z3rlimit 128 --z3cliopt smt.arith.nl=false --using_facts_from '*,-FStar.Int.Cast' --query_stats"

let read_header
  packet packet_len cid_len last
=
  let h0 = HST.get () in
  let sl = LL.make_slice packet packet_len in
  LL.valid_facts (lp_parse_header cid_len last) h0 sl 0ul;
  assert (B.as_seq h0 packet `Seq.equal` LL.bytes_of_slice_from h0 sl 0ul);
  let len = validate_header cid_len last sl 0ul in
  if len `U32.gt` LL.validator_max_length
  then None
  else begin
    let g = Ghost.hide (LL.contents (lp_parse_header cid_len last) h0 sl 0ul) in
    LL.valid_bitsum_elim
      #parse_u8_kind
      #8
      #U8.t
      #uint8
      first_byte
      #(header' cid_len last)
      (first_byte_of_header cid_len last)
      (header_body_type cid_len last)
      (header_synth cid_len last)
      parse_u8
      (parse_header_body cid_len last)
      h0
      sl
      0ul;
    let r = LJ.read_u8 sl 0ul in
    let res = destr_first_byte
      (read_header_body_t sl cid_len last)
      (fun _ cond dt df len' -> if cond then dt () len' else df () len')
      (read_header_body sl cid_len last)
      r
      len
    in
    lemma_header_parsing_post (U32.v cid_len) (U64.v last) (LL.bytes_of_slice_from h0 sl 0ul);
    Some (res, len)
  end

let write_header
  dst x
=
  admit ()

let putative_pn_offset
  cid_len b len
=
  let sl = LowParse.Slice.make_slice b len in
  let h0 = HST.get () in
  if not (1ul `U32.lte` cid_len && cid_len `U32.lte` 4ul)
  then 0ul
  else
    let _ = LL.valid_facts parse_u8 h0 sl 0ul in
    let pos1 = LJ.validate_u8 () sl 0ul in
    if pos1 `U32.gt` LL.validator_max_length
    then 0ul
    else
      let _ =
        parser_kind_prop_equiv parse_u8_kind parse_u8;
        assert (pos1 == 1ul)
      in
      let hd = LJ.read_u8 sl 0ul in
      if uint8.get_bitfield hd 7 8 = 0uy
      then
        let _ = LL.valid_facts (parse_bounded_integer (U32.v cid_len)) h0 sl pos1 in
        let pos2 = LI.validate_bounded_integer' cid_len sl pos1 in
        if pos2 `U32.gt` LL.validator_max_length
        then 0ul
        else pos2
      else
        let packet_type = uint8.get_bitfield hd 4 6 in
        if packet_type = 3uy
        then 0ul
        else
          let _ = LL.valid_facts parse_common_long h0 sl pos1 in
          let pos2 = validate_common_long sl pos1 in
          if pos2 `U32.gt` LL.validator_max_length
          then 0ul
          else
            let pos3 =
              if packet_type = 0uy
              then
                let _ = LL.valid_facts (parse_bounded_vlgenbytes 0 token_max_len (parse_bounded_varint 0 token_max_len)) h0 sl pos2 in
                let pos3 = LB.validate_bounded_vlgenbytes 0 0ul token_max_len (U32.uint_to_t token_max_len) (validate_bounded_varint 0ul (U32.uint_to_t token_max_len)) (read_bounded_varint 0 token_max_len) sl pos2 in
                if pos3 `U32.gt` LL.validator_max_length
                then 0ul
                else pos3
              else
                pos2
            in
            if pos3 = 0ul
            then 0ul
            else
              let _ = LL.valid_facts parse_varint h0 sl pos3 in
              let pos4 = validate_varint sl pos3 in
              if pos4 `U32.gt` LL.validator_max_length
              then 0ul
              else pos4

let pn_offset
  h
= admit ()

let header_len_correct
  h m
= admit ()
