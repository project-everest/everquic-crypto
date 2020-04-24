module QUIC.Impl.Public
open QUIC.Spec.Public
friend QUIC.Spec.Public

module LP = LowParse.Low

inline_for_extraction
let validate_common_long : LP.validator parse_common_long =
  LP.validate_u32 () `LP.validate_nondep_then` (LP.validate_bounded_vlbytes 0 20 `LP.validate_nondep_then` LP.validate_bounded_vlbytes 0 20)

module VI = QUIC.Impl.VarInt

inline_for_extraction
let validate_payload_and_pn_length : LP.validator parse_payload_and_pn_length =
  LP.validate_filter
    VI.validate_varint
    VI.read_varint
    payload_and_pn_length_prop
    (fun x -> payload_and_pn_length_prop x)

inline_for_extraction
let validate_long_zero_rtt_body : LP.validator parse_long_zero_rtt_body =
  validate_common_long `LP.validate_nondep_then` validate_payload_and_pn_length

inline_for_extraction
let validate_long_handshake_body : LP.validator parse_long_handshake_body =
  validate_common_long `LP.validate_nondep_then` validate_payload_and_pn_length

inline_for_extraction
let validate_long_retry_body : LP.validator parse_long_retry_body =
  validate_common_long `LP.validate_nondep_then` LP.validate_bounded_vlbytes 0 20

inline_for_extraction
let validate_long_initial_body : LP.validator parse_long_initial_body =
  validate_common_long `LP.validate_nondep_then` (LP.validate_bounded_vlgenbytes 0 0ul token_max_len (U32.uint_to_t token_max_len) (VI.validate_bounded_varint 0ul (U32.uint_to_t token_max_len)) (VI.read_bounded_varint 0 token_max_len) `LP.validate_nondep_then` validate_payload_and_pn_length)

module LPB = LowParse.Low.BitSum

#push-options "--z3rlimit 32 --max_fuel 8 --max_ifuel 8 --initial_fuel 8 --initial_ifuel 8"

[@LPB.filter_bitsum'_t_attr]
inline_for_extraction
noextract
let validate_header_body_cases
  (short_dcid_len: short_dcid_len_t)
  (k' : LPB.bitsum'_key_type first_byte)
: Tot (LP.validator (dsnd (parse_header_body short_dcid_len k')))
= match LP.coerce (LPB.bitsum'_key_type first_byte) k' with
  | (| Short, (| (), () |) |) ->
    LP.validate_weaken (LP.strong_parser_kind 0 20 None) (LP.validate_flbytes (U32.v short_dcid_len) short_dcid_len) ()
  | (| Long, (| (), (| Initial, () |) |) |) ->
    validate_long_initial_body
  | (| Long, (| (), (| ZeroRTT, () |) |) |) ->
    validate_long_zero_rtt_body
  | (| Long, (| (), (| Handshake, () |) |) |) ->
    validate_long_handshake_body
  | (| Long, (| (), (| Retry, () |) |) |) ->
    validate_long_retry_body

inline_for_extraction
noextract
let filter_first_byte
: (LPB.filter_bitsum'_t first_byte)
= norm [primops; iota; zeta; delta_attr [`%LPB.filter_bitsum'_t_attr]]
  (LPB.mk_filter_bitsum'_t' first_byte)

inline_for_extraction
noextract
let mk_validate_header_body_cases
: LPB.validate_bitsum_cases_t first_byte
= norm [primops; iota; zeta; delta_attr [`%LPB.filter_bitsum'_t_attr]]
  (LPB.mk_validate_bitsum_cases_t' first_byte)

let validate_header
  (short_dcid_len: short_dcid_len_t)
: Tot (LP.validator (parse_header short_dcid_len))
= LPB.validate_bitsum
    first_byte
    (first_byte_of_header short_dcid_len)
    (header_body_type short_dcid_len)
    (header_synth short_dcid_len)
    (LP.validate_u8 ())
    LP.read_u8
    (filter_first_byte)
    (parse_header_body short_dcid_len)
    (validate_header_body_cases short_dcid_len)
    (mk_validate_header_body_cases)

inline_for_extraction
noextract
let destr_first_byte
: (LPB.destr_bitsum'_t first_byte)
= norm [primops; iota; zeta; delta_attr [`%LPB.filter_bitsum'_t_attr]]
  (LPB.mk_destr_bitsum'_t first_byte)


(* Length computations need to be transparent because the precondition
to QUIC.Impl.encrypt requires the user to provide a destination buffer
large enough to contain the byte representation of the header *)

let read_header_body_post
  (sl: LP.slice (B.trivial_preorder _) (B.trivial_preorder _))
  (cid_len: U32.t { U32.v cid_len <= 20 } )
  (tg: LPB.bitsum'_type first_byte)
  (h: HS.mem)
  (x: header)
  (h' : HS.mem)
: GTot Type0
= LP.valid (parse_header cid_len) h sl 0ul /\ (
    let hd = LP.contents (parse_header cid_len) h sl 0ul in
    let len = LP.get_valid_pos (parse_header cid_len) h sl 0ul in
    header_live x h' /\
    LP.loc_slice_from_to sl 0ul len `B.loc_includes` header_footprint x /\
    g_header x h' == hd
    )

inline_for_extraction
noextract
let read_header_body_t
  (sl: LP.slice (B.trivial_preorder _) (B.trivial_preorder _))
  (cid_len: U32.t { U32.v cid_len <= 20 } )
  (tg: LPB.bitsum'_type first_byte)
: Tot (Type u#0)
= unit ->
  HST.Stack header
  (requires (fun h ->
    let p = dsnd (parse_header_body cid_len (LPB.bitsum'_key_of_t first_byte tg)) in
    LP.valid (parse_header cid_len) h sl 0ul /\ (
    let len = LP.get_valid_pos (parse_header cid_len) h sl 0ul in
    1 <= U32.v sl.LP.len /\
    LP.valid_pos p h sl 1ul len /\
    LP.contents (parse_header cid_len) h sl 0ul == (header_synth cid_len).LPB.f tg (LP.contents p h sl 1ul)
  )))
  (ensures (fun h x h' ->
    B.modifies B.loc_none h h' /\
    read_header_body_post sl cid_len tg h x h'
  ))

#push-options "--z3rlimit 64 --z3cliopt smt.arith.nl=false --using_facts_from '*,-FStar.Int.Cast' --query_stats --max_fuel 9 --initial_fuel 9 --max_ifuel 9 --initial_ifuel 9 --query_stats"

let read_header_body_short
  (sl: LP.slice (B.trivial_preorder _) (B.trivial_preorder _))
  (cid_len: U32.t { U32.v cid_len <= 20 } )
  (spin: LPB.bitfield LPB.uint8 1)
  (protected_bits: LPB.bitfield LPB.uint8 5)
: Tot (read_header_body_t sl cid_len (| Short, (| (), (spin, (protected_bits, () ) ) |) |) )
= fun len ->
    let h0 = HST.get () in
    assert_norm (LPB.bitsum'_key_of_t first_byte (| Short, (| (), (spin, (protected_bits, ()) ) |) |) == (| Short, (| (), () |) |) );
    LP.valid_weaken (LP.strong_parser_kind 0 20 None) (LP.parse_flbytes (U32.v cid_len)) h0 sl 1ul;
    LP.valid_flbytes_elim h0 (U32.v cid_len) sl 1ul;
    let pos = LP.jump_flbytes (U32.v cid_len) cid_len sl 1ul in
    let dcid = B.sub sl.LP.base 1ul (pos `U32.sub` 1ul) in
    PShort protected_bits (spin = 1uy) dcid cid_len

#pop-options

#push-options "--z3rlimit 128 --z3cliopt smt.arith.nl=false --query_stats --max_fuel 9 --initial_fuel 9 --max_ifuel 9 --initial_ifuel 9 --query_stats"

let read_header_body_long_retry
  (sl: LP.slice (B.trivial_preorder _) (B.trivial_preorder _))
  (cid_len: U32.t { U32.v cid_len <= 20 } )
  (protected_bits: LPB.bitfield LPB.uint8 4)
: Tot (read_header_body_t sl cid_len (| Long, (| (), (| Retry, (protected_bits, ()) |) |) |) )
= fun len ->
    let h0 = HST.get () in
    assert_norm (LPB.bitsum'_key_of_t first_byte (| Long, (| (), (| Retry, (protected_bits, ()) |) |) |)  == (| Long, (| (), (| Retry, () |) |) |) );
    LP.valid_nondep_then h0 parse_common_long (LP.parse_bounded_vlbytes 0 20) sl 1ul;
    LP.valid_nondep_then h0 LP.parse_u32 (LP.parse_bounded_vlbytes 0 20 `LP.nondep_then` LP.parse_bounded_vlbytes 0 20) sl 1ul;
    let version = LP.read_u32 sl 1ul in
    let pos1 = LP.jump_u32 sl 1ul in
    LP.valid_nondep_then h0 (LP.parse_bounded_vlbytes 0 20) (LP.parse_bounded_vlbytes 0 20) sl pos1;
    let dcid = LP.get_vlbytes_contents 0 20 sl pos1 in
    let dcid_len = LP.bounded_vlbytes_payload_length 0 20 sl pos1 in
    let pos2 = LP.jump_bounded_vlbytes 0 20 sl pos1 in
    let scid = LP.get_vlbytes_contents 0 20 sl pos2 in
    let scid_len = LP.bounded_vlbytes_payload_length 0 20 sl pos2 in
    let pos3 = LP.jump_bounded_vlbytes 0 20 sl pos2 in
    let odcid = LP.get_vlbytes_contents 0 20 sl pos3 in
    let odcid_len = LP.bounded_vlbytes_payload_length 0 20 sl pos3 in
    let spec = PRetry odcid odcid_len in
    (PLong protected_bits version dcid dcid_len scid scid_len spec)

#pop-options

let valid_long_initial_body_elim
  (h0: HS.mem)
  (sl: LP.slice (B.trivial_preorder _) (B.trivial_preorder _))
  (pos: U32.t)
: Lemma
  (requires (LP.valid parse_long_initial_body h0 sl pos))
  (ensures (
    LP.valid parse_long_initial_body h0 sl pos /\
    LP.valid_content_pos
      (parse_common_long `LP.nondep_then` (LP.parse_bounded_vlgenbytes 0 token_max_len (VI.parse_bounded_varint 0 token_max_len) `LP.nondep_then` parse_payload_and_pn_length))
      h0
      sl
      pos
      (LP.contents parse_long_initial_body h0 sl pos)
      (LP.get_valid_pos parse_long_initial_body h0 sl pos)
  ))
= LP.valid_facts parse_long_initial_body h0 sl pos;
  LP.valid_facts
    (parse_common_long `LP.nondep_then` (LP.parse_bounded_vlgenbytes 0 token_max_len (VI.parse_bounded_varint 0 token_max_len) `LP.nondep_then` parse_payload_and_pn_length))
    h0 sl pos

inline_for_extraction
let read_payload_and_pn_length : LP.leaf_reader parse_payload_and_pn_length =
  LP.read_filter VI.read_varint payload_and_pn_length_prop

#push-options "--z3rlimit 1024 --z3cliopt smt.arith.nl=false --query_stats --max_fuel 9 --initial_fuel 9 --max_ifuel 9 --initial_ifuel 9 --query_stats"

#restart-solver

let read_header_body_long_initial
  (sl: LP.slice (B.trivial_preorder _) (B.trivial_preorder _))
  (cid_len: U32.t { U32.v cid_len <= 20 } )
  (protected_bits: LPB.bitfield LPB.uint8 4)
: Tot (read_header_body_t sl cid_len (| Long, (| (), (| Initial, (protected_bits, () ) |) |) |) )
= fun len ->
    let h0 = HST.get () in
    assert_norm (LPB.bitsum'_key_of_t first_byte (| Long, (| (), (| Initial, (protected_bits, () ) |) |) |) == (| Long, (| (), (| Initial, () |) |) |) );
    valid_long_initial_body_elim h0 sl 1ul;
    LP.valid_nondep_then h0 parse_common_long (LP.parse_bounded_vlgenbytes 0 token_max_len (VI.parse_bounded_varint 0 token_max_len) `LP.nondep_then` parse_payload_and_pn_length) sl 1ul;
    LP.valid_nondep_then h0 LP.parse_u32 (LP.parse_bounded_vlbytes 0 20 `LP.nondep_then` LP.parse_bounded_vlbytes 0 20) sl 1ul;
    let version = LP.read_u32 sl 1ul in
    let pos1 = LP.jump_u32 sl 1ul in
    LP.valid_nondep_then h0 (LP.parse_bounded_vlbytes 0 20) (LP.parse_bounded_vlbytes 0 20) sl pos1;
    let dcid = LP.get_vlbytes_contents 0 20 sl pos1 in
    let dcid_len = LP.bounded_vlbytes_payload_length 0 20 sl pos1 in
    let pos2 = LP.jump_bounded_vlbytes 0 20 sl pos1 in
    let scid = LP.get_vlbytes_contents 0 20 sl pos2 in
    let scid_len = LP.bounded_vlbytes_payload_length 0 20 sl pos2 in
    let pos3 = LP.jump_bounded_vlbytes 0 20 sl pos2 in
    LP.valid_nondep_then h0 (LP.parse_bounded_vlgenbytes 0 token_max_len (VI.parse_bounded_varint 0 token_max_len)) (parse_payload_and_pn_length) sl pos3;
    let token = LP.get_bounded_vlgenbytes_contents 0 token_max_len (VI.read_bounded_varint 0 token_max_len) (VI.jump_bounded_varint 0 token_max_len) sl pos3 in
    let token_len = LP.bounded_vlgenbytes_payload_length 0 token_max_len (VI.read_bounded_varint 0 token_max_len) sl pos3 in
    let pos4 = LP.jump_bounded_vlgenbytes 0 token_max_len (VI.jump_bounded_varint 0 token_max_len) (VI.read_bounded_varint 0 token_max_len) sl pos3 in
    let payload_and_pn_length = read_payload_and_pn_length sl pos4 in
    let spec = PInitial (payload_and_pn_length) token token_len in
    PLong protected_bits version dcid dcid_len scid scid_len spec

#pop-options

let valid_long_handshake_body_elim
  (h0: HS.mem)
  (sl: LP.slice (B.trivial_preorder _) (B.trivial_preorder _))
  (pos: U32.t)
: Lemma
  (requires (LP.valid parse_long_handshake_body h0 sl pos))
  (ensures (
    LP.valid parse_long_handshake_body h0 sl pos /\
    LP.valid_content_pos
      (parse_common_long `LP.nondep_then` parse_payload_and_pn_length)
      h0
      sl
      pos
      (LP.contents parse_long_handshake_body h0 sl pos)
      (LP.get_valid_pos parse_long_handshake_body h0 sl pos)
  ))
= LP.valid_facts parse_long_handshake_body h0 sl pos;
  LP.valid_facts
    (parse_common_long `LP.nondep_then` VI.parse_varint)
    h0 sl pos

#push-options "--z3rlimit 512 --z3cliopt smt.arith.nl=false --query_stats --max_fuel 9 --initial_fuel 9 --max_ifuel 9 --initial_ifuel 9 --query_stats"

#restart-solver

let read_header_body_long_handshake
  (sl: LP.slice (B.trivial_preorder _) (B.trivial_preorder _))
  (cid_len: U32.t { U32.v cid_len <= 20 } )
  (protected_bits: LPB.bitfield LPB.uint8 4)
: Tot (read_header_body_t sl cid_len (| Long, (| (), (| Handshake, (protected_bits, () ) |) |) |) )
= fun len ->
    let h0 = HST.get () in
    assert_norm (LPB.bitsum'_key_of_t first_byte (| Long, (| (), (| Handshake, (protected_bits, () ) |) |) |) == (| Long, (| (), (| Handshake, () |) |) |) );
    valid_long_handshake_body_elim h0 sl 1ul;
    LP.valid_nondep_then h0 parse_common_long parse_payload_and_pn_length sl 1ul;
    LP.valid_nondep_then h0 LP.parse_u32 (LP.parse_bounded_vlbytes 0 20 `LP.nondep_then` LP.parse_bounded_vlbytes 0 20) sl 1ul;
    let version = LP.read_u32 sl 1ul in
    let pos1 = LP.jump_u32 sl 1ul in
    LP.valid_nondep_then h0 (LP.parse_bounded_vlbytes 0 20) (LP.parse_bounded_vlbytes 0 20) sl pos1;
    let dcid = LP.get_vlbytes_contents 0 20 sl pos1 in
    let dcid_len = LP.bounded_vlbytes_payload_length 0 20 sl pos1 in
    let pos2 = LP.jump_bounded_vlbytes 0 20 sl pos1 in
    let scid = LP.get_vlbytes_contents 0 20 sl pos2 in
    let scid_len = LP.bounded_vlbytes_payload_length 0 20 sl pos2 in
    let pos3 = LP.jump_bounded_vlbytes 0 20 sl pos2 in
    let payload_and_pn_length = read_payload_and_pn_length sl pos3 in
    let spec = PHandshake payload_and_pn_length in
    PLong protected_bits version dcid dcid_len scid scid_len spec

#pop-options

let valid_long_zero_rtt_body_elim
  (h0: HS.mem)
  (sl: LP.slice (B.trivial_preorder _) (B.trivial_preorder _))
  (pos: U32.t)
: Lemma
  (requires (LP.valid parse_long_zero_rtt_body h0 sl pos))
  (ensures (
    LP.valid parse_long_zero_rtt_body h0 sl pos /\
    LP.valid_content_pos
      (parse_common_long `LP.nondep_then` parse_payload_and_pn_length)
      h0
      sl
      pos
      (LP.contents parse_long_zero_rtt_body h0 sl pos)
      (LP.get_valid_pos parse_long_zero_rtt_body h0 sl pos)
  ))
= LP.valid_facts parse_long_zero_rtt_body h0 sl pos;
  LP.valid_facts
    (parse_common_long `LP.nondep_then` parse_payload_and_pn_length)
    h0 sl pos

#push-options "--z3rlimit 512 --z3cliopt smt.arith.nl=false --query_stats --max_fuel 9 --initial_fuel 9 --max_ifuel 9 --initial_ifuel 9 --query_stats"

#restart-solver

let read_header_body_long_zero_rtt
  (sl: LP.slice (B.trivial_preorder _) (B.trivial_preorder _))
  (cid_len: U32.t { U32.v cid_len <= 20 } )
  (protected_bits: LPB.bitfield LPB.uint8 4)
: Tot (read_header_body_t sl cid_len (| Long, (| (), (| ZeroRTT, (protected_bits, () ) |) |) |) )
= fun len ->
    let h0 = HST.get () in
    assert_norm (LPB.bitsum'_key_of_t first_byte (| Long, (| (), (| ZeroRTT, (protected_bits, () ) |) |) |) == (| Long, (| (), (| ZeroRTT, () |) |) |) );
    valid_long_zero_rtt_body_elim h0 sl 1ul;
    LP.valid_nondep_then h0 parse_common_long parse_payload_and_pn_length sl 1ul;
    LP.valid_nondep_then h0 LP.parse_u32 (LP.parse_bounded_vlbytes 0 20 `LP.nondep_then` LP.parse_bounded_vlbytes 0 20) sl 1ul;
    let version = LP.read_u32 sl 1ul in
    let pos1 = LP.jump_u32 sl 1ul in
    LP.valid_nondep_then h0 (LP.parse_bounded_vlbytes 0 20) (LP.parse_bounded_vlbytes 0 20) sl pos1;
    let dcid = LP.get_vlbytes_contents 0 20 sl pos1 in
    let dcid_len = LP.bounded_vlbytes_payload_length 0 20 sl pos1 in
    let pos2 = LP.jump_bounded_vlbytes 0 20 sl pos1 in
    let scid = LP.get_vlbytes_contents 0 20 sl pos2 in
    let scid_len = LP.bounded_vlbytes_payload_length 0 20 sl pos2 in
    let pos3 = LP.jump_bounded_vlbytes 0 20 sl pos2 in
    let payload_and_pn_length = read_payload_and_pn_length sl pos3 in
    let spec = PZeroRTT payload_and_pn_length in
    PLong protected_bits version dcid dcid_len scid scid_len spec

#pop-options

inline_for_extraction
noextract
let read_header_body
  (sl: LP.slice (B.trivial_preorder _) (B.trivial_preorder _))
  (cid_len: U32.t { U32.v cid_len <= 20 } )
  (tg: LPB.bitsum'_type first_byte)
: Tot (read_header_body_t sl cid_len tg)
= fun len ->
  let h0 = HST.get () in
  match tg with
  | (| Short, (| (), (spin, (protected_bits, ())) |) |) ->
    read_header_body_short sl cid_len spin protected_bits len
  | (| Long, (| (), (| Retry, (protected_bits, ()) |) |) |) ->
    read_header_body_long_retry sl cid_len protected_bits len
  | (| Long, (| (), (| Initial, (protected_bits, ()) |) |) |) ->
    read_header_body_long_initial sl cid_len protected_bits len
  | (| Long, (| (), (| Handshake, (protected_bits, ()) |) |) |) ->
    read_header_body_long_handshake sl cid_len protected_bits len
  | (| Long, (| (), (| ZeroRTT, (protected_bits, ()) |) |) |) ->
    read_header_body_long_zero_rtt sl cid_len protected_bits len

#push-options "--z3rlimit 512 --z3cliopt smt.arith.nl=false"

let read_header packet packet_len cid_len =
  let h0 = HST.get () in
  let sl = LP.make_slice packet packet_len in
  LP.valid_facts (parse_header cid_len) h0 sl 0ul;
  assert (B.as_seq h0 packet `Seq.equal` LP.bytes_of_slice_from h0 sl 0ul);
  assert_norm (
    let k = parse_header_kind' cid_len in
    Some? k.LP.parser_kind_high /\
    Some?.v k.LP.parser_kind_high <= U32.v LP.validator_max_length /\
    k.LP.parser_kind_subkind == Some LP.ParserStrong
  );
  let len = LP.validate_bounded_strong_prefix (validate_header cid_len) sl 0ul in
  if len `U32.gt` LP.validator_max_length
  then None
  else begin
    LPB.valid_bitsum_elim
      #LP.parse_u8_kind
      #8
      #U8.t
      #LPB.uint8
      first_byte
      #(header' cid_len)
      (first_byte_of_header cid_len)
      (header_body_type cid_len)
      (header_synth cid_len)
      LP.parse_u8
      (parse_header_body cid_len)
      h0
      sl
      0ul;
    let r = LP.read_u8 sl 0ul in
    let res = destr_first_byte
      (read_header_body_t sl cid_len)
      (fun _ cond dt df len' -> if cond then dt () len' else df () len')
      (read_header_body sl cid_len)
      r
      ()
    in
    Some (res, len)
  end

#pop-options
