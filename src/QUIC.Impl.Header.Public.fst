module QUIC.Impl.Header.Public
open QUIC.Spec.Header.Public
open QUIC.Impl.Base

friend QUIC.Spec.Header.Public

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

#push-options "--z3rlimit 128 --z3cliopt smt.arith.nl=false --using_facts_from '*,-FStar.Int.Cast' --query_stats --max_fuel 9 --initial_fuel 9 --max_ifuel 9 --initial_ifuel 9 --query_stats"

#restart-solver

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
    PShort (Secret.hide #Secret.U8 protected_bits) (spin = 1uy) dcid cid_len

#pop-options

#push-options "--z3rlimit 128 --z3cliopt smt.arith.nl=false --query_stats --max_fuel 9 --initial_fuel 9 --max_ifuel 9 --initial_ifuel 9 --query_stats"

#restart-solver

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
    (PLong (Secret.hide #Secret.U8 protected_bits) version dcid dcid_len scid scid_len spec)

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
    PLong (Secret.hide #Secret.U8 protected_bits) version dcid dcid_len scid scid_len spec

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
    PLong (Secret.hide #Secret.U8 protected_bits) version dcid dcid_len scid scid_len spec

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
    PLong (Secret.hide #Secret.U8 protected_bits) version dcid dcid_len scid scid_len spec

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
    let k = parse_header_kind cid_len in
    Some? k.LP.parser_kind_high /\
    Some?.v k.LP.parser_kind_high <= U32.v LP.validator_max_length /\
    k.LP.parser_kind_subkind == Some LP.ParserStrong
  );
  begin
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
    res
  end

#pop-options

inline_for_extraction
noextract
let synth_first_byte
: (LPB.synth_bitsum'_recip_t first_byte)
= norm [primops; iota; zeta; delta_attr [`%LPB.filter_bitsum'_t_attr]]
  (LPB.mk_synth_bitsum'_recip first_byte)

module LW = LowParse.Low.Writers.Instances

#push-options "--z3rlimit 64 --max_fuel 4 --initial_fuel 4"

inline_for_extraction
noextract
let swrite_header_short
  (protected_bits: bitfield 5)
  (spin: bool)
  (cid: B.buffer U8.t)
  (cid_len: U32.t {
    let l = U32.v cid_len in
    l == B.length cid /\
    0 <= l /\ l <= 20
  })
  (h0: HS.mem {
    B.live h0 cid
  })
  (out: LP.slice (B.trivial_preorder _) (B.trivial_preorder _) {
    B.loc_disjoint (B.loc_buffer cid) (LP.loc_slice_from out 0ul)
  })
: Tot (w: LW.swriter (serialize_header cid_len) h0 0 out 0ul {
    LW.swvalue w == S.PShort protected_bits spin (FB.hide (B.as_seq h0 cid))
  })
= 
  [@inline_let]
  let tg : LPB.bitsum'_type first_byte =
    (| Short, (| (), ((if spin then 1uy else 0uy), (protected_bits, ())) |) |)
  in
  [@inline_let]
  let k : LPB.bitsum'_key_type first_byte =
    (| Short, (| (), () |) |)
  in
  [@inline_let]
  let _ =
    assert_norm (LPB.bitsum'_key_of_t first_byte tg == k);
    assert_norm (first_byte_of_header cid_len (S.PShort protected_bits spin (FB.hide (B.as_seq h0 cid))) == tg)
  in
  [@inline_let]
  let s : LW.swriter (serialize_header_body cid_len k) h0 _ out 0ul =
    LW.swrite_weaken (LP.strong_parser_kind 0 20 None) (LW.swrite_flbytes h0 out 0ul cid_len cid)
  in
  LW.swrite_bitsum
    h0
    _
    out
    0ul
    #LP.parse_u8_kind
    #8
    #U8.t
    first_byte
    #(header' cid_len)
    (first_byte_of_header cid_len)
    (header_body_type cid_len)
    (header_synth cid_len)
    #LP.parse_u8
    #LP.serialize_u8
    LP.write_u8
    synth_first_byte
    #(parse_header_body cid_len)
    (serialize_header_body cid_len)
    tg
    s

#pop-options

inline_for_extraction
noextract
let swrite_common_long
  (version: U32.t)
  (dcid: B.buffer U8.t)
  (dcid_len: U32.t {
    let len = U32.v dcid_len in
    len == B.length dcid /\
    0 <= len /\ len <= 20
  })
  (scid: B.buffer U8.t)
  (scid_len: U32.t {
    let len = U32.v scid_len in
    len == B.length scid /\
    0 <= len /\ len <= 20
  })
  (h0: HS.mem {
    B.live h0 dcid /\
    B.live h0 scid
  })
  (out: LW.slice (B.trivial_preorder _) (B.trivial_preorder _) {
    B.loc_disjoint (B.loc_buffer dcid `B.loc_union` B.loc_buffer scid) (LW.loc_slice_from out 0ul)
  })
: Tot (w: LW.swriter serialize_common_long h0 0 out 0ul {
    LW.swvalue w == (version, (FB.hide (B.as_seq h0 dcid), FB.hide (B.as_seq h0 scid)))
  })
= LW.swrite_leaf LP.write_u32 h0 out 0ul version `LW.swrite_nondep_then` (
    LW.swrite_bounded_vlbytes h0 out 0ul 0 20 dcid_len dcid `LW.swrite_nondep_then`
    LW.swrite_bounded_vlbytes h0 out 0ul 0 20 scid_len scid
  )

inline_for_extraction
let swrite_payload_and_pn_length
  (payload_and_pn_length: payload_and_pn_length_t)
  (h0: HS.mem)
  (out: LW.slice (B.trivial_preorder _) (B.trivial_preorder _))
: Tot (w: LW.swriter (serialize_payload_and_pn_length) h0 0 out 0ul {
    LW.swvalue w == payload_and_pn_length
  })
= payload_and_pn_length_prop `LW.swrite_filter` LW.swrite_leaf (LP.leaf_writer_strong_of_serializer32 VI.write_varint ()) h0 out 0ul payload_and_pn_length

#push-options "--z3rlimit 128 --max_fuel 4 --initial_fuel 4"

inline_for_extraction
noextract
let swrite_header_long_initial
  (protected_bits: bitfield 4)
  (short_dcid_len: short_dcid_len_t)
  (version: U32.t)
  (dcid: B.buffer U8.t)
  (dcid_len: U32.t {
    let len = U32.v dcid_len in
    len == B.length dcid /\
    0 <= len /\ len <= 20
  })
  (scid: B.buffer U8.t)
  (scid_len: U32.t {
    let len = U32.v scid_len in
    len == B.length scid /\
    0 <= len /\ len <= 20
  })
  (payload_and_pn_length: payload_and_pn_length_t)
  (token: B.buffer U8.t)
  (token_length: U32.t {
    let v = U32.v token_length in
    v == B.length token /\
    0 <= v /\ v <= token_max_len
  })
  (h0: HS.mem {
    B.live h0 dcid /\
    B.live h0 scid /\
    B.live h0 token
  })
  (out: LP.slice (B.trivial_preorder _) (B.trivial_preorder _) {
    B.loc_disjoint ((B.loc_buffer dcid `B.loc_union` B.loc_buffer scid) `B.loc_union` B.loc_buffer token) (LW.loc_slice_from out 0ul)
  })
: Tot (w: LW.swriter (serialize_header short_dcid_len) h0 0 out 0ul {
    LW.swvalue w == S.PLong protected_bits version (FB.hide (B.as_seq h0 dcid)) (FB.hide (B.as_seq h0 scid)) (S.PInitial (FB.hide (B.as_seq h0 token))  payload_and_pn_length)
  })
= 
  [@inline_let]
  let tg : LPB.bitsum'_type first_byte =
    (| Long, (| (), (| Initial, (protected_bits, ()) |) |) |)
  in
  [@inline_let]
  let k : LPB.bitsum'_key_type first_byte =
    (| Long, (| (), (| Initial, () |) |) |)
  in
  [@inline_let]
  let _ =
    assert_norm (LPB.bitsum'_key_of_t first_byte tg == k);
    assert_norm (first_byte_of_header short_dcid_len (S.PLong protected_bits version (FB.hide (B.as_seq h0 dcid)) (FB.hide (B.as_seq h0 scid)) (S.PInitial (FB.hide (B.as_seq h0 token))  payload_and_pn_length)) == tg)
  in
  [@inline_let]
  let s : LW.swriter (serialize_header_body short_dcid_len k) h0 _ out 0ul =
    swrite_common_long version dcid dcid_len scid scid_len h0 out `LW.swrite_nondep_then` (
      LW.swrite_bounded_vlgenbytes h0 out 0ul 0 token_max_len (LP.leaf_writer_strong_of_serializer32 (VI.write_bounded_varint 0 token_max_len) ()) token_length token `LW.swrite_nondep_then`
      swrite_payload_and_pn_length payload_and_pn_length h0 out
    )
  in
  LW.swrite_bitsum
    h0
    _
    out
    0ul
    #LP.parse_u8_kind
    #8
    #U8.t
    first_byte
    #(header' short_dcid_len)
    (first_byte_of_header short_dcid_len)
    (header_body_type short_dcid_len)
    (header_synth short_dcid_len)
    #LP.parse_u8
    #LP.serialize_u8
    LP.write_u8
    synth_first_byte
    #(parse_header_body short_dcid_len)
    (serialize_header_body short_dcid_len)
    tg
    s

inline_for_extraction
noextract
let swrite_header_long_zeroRTT
  (protected_bits: bitfield 4)
  (short_dcid_len: short_dcid_len_t)
  (version: U32.t)
  (dcid: B.buffer U8.t)
  (dcid_len: U32.t {
    let len = U32.v dcid_len in
    len == B.length dcid /\
    0 <= len /\ len <= 20
  })
  (scid: B.buffer U8.t)
  (scid_len: U32.t {
    let len = U32.v scid_len in
    len == B.length scid /\
    0 <= len /\ len <= 20
  })
  (payload_and_pn_length: payload_and_pn_length_t)
  (h0: HS.mem {
    B.live h0 dcid /\
    B.live h0 scid
  })
  (out: LW.slice (B.trivial_preorder _) (B.trivial_preorder _) {
    B.loc_disjoint (B.loc_buffer dcid `B.loc_union` B.loc_buffer scid) (LW.loc_slice_from out 0ul)
  })
: Tot (w: LW.swriter (serialize_header short_dcid_len) h0 0 out 0ul {
      LW.swvalue w == S.PLong protected_bits version (FB.hide (B.as_seq h0 dcid)) (FB.hide (B.as_seq h0 scid)) (S.PZeroRTT payload_and_pn_length)
  })
=
  [@inline_let]
  let tg : LPB.bitsum'_type first_byte =
    (| Long, (| (), (| ZeroRTT, (protected_bits, ()) |) |) |)
  in
  [@inline_let]
  let k : LPB.bitsum'_key_type first_byte =
    (| Long, (| (), (| ZeroRTT, () |) |) |)
  in
  [@inline_let]
  let _ =
    assert_norm (LPB.bitsum'_key_of_t first_byte tg == k);
    assert_norm (first_byte_of_header short_dcid_len (S.PLong protected_bits version (FB.hide (B.as_seq h0 dcid)) (FB.hide (B.as_seq h0 scid)) (S.PZeroRTT payload_and_pn_length)) == tg)
  in
  [@inline_let]
  let s : LW.swriter (serialize_header_body short_dcid_len k) h0 _ out 0ul =
    swrite_common_long version dcid dcid_len scid scid_len h0 out `LW.swrite_nondep_then`
    swrite_payload_and_pn_length payload_and_pn_length h0 out
  in
  LW.swrite_bitsum
    h0
    _
    out
    0ul
    #LP.parse_u8_kind
    #8
    #U8.t
    first_byte
    #(header' short_dcid_len)
    (first_byte_of_header short_dcid_len)
    (header_body_type short_dcid_len)
    (header_synth short_dcid_len)
    #LP.parse_u8
    #LP.serialize_u8
    LP.write_u8
    synth_first_byte
    #(parse_header_body short_dcid_len)
    (serialize_header_body short_dcid_len)
    tg
    s

inline_for_extraction
noextract
let swrite_header_long_handshake
  (protected_bits: bitfield 4)
  (short_dcid_len: short_dcid_len_t)
  (version: U32.t)
  (dcid: B.buffer U8.t)
  (dcid_len: U32.t {
    let len = U32.v dcid_len in
    len == B.length dcid /\
    0 <= len /\ len <= 20
  })
  (scid: B.buffer U8.t)
  (scid_len: U32.t {
    let len = U32.v scid_len in
    len == B.length scid /\
    0 <= len /\ len <= 20
  })
  (payload_and_pn_length: payload_and_pn_length_t)
  (h0: HS.mem {
    B.live h0 dcid /\
    B.live h0 scid
  })
  (out: LW.slice (B.trivial_preorder _) (B.trivial_preorder _) {
    B.loc_disjoint (B.loc_buffer dcid `B.loc_union` B.loc_buffer scid) (LW.loc_slice_from out 0ul)
  })
: Tot (w: LW.swriter (serialize_header short_dcid_len) h0 0 out 0ul {
      LW.swvalue w == S.PLong protected_bits version (FB.hide (B.as_seq h0 dcid)) (FB.hide (B.as_seq h0 scid)) (S.PHandshake payload_and_pn_length)
  })
= [@inline_let]
  let tg : LPB.bitsum'_type first_byte =
    (| Long, (| (), (| Handshake, (protected_bits, ()) |) |) |)
  in
  [@inline_let]
  let k : LPB.bitsum'_key_type first_byte =
    (| Long, (| (), (| Handshake, () |) |) |)
  in
  [@inline_let]
  let _ =
    assert_norm (LPB.bitsum'_key_of_t first_byte tg == k);
    assert_norm (first_byte_of_header short_dcid_len (S.PLong protected_bits version (FB.hide (B.as_seq h0 dcid)) (FB.hide (B.as_seq h0 scid)) (S.PHandshake payload_and_pn_length)) == tg)
  in
  [@inline_let]
  let s : LW.swriter (serialize_header_body short_dcid_len k) h0 _ out 0ul =
    swrite_common_long version dcid dcid_len scid scid_len h0 out `LW.swrite_nondep_then`
    swrite_payload_and_pn_length payload_and_pn_length h0 out
  in
  LW.swrite_bitsum
    h0
    _
    out
    0ul
    #LP.parse_u8_kind
    #8
    #U8.t
    first_byte
    #(header' short_dcid_len)
    (first_byte_of_header short_dcid_len)
    (header_body_type short_dcid_len)
    (header_synth short_dcid_len)
    #LP.parse_u8
    #LP.serialize_u8
    LP.write_u8
    synth_first_byte
    #(parse_header_body short_dcid_len)
    (serialize_header_body short_dcid_len)
    tg
    s

inline_for_extraction
noextract
let swrite_header_long_retry
  (protected_bits: bitfield 4)
  (short_dcid_len: short_dcid_len_t)
  (version: U32.t)
  (dcid: B.buffer U8.t)
  (dcid_len: U32.t {
    let len = U32.v dcid_len in
    len == B.length dcid /\
    0 <= len /\ len <= 20
  })
  (scid: B.buffer U8.t)
  (scid_len: U32.t {
    let len = U32.v scid_len in
    len == B.length scid /\
    0 <= len /\ len <= 20
  })
  (odcid: B.buffer U8.t)
  (odcid_len: U32.t {
    let len = U32.v odcid_len in
    len == B.length odcid /\
    0 <= len /\ len <= 20
  })
  (h0: HS.mem {
    B.live h0 dcid /\
    B.live h0 scid /\
    B.live h0 odcid
  })
  (out: LW.slice (B.trivial_preorder _) (B.trivial_preorder _) {
    B.loc_disjoint ((B.loc_buffer dcid `B.loc_union` B.loc_buffer scid) `B.loc_union` B.loc_buffer odcid) (LW.loc_slice_from out 0ul)
  })
: Tot (w: LW.swriter (serialize_header short_dcid_len) h0 0 out 0ul {
      LW.swvalue w == S.PLong protected_bits version (FB.hide (B.as_seq h0 dcid)) (FB.hide (B.as_seq h0 scid)) (S.PRetry (FB.hide (B.as_seq h0 odcid)))
  })
= [@inline_let]
  let tg : LPB.bitsum'_type first_byte =
    (| Long, (| (), (| Retry, (protected_bits, () ) |) |) |)
  in
  [@inline_let]
  let k : LPB.bitsum'_key_type first_byte =
    (| Long, (| (), (| Retry, () |) |) |)
  in
  [@inline_let]
  let _ =
    assert_norm (LPB.bitsum'_key_of_t first_byte tg == k);
    assert_norm (first_byte_of_header short_dcid_len (S.PLong protected_bits version (FB.hide (B.as_seq h0 dcid)) (FB.hide (B.as_seq h0 scid)) (S.PRetry (FB.hide (B.as_seq h0 odcid)))) == tg)
  in
  [@inline_let]
  let s : LW.swriter (serialize_header_body short_dcid_len k) h0 0 out 0ul =
    swrite_common_long version dcid dcid_len scid scid_len h0 out `LW.swrite_nondep_then`
    LW.swrite_bounded_vlbytes h0 out 0ul 0 20 odcid_len odcid
  in
  LW.swrite_bitsum
    h0
    0
    out
    0ul
    #LP.parse_u8_kind
    #8
    #U8.t
    first_byte
    #(header' short_dcid_len)
    (first_byte_of_header short_dcid_len)
    (header_body_type short_dcid_len)
    (header_synth short_dcid_len)
    #LP.parse_u8
    #LP.serialize_u8
    LP.write_u8
    synth_first_byte
    #(parse_header_body short_dcid_len)
    (serialize_header_body short_dcid_len)
    tg
    s

#pop-options

#restart-solver

inline_for_extraction
val write_header_aux
  (short_dcid_len: short_dcid_len_t)
  (h: header)
  (out: B.buffer U8.t)
  (out_len: U32.t { U32.v out_len <= B.length out })
: HST.Stack U32.t
  (requires (fun h0 ->
    (PShort? h ==> PShort?.cid_len h == short_dcid_len) /\
    header_live h h0 /\
    B.live h0 out /\
    B.loc_disjoint (header_footprint h) (B.loc_buffer out) /\
    Seq.length (LP.serialize (serialize_header short_dcid_len) (set_protected_bits (g_header h h0) 0uy)) <= U32.v out_len
  ))
  (ensures (fun h0 len h1 ->
    let gh = set_protected_bits (g_header h h0) 0uy in
    let s = LP.serialize (serialize_header short_dcid_len) gh in
    U32.v len <= U32.v out_len /\
    B.modifies (B.loc_buffer out) h0 h1 /\
    Seq.slice (B.as_seq h1 out) 0 (U32.v len) == s 
  ))

#push-options "--z3rlimit 32"

#restart-solver

let write_header_aux
  short_dcid_len h out out_len
= let h0 = HST.get () in
  let sl = LW.make_slice out out_len in
  LW.serialized_length_eq (serialize_header short_dcid_len) (set_protected_bits (g_header h h0) 0uy);
  let len = match h with
  | PShort pb spin cid cid_len ->
    LW.swrite (swrite_header_short 0uy spin cid cid_len h0 sl) 0ul
  | PLong pb version dcid dcil scid scil spec ->
    begin match spec with
    | PInitial payload_and_pn_length token token_length ->
      LW.swrite (swrite_header_long_initial 0uy short_dcid_len version dcid dcil scid scil payload_and_pn_length token token_length h0 sl) 0ul
    | PZeroRTT payload_and_pn_length ->
      LW.swrite (swrite_header_long_zeroRTT 0uy short_dcid_len version dcid dcil scid scil payload_and_pn_length h0 sl) 0ul
    | PHandshake payload_and_pn_length ->
      LW.swrite (swrite_header_long_handshake 0uy short_dcid_len version dcid dcil scid scil payload_and_pn_length h0 sl) 0ul
    | PRetry odcid odcil ->
      LW.swrite (swrite_header_long_retry 0uy short_dcid_len version dcid dcil scid scil odcid odcil h0 sl) 0ul
    end
  in
  let h1 = HST.get () in
  LP.valid_pos_valid_exact  (parse_header short_dcid_len) h1 sl 0ul len;
  LP.valid_exact_serialize (serialize_header short_dcid_len) h1 sl 0ul len;
  len

#pop-options

let get_pb
  (h: header)
: Tot (secret_bitfield (if PShort? h then 5 else 4))
= 
  match h with
  | PShort pb spin cid cid_len ->
    pb
  | PLong pb version dcid dcil scid scil spec ->
    pb

let get_pb_correct
  (h: header)
  (m: HS.mem)
: Lemma
  (ensures (Secret.v (get_pb h) == U8.v (get_protected_bits (g_header h m))))
= ()

let get_pb_complete
  (h: header)
  (m: HS.mem)
: Lemma
  (set_protected_bits (set_protected_bits (g_header h m) 0uy) (U8.uint_to_t (Secret.v (get_pb h))) == g_header h m)
= ()

module SecretBuffer = QUIC.Secret.Buffer
module Seq = QUIC.Secret.Seq

#pop-options

#push-options "--z3rlimit 64 --query_stats"

#restart-solver

let write_header
  short_dcid_len h out out_len
=
  let h0 = HST.get () in
  let pb = get_pb h in
  serialize_set_protected_bits short_dcid_len (g_header h h0) 0uy;
  assert (Seq.length (LP.serialize (serialize_header short_dcid_len) (set_protected_bits (g_header h h0) 0uy)) == Seq.length (LP.serialize (serialize_header short_dcid_len) (g_header h h0)));
  let len = write_header_aux short_dcid_len h out out_len in
  let h1 = HST.get () in
  let f () : Lemma (
    let s = Seq.slice (B.as_seq h1 out) 0 (U32.v len) in
    Seq.length s > 0 /\
    LP.serialize (serialize_header short_dcid_len) (g_header h h0) ==
      LPB.uint8.LPB.set_bitfield (Seq.head s) 0 (if PShort? h then 5 else 4) (U8.uint_to_t (Secret.v pb) <: U8.t) `Seq.cons` Seq.tail s
  )
  =
    get_pb_complete h h0;
    serialize_set_protected_bits short_dcid_len (set_protected_bits (g_header h h0) 0uy) (U8.uint_to_t (Secret.v pb) <: U8.t)
  in
  f ();
  let post
    ()
    (contl: Seq.lseq U8.t 0)
    (cont: Seq.lseq U8.t (U32.v len))
    (contr: Seq.lseq U8.t (B.length out - U32.v len))
    (m: HS.mem)
  : GTot Type0
  =
      let s = Seq.slice (B.as_seq h1 out) 0 (U32.v len) in
      Seq.length s > 0 /\
      cont `Seq.equal` (LPB.uint8.LPB.set_bitfield (Seq.head s) 0 (if PShort? h then 5 else 4) (U8.uint_to_t (Secret.v pb) <: U8.t) `Seq.cons` Seq.tail s)
  in
  SecretBuffer.with_buffer_hide
    #unit
    out
    0ul
    len
    h1
    B.loc_none
    B.loc_none
    1ul 0ul 0ul 1ul 1ul 0ul
    post
    (fun _ bl bs br ->
      let x = B.index bs 0ul in
      let y =
        if PShort? h
        then Secret.set_bitfield #Secret.U8 x 0ul 5ul pb
        else Secret.set_bitfield #Secret.U8 x 0ul 4ul pb
      in
      assert (
        let s = Seq.slice (B.as_seq h1 out) 0 (U32.v len) in
        Secret.reveal #Secret.U8 y == LPB.uint8.LPB.set_bitfield (Seq.head s) 0 (if PShort? h then 5 else 4) (U8.uint_to_t (Secret.v pb) <: U8.t)
      );
      SecretBuffer.buffer_update_strong bs 0ul y;
      let h2 = HST.get () in
      assert (
        let s = Seq.slice (B.as_seq h1 out) 0 (U32.v len) in
        Seq.length s > 0 /\
        B.as_seq h2 bs `Seq.equal` Seq.cons y (Seq.tail (Seq.seq_hide #Secret.U8 s))
      )
    )
  ;
  len

#restart-solver

let header_len_correct
  dcid_len m h
= let hs = g_header h m in
  let f () : Lemma (U32.v (header_len h) == header_len' hs) =
    match h with
    | PLong pb version dcid dcil scid scil spec ->
      begin match spec with
      | PInitial payload_and_pn_length token token_length ->
        VI.bounded_varint_len_correct 0 token_max_len token_length;
        VI.varint_len_correct payload_and_pn_length
      | PZeroRTT payload_and_pn_length ->
        VI.varint_len_correct payload_and_pn_length
      | PHandshake payload_and_pn_length ->
        VI.varint_len_correct payload_and_pn_length
      | PRetry odcid odcil -> ()
    end
    | _ -> ()
  in
  f ();
  header_len'_correct dcid_len hs
