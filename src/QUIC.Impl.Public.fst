module QUIC.Impl.Public
include QUIC.Spec.Public

module LP = LowParse.Low

inline_for_extraction
let validate_common_long : LP.validator parse_common_long =
  LP.validate_u32 () `LP.validate_nondep_then` (LP.validate_bounded_vlbytes 0 20 `LP.validate_nondep_then` LP.validate_bounded_vlbytes 0 20)

module VI = QUIC.Impl.VarInt

inline_for_extraction
let validate_long_zero_rtt_body : LP.validator parse_long_zero_rtt_body =
  validate_common_long `LP.validate_nondep_then` VI.validate_varint

inline_for_extraction
let validate_long_handshake_body : LP.validator parse_long_handshake_body =
  validate_common_long `LP.validate_nondep_then` VI.validate_varint

inline_for_extraction
let validate_long_retry_body : LP.validator parse_long_retry_body =
  validate_common_long `LP.validate_nondep_then` LP.validate_bounded_vlbytes 0 20

module U32 = FStar.UInt32

inline_for_extraction
let validate_long_initial_body : LP.validator parse_long_initial_body =
  validate_common_long `LP.validate_nondep_then` (LP.validate_bounded_vlgenbytes 0 0ul token_max_len (U32.uint_to_t token_max_len) (VI.validate_bounded_varint 0ul (U32.uint_to_t token_max_len)) (VI.read_bounded_varint 0 token_max_len) `LP.validate_nondep_then` VI.validate_varint)

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

module S = QUIC.Spec.Public
module B = LowStar.Buffer
module U8 = FStar.UInt8

noeq
type long_header_specifics =
| PInitial:
  (payload_and_pn_length: uint62_t) ->
  (token: B.buffer U8.t) ->
  (token_length: U32.t { let v = U32.v token_length in v == B.length token /\ 0 <= v /\ v <= token_max_len }) ->
  long_header_specifics
| PZeroRTT:
  (payload_and_pn_length: uint62_t) ->
  long_header_specifics
| PHandshake:
  (payload_and_pn_length: uint62_t) ->
  long_header_specifics
| PRetry:
  odcid: B.buffer U8.t ->
  odcil: U32.t { let v = U32.v odcil in v = B.length odcid /\ 0 <= v /\ v <= 20 } ->
  long_header_specifics

noeq
type header =
| PLong:
  (protected_bits: bitfield 4) ->
  (version: U32.t) ->
  dcid: B.buffer U8.t ->
  dcil: U32.t { let v = U32.v dcil in v == B.length dcid /\ 0 <= v /\ v <= 20 } ->
  scid: B.buffer U8.t ->
  scil: U32.t { let v = U32.v scil in v == B.length scid /\ 0 <= v /\ v <= 20 } ->
  (spec: long_header_specifics) ->
  header
| PShort:
  (protected_bits: bitfield 5) ->
  (spin: bool) ->
  cid: B.buffer U8.t ->
  cid_len: U32.t{
    let l = U32.v cid_len in
    l == B.length cid /\
    0 <= l /\ l <= 20
  } ->
  header

module HS = FStar.HyperStack

let header_live (h: header) (m: HS.mem) : GTot Type0 =
  match h with
  | PShort protected_bits spin cid cid_len ->
    B.live m cid
  | PLong protected_bits version dcid dcil scid scil spec ->
    B.live m dcid /\ B.live m scid /\
    begin match spec with
    | PInitial payload_and_pn_length token token_length ->
      B.live m token
    | PRetry odcid odcil ->
      B.live m odcid
    | _ -> True
    end

let header_footprint (h: header) : GTot B.loc =
  match h with
  | PShort protected_bits spin cid cid_len ->
    B.loc_buffer cid
  | PLong protected_bits version dcid dcil scid scil spec ->
    B.loc_buffer dcid `B.loc_union` B.loc_buffer scid `B.loc_union`
    begin match spec with
    | PInitial payload_and_pn_length token token_length ->
      B.loc_buffer token
    | PRetry odcid odcil ->
      B.loc_buffer odcid
    | _ -> B.loc_none
    end

let header_live_loc_not_unused_in_footprint (h: header) (m: HS.mem) : Lemma
  (requires (header_live h m))
  (ensures (B.loc_not_unused_in m `B.loc_includes` header_footprint h))
= ()

module FB = FStar.Bytes

let g_header (h: header) (m: HS.mem) : GTot S.header =
  match h with
  | PShort protected_bits spin cid cid_len ->
    S.PShort protected_bits spin (FB.hide (B.as_seq m cid))
  | PLong protected_bits version dcid dcil scid scil spec ->
    S.PLong protected_bits version (FB.hide (B.as_seq m dcid)) (FB.hide (B.as_seq m scid))
    begin match spec with
    | PInitial payload_and_pn_length token token_length ->
      S.PInitial (FB.hide (B.as_seq m token)) payload_and_pn_length 
    | PRetry odcid odcil ->
      S.PRetry (FB.hide (B.as_seq m odcid))
    | PHandshake payload_and_pn_length -> S.PHandshake payload_and_pn_length
    | PZeroRTT payload_and_pn_length -> S.PZeroRTT payload_and_pn_length    
    end

let frame_header_live
  (h: header)
  (l: B.loc)
  (m1 m2: HS.mem)
: Lemma
  (requires (
    header_live h m1 /\
    B.modifies l m1 m2 /\
    B.loc_disjoint l (header_footprint h)
  ))
  (ensures (header_live h m2))
= ()

let frame_header
  (h: header)
  (l: B.loc)
  (m1 m2: HS.mem)
: Lemma
  (requires (
    header_live h m1 /\
    B.modifies l m1 m2 /\
    B.loc_disjoint l (header_footprint h)
  ))
  (ensures (header_live h m2 /\ g_header h m2 == g_header h m1))
= ()


(* Length computations need to be transparent because the precondition
to QUIC.Impl.encrypt requires the user to provide a destination buffer
large enough to contain the byte representation of the header *)

module U64 = FStar.UInt64

module HST = FStar.HyperStack.ST

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

assume
val read_header_body
  (sl: LP.slice (B.trivial_preorder _) (B.trivial_preorder _))
  (cid_len: U32.t { U32.v cid_len <= 20 } )
  (tg: LPB.bitsum'_type first_byte)
: Tot (read_header_body_t sl cid_len tg)

val read_header
  (packet: B.buffer U8.t)
  (packet_len: U32.t { let v = U32.v packet_len in v == B.length packet })
  (cid_len: U32.t { U32.v cid_len <= 20 } )
: HST.Stack (option (header & U32.t))
  (requires (fun h ->
    B.live h packet
  ))
  (ensures (fun h res h' ->
    B.modifies B.loc_none h h' /\
    begin
      match LP.parse (parse_header cid_len) (B.as_seq h packet), res with
      | None, None -> True
      | Some (x, len), Some (x', len') ->
        header_live x' h' /\
        len <= B.length packet /\
        B.loc_buffer (B.gsub packet 0ul (U32.uint_to_t len)) `B.loc_includes` header_footprint x' /\
        g_header x' h' == x /\
        U32.v len' == len
      | _ -> False
    end
  ))

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
