module QUIC.Spec.Base

module FB = FStar.Bytes
module U64 = FStar.UInt64
module U32 = FStar.UInt32
module U8 = FStar.UInt8
module S = FStar.Seq

inline_for_extraction
let uint62_bound : (uint62_bound: U64.t { U64.v uint62_bound == pow2 62 }) =
  [@inline_let] let v = 4611686018427387904uL in
  [@inline_let] let _ = assert_norm (U64.v v == pow2 62) in
  v

inline_for_extraction
let uint62_t = (x: U64.t { U64.v x < U64.v uint62_bound })

type byte = FStar.UInt8.t
type bytes = s:S.seq byte
type lbytes (n:nat) = b:bytes{S.length b = n}

inline_for_extraction
let vlbytes (min: nat) (max: nat) =
  (x: FB.bytes { min <= FB.length x /\ FB.length x <= max })

inline_for_extraction
noextract
let token_max_len = 16383 // arbitrary bound

inline_for_extraction
noextract
type packet_number_length_t : eqtype = (x: U32.t { 1 <= U32.v x /\ U32.v x <= 4 })

inline_for_extraction
noextract
let bitfield
  (sz: nat { sz <= 8 })
: Tot eqtype
= (x: U8.t { U8.v x < pow2 sz })

// TODO: here add the constraint { payload_length + packet_number_length < pow2 62 } and change the parser accordingly (see comment on QUIC.Parse.fst:payload_length_pn)

noeq
type long_header_specifics =
| MInitial:
  (token: vlbytes 0 token_max_len) -> // arbitrary bound
  (payload_length: uint62_t) ->
  (packet_number_length: packet_number_length_t) ->
  (packet_number: uint62_t) ->
  long_header_specifics
| MZeroRTT:
  (payload_length: uint62_t) ->
  (packet_number_length: packet_number_length_t) ->
  (packet_number: uint62_t) ->
  long_header_specifics
| MHandshake:
  (payload_length: uint62_t) ->
  (packet_number_length: packet_number_length_t) ->
  (packet_number: uint62_t) ->
  long_header_specifics
| MRetry:
  (unused: bitfield 4) ->
  (odcid: vlbytes 0 20) -> // TODO: change bounds to drop instead of rejecting as invalid
  long_header_specifics

noeq
type header =
| MLong:
  (version: U32.t) ->
  (dcid: vlbytes 0 20) ->
  (scid: vlbytes 0 20) ->
  (spec: long_header_specifics) ->
  header
| MShort:
  (spin: bool) ->
  (key_phase: bool) ->
  (dcid: vlbytes 0 20) ->
  (packet_number_length: packet_number_length_t) ->
  (packet_number: uint62_t) ->
  header

let is_initial (h: header) : Tot bool =
  if MLong? h then MInitial? (MLong?.spec h) else false

let is_zero_rtt (h: header) : Tot bool =
  if MLong? h then MZeroRTT? (MLong?.spec h) else false

let is_handshake (h: header) : Tot bool =
  if MLong? h then MHandshake? (MLong?.spec h) else false

let is_retry (h: header) : Tot bool =
  if MLong? h then MRetry? (MLong?.spec h) else false

let pn_length (h: header { ~ (is_retry h) }) : Tot packet_number_length_t =
  match h with
  | MLong _ _ _ spec ->
    begin match spec with
    | MInitial _ _ pnl _ -> pnl
    | MZeroRTT _ pnl _ -> pnl
    | MHandshake _ pnl _ -> pnl
    end
  | MShort _ _ _ pnl _ -> pnl

let packet_number (h: header {~ (is_retry h)}) : Tot uint62_t =
  match h with
  | MLong _ _ _ spec ->
    begin match spec with
    | MInitial _ _ _ pn -> pn
    | MZeroRTT _ _ pn -> pn
    | MHandshake _ _ pn -> pn
    end
  | MShort _ _ _ _ pn -> pn

let dcid_len (h: header) : Tot nat =
  match h with
  | MLong _ dcid _ _ -> FB.length dcid
  | MShort _ _ dcid _ _ -> FB.length dcid

type packet = b:bytes{let l = S.length b in (* 21 <= l /\ *) l < pow2 32}

(* Packet number *)

inline_for_extraction
let last_packet_number_t = (last: uint62_t { U64.v last + 1 < U64.v uint62_bound})

let bound_npn' (pn_len:nat { pn_len < 4 }) : Tot (y: nat {y == pow2 (8 `op_Multiply` (pn_len + 1)) }) =
  assert_norm (pow2 8 == 256);
  assert_norm (pow2 16 == 65536);
  assert_norm (pow2 24 == 16777216);
  assert_norm (pow2 32 == 4294967296);
  match pn_len with
  | 0 -> 256
  | 1 -> 65536
  | 2 -> 16777216
  | 3 -> 4294967296

let in_window (pn_len: nat { pn_len < 4 }) (last pn:nat) =
  let h = bound_npn' pn_len in
  (last+1 < h/2 /\ pn < h) \/
  (last+1 >= U64.v uint62_bound - h/2 /\ pn >= U64.v uint62_bound - h) \/
  (last+1 - h/2 < pn /\ pn <= last+1 + h/2)

(* Payload length *)

let has_payload_length
  (h: header)
: Tot bool
= MLong? h && (not (MRetry? (MLong?.spec h)))

let payload_length 
  (h: header { has_payload_length h })
: Tot uint62_t
= match MLong?.spec h with
  | MInitial _ pl _ _ -> pl
  | MZeroRTT pl _ _ -> pl
  | MHandshake pl _ _ -> pl

(* Correctness of a packet wrt. parsing parameters (cid_len, window) *)

let is_valid_header (h: header) (cid_len: nat) (last: nat) : Tot Type0 =
  (MShort? h ==> dcid_len h == cid_len) /\
  ((~ (is_retry h)) ==> in_window (U32.v (pn_length h) - 1) last (U64.v (packet_number h)))
