module QUIC.Spec.Base

module FB = FStar.Bytes
module U64 = FStar.UInt64
module U32 = FStar.UInt32
module U8 = FStar.UInt8
module S = FStar.Seq

inline_for_extraction
let varint_bound : (varint_bound: U64.t { U64.v varint_bound == pow2 62 }) =
  [@inline_let] let v = 4611686018427387904uL in
  [@inline_let] let _ = assert_norm (U64.v v == pow2 62) in
  v

inline_for_extraction
let varint_t = (x: U64.t { U64.v x < U64.v varint_bound })

type byte = FStar.UInt8.t
type bytes = s:S.seq byte
type lbytes (n:nat) = b:bytes{S.length b = n}

inline_for_extraction
let vlbytes (min: nat) (max: nat) =
  (x: FB.bytes { min <= FB.length x /\ FB.length x <= max })

inline_for_extraction
noextract
let integer_size = (x: nat { 1 <= x /\ x <= 4 })

inline_for_extraction
noextract
let bounded_integer_prop
  (sz: integer_size)
  (x: U32.t)
: Tot Type0
= match sz with
  | 1 -> U32.v x < 256
  | 2 -> U32.v x < 65536
  | 3 -> U32.v x < 16777296
  | 4 -> True

inline_for_extraction
noextract
let bounded_integer
  (sz: integer_size)
: Tot eqtype
= (x: U32.t { bounded_integer_prop sz x })

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

noeq
type long_header_specifics =
| MInitial:
  (token: vlbytes 0 token_max_len) -> // arbitrary bound
  (payload_length: varint_t) ->
  (packet_number_length: packet_number_length_t) ->
  (packet_number: bounded_integer (U32.v packet_number_length)) ->
  long_header_specifics
| MZeroRTT:
  (payload_length: varint_t) ->
  (packet_number_length: packet_number_length_t) ->
  (packet_number: bounded_integer (U32.v packet_number_length)) ->
  long_header_specifics
| MHandshake:
  (payload_length: varint_t) ->
  (packet_number_length: packet_number_length_t) ->
  (packet_number: bounded_integer (U32.v packet_number_length)) ->
  long_header_specifics
| MRetry:
  (unused: bitfield 4) ->
  (odcid: vlbytes 0 20) -> // TODO: change bounds to drop instead of rejecting as invalid
  long_header_specifics

noeq
type header =
| MLong:
  (version: FB.lbytes 4) ->
  (dcid: vlbytes 0 20) ->
  (scid: vlbytes 0 20) ->
  (spec: long_header_specifics) ->
  header
| MShort:
  (spin: bool) ->
  (key_phase: bool) ->
  (dcid: FB.bytes) ->
  (packet_number_length: packet_number_length_t) ->
  (packet_number: bounded_integer (U32.v packet_number_length)) ->
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

let packet_number (h: header {~ (is_retry h)}) : Tot (bounded_integer (U32.v (pn_length h))) =
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

inline_for_extraction
let short_dcid_len_t = (short_dcid_len: U32.t { U32.v short_dcid_len <= 20 })

let header_short_dcid_length_prop
  (m: header)
  (short_dcid_len: short_dcid_len_t)
: GTot bool
= if MShort? m
  then FB.length (MShort?.dcid m) = U32.v short_dcid_len
  else true

inline_for_extraction
type header' (short_dcid_len: short_dcid_len_t) = (m: header { header_short_dcid_length_prop m short_dcid_len })

type packet = b:bytes{let l = S.length b in 21 <= l /\ l < pow2 32}
