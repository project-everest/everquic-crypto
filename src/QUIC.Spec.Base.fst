module QUIC.Spec.Base

module FB = FStar.Bytes
module U62 = QUIC.UInt62
module U64 = FStar.UInt64
module U32 = FStar.UInt32
module U8 = FStar.UInt8
module S = FStar.Seq
module PN = QUIC.Spec.PacketNumber

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
let bitfield
  (sz: nat { sz <= 8 })
: Tot eqtype
= (x: U8.t { U8.v x < pow2 sz })

type payload_and_pn_length_t = (payload_and_pn_length: U62.t { U64.v payload_and_pn_length >= 20 })

noeq
type long_header_specifics =
| MInitial:
  (token: vlbytes 0 token_max_len) -> // arbitrary bound
  (payload_and_pn_length: payload_and_pn_length_t) ->
  (packet_number_length: PN.packet_number_length_t) ->
  (packet_number: PN.packet_number_t) ->
  long_header_specifics
| MZeroRTT:
  (payload_and_pn_length: payload_and_pn_length_t) ->
  (packet_number_length: PN.packet_number_length_t) ->
  (packet_number: PN.packet_number_t) ->
  long_header_specifics
| MHandshake:
  (payload_and_pn_length: payload_and_pn_length_t) ->
  (packet_number_length: PN.packet_number_length_t) ->
  (packet_number: PN.packet_number_t) ->
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
  (packet_number_length: PN.packet_number_length_t) ->
  (packet_number: PN.packet_number_t) ->
  header

let is_initial (h: header) : Tot bool =
  if MLong? h then MInitial? (MLong?.spec h) else false

let is_zero_rtt (h: header) : Tot bool =
  if MLong? h then MZeroRTT? (MLong?.spec h) else false

let is_handshake (h: header) : Tot bool =
  if MLong? h then MHandshake? (MLong?.spec h) else false

let is_retry (h: header) : Tot bool =
  if MLong? h then MRetry? (MLong?.spec h) else false

let pn_length (h: header { ~ (is_retry h) }) : Tot PN.packet_number_length_t =
  match h with
  | MLong _ _ _ spec ->
    begin match spec with
    | MInitial _ _ pnl _ -> pnl
    | MZeroRTT _ pnl _ -> pnl
    | MHandshake _ pnl _ -> pnl
    end
  | MShort _ _ _ pnl _ -> pnl

let packet_number (h: header {~ (is_retry h)}) : Tot PN.packet_number_t =
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


(* Payload length *)

let has_payload_length
  (h: header)
: Tot bool
= MLong? h && (not (MRetry? (MLong?.spec h)))

let payload_length 
  (h: header { has_payload_length h })
: Tot U62.t
= match MLong?.spec h with
  | MInitial _ pl _ _ -> pl
  | MZeroRTT pl _ _ -> pl
  | MHandshake pl _ _ -> pl

(* Correctness of a packet wrt. parsing parameters (cid_len, window) *)

module Secret = Lib.IntTypes

let is_valid_header (h: header) (cid_len: nat) (last: nat) : Tot Type0 =
  (MShort? h ==> dcid_len h == cid_len) /\
  ((~ (is_retry h)) ==> PN.in_window (Secret.v (pn_length h) - 1) last (Secret.v (packet_number h)))
