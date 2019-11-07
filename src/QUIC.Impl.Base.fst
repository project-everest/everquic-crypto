module QUIC.Impl.Base
open QUIC.Spec.Base

module B = LowStar.Buffer
module U8 = FStar.UInt8
module U64 = FStar.UInt64
module U32 = FStar.UInt32
module Spec = QUIC.Spec.Base

/// Information stored in a QUIC header. This is a Low* type passed by value --
/// it's a little expensive. Consider passing it by reference in ``encrypt``?
///
/// Note that we try to follow the convention of buffer arguments followed by
/// their lengths.

noeq type long_header_specifics =
  | BInitial:
    payload_length: uint62_t ->
    packet_number: uint62_t ->
    packet_number_length: packet_number_length_t ->
    token: B.buffer U8.t -> (* I reordered those so that the extracted code for this type is a tagged union with common prefixes *)
    token_length: U32.t { let v = U32.v token_length in v == B.length token /\ 0 <= v /\ v <= token_max_len  } ->
    long_header_specifics
  | BZeroRTT:
    payload_length: uint62_t ->
    packet_number: uint62_t ->
    packet_number_length: packet_number_length_t ->
    long_header_specifics
  | BHandshake:
    payload_length: uint62_t ->
    packet_number: uint62_t ->
    packet_number_length: packet_number_length_t ->
    long_header_specifics
  | BRetry:
    unused: bitfield 4 ->
    odcid: B.buffer U8.t ->
    odcil: U32.t { let v = U32.v odcil in v = B.length odcid /\ 0 <= v /\ v <= 20 } ->
    long_header_specifics

noeq type header =
  | BLong:
    version: U32.t ->
    dcid: B.buffer U8.t ->
    dcil: U32.t { let v = U32.v dcil in v == B.length dcid /\ 0 <= v /\ v <= 20 } ->
    scid: B.buffer U8.t ->
    scil: U32.t { let v = U32.v scil in v == B.length scid /\ 0 <= v /\ v <= 20 } ->
    spec: long_header_specifics ->
    header
  | BShort:
    spin: bool ->
    phase: bool ->
    cid: B.buffer U8.t ->
    cid_len: U32.t{
      let l = U32.v cid_len in
      l == B.length cid /\
      0 <= l /\ l <= 20
    } ->
    packet_number: uint62_t ->
    packet_number_length: packet_number_length_t ->
    header

module HS = FStar.HyperStack

let header_live (h: header) (m: HS.mem) : GTot Type0 =
  match h with
  | BShort spin phase cid cid_len packet_number packet_number_length ->
    B.live m cid
  | BLong version dcid dcil scid scil spec ->
    B.live m dcid /\ B.live m scid /\
    begin match spec with
    | BInitial payload_length packet_number packet_number_length token token_length ->
      B.live m token
    | BRetry unused odcid odcil ->
      B.live m odcid
    | _ -> True
    end

let header_footprint (h: header) : GTot B.loc =
  match h with
  | BShort spin phase cid cid_len packet_number packet_number_length ->
    B.loc_buffer cid
  | BLong version dcid dcil scid scil spec ->
    (B.loc_buffer dcid `B.loc_union` B.loc_buffer scid) `B.loc_union`
    begin match spec with
    | BInitial payload_length packet_number packet_number_length token token_length ->
      B.loc_buffer token
    | BRetry unused odcid odcil ->
      B.loc_buffer odcid
    | _ -> B.loc_none
    end

module FB = FStar.Bytes

let g_header (h: header) (m: HS.mem) : GTot Spec.header =
  match h with
  | BShort spin phase cid cid_len packet_number packet_number_length ->
    MShort spin phase (FB.hide (B.as_seq m cid)) packet_number_length packet_number
  | BLong version dcid dcil scid scil spec ->
    MLong version (FB.hide (B.as_seq m dcid)) (FB.hide (B.as_seq m scid))
      begin match spec with
      | BInitial payload_length packet_number packet_number_length token token_length ->
        MInitial (FB.hide (B.as_seq m token)) payload_length packet_number_length packet_number
      | BZeroRTT payload_length packet_number packet_number_length ->
        MZeroRTT payload_length packet_number_length packet_number
      | BHandshake payload_length packet_number packet_number_length ->
        MHandshake payload_length packet_number_length packet_number
      | BRetry unused odcid odcil ->
        MRetry unused (FB.hide (B.as_seq m odcid))
      end

let frame_header
  (h: header)
  (l: B.loc)
  (m1 m2: HS.mem)
: Lemma
  (requires (header_live h m1 /\ B.modifies l m1 m2 /\ B.loc_disjoint l (header_footprint h)))
  (ensures (header_live h m2 /\ g_header h m2 == g_header h m1))
= ()
