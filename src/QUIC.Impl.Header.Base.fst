module QUIC.Impl.Header.Base
open QUIC.Spec.Header.Base
include QUIC.Impl.Base

module B = LowStar.Buffer
module U8 = FStar.UInt8
module U64 = FStar.UInt64
module U32 = FStar.UInt32
module Spec = QUIC.Spec.Header.Base
module PN = QUIC.Spec.PacketNumber.Base
module U62 = QUIC.UInt62
module Secret = QUIC.Secret.Int

/// Information stored in a QUIC header. This is a Low* type passed by value --
/// it's a little expensive. Consider passing it by reference in ``encrypt``?
///
/// Note that we try to follow the convention of buffer arguments followed by
/// their lengths.

(* NOTE: in the following header type, payload_and_pn_length contains the
length of the actual payload AND of the packet number. *)

(* NOTE: the header no longer contains the packet number, which is
part of the state, so that the client no longer needs to take care of
it *)

noeq type long_header_specifics =
  | BInitial:
    reserved_bits: secret_bitfield 2 ->
    payload_and_pn_length: payload_and_pn_length_t ->
    packet_number_length: PN.packet_number_length_t ->
    token: B.buffer U8.t -> (* I reordered those so that the extracted code for this type is a tagged union with common prefixes *)
    token_length: U32.t { let v = U32.v token_length in v == B.length token /\ 0 <= v /\ v <= token_max_len  } ->
    long_header_specifics
  | BZeroRTT:
    reserved_bits: secret_bitfield 2 ->
    payload_and_pn_length: payload_and_pn_length_t ->
    packet_number_length: PN.packet_number_length_t ->
    long_header_specifics
  | BHandshake:
    reserved_bits: secret_bitfield 2 ->
    payload_and_pn_length: payload_and_pn_length_t ->
    packet_number_length: PN.packet_number_length_t ->
    long_header_specifics
  | BRetry:
    unused: secret_bitfield 4 ->
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
    reserved_bits: secret_bitfield 2 ->
    spin: bool ->
    phase: secret_bitfield 1 -> // no secret bools in HACL*
    cid: B.buffer U8.t ->
    cid_len: U32.t{
      let l = U32.v cid_len in
      l == B.length cid /\
      0 <= l /\ l <= 20
    } ->
    packet_number_length: PN.packet_number_length_t ->
    header

let dcid_len
  (h: header)
: Tot U32.t
= match h with
  | BShort rb spin phase cid cid_len packet_number_length ->
    cid_len
  | BLong version dcid dcil scid scil spec -> dcil

// inline_for_extraction
let is_retry
  (h: header)
: Tot bool
= BLong? h && BRetry? (BLong?.spec h)

// inline_for_extraction
let pn_length
  (h: header {~ (is_retry h)})
: Tot PN.packet_number_length_t
= match h with
  | BShort _ spin phase cid cid_len packet_number_length ->
    packet_number_length
  | BLong version dcid dcil scid scil spec ->
    begin match spec with
    | BInitial _ payload_and_pn_length packet_number_length token token_length ->
      packet_number_length
    | BZeroRTT _ payload_length packet_number_length ->
      packet_number_length
    | BHandshake _ payload_length packet_number_length ->
      packet_number_length
    end

// inline_for_extraction
let has_payload_length
  (h: header)
: Tot bool
= BLong? h && not (BRetry? (BLong?.spec h))

// inline_for_extraction
let payload_and_pn_length
  (h: header { has_payload_length h })
: Tot payload_and_pn_length_t
= match BLong?.spec h with
  | BInitial _ pl _ _ _ -> pl
  | BZeroRTT _ pl _ -> pl
  | BHandshake _ pl _ -> pl

// inline_for_extraction
let payload_length
  (h: header { has_payload_length h })
: Tot U62.secret
= Secret.to_u64 (payload_and_pn_length h) `Secret.sub` Secret.to_u64 (pn_length h)

module HS = FStar.HyperStack

let header_live (h: header) (m: HS.mem) : GTot Type0 =
  match h with
  | BShort _ spin phase cid cid_len packet_number_length ->
    B.live m cid
  | BLong version dcid dcil scid scil spec ->
    B.live m dcid /\ B.live m scid /\
    begin match spec with
    | BInitial _ payload_length packet_number_length token token_length ->
      B.live m token
    | BRetry unused odcid odcil ->
      B.live m odcid
    | _ -> True
    end

let header_footprint (h: header) : GTot B.loc =
  match h with
  | BShort _ spin phase cid cid_len packet_number_length ->
    B.loc_buffer cid
  | BLong version dcid dcil scid scil spec ->
    (B.loc_buffer dcid `B.loc_union` B.loc_buffer scid) `B.loc_union`
    begin match spec with
    | BInitial _ payload_length packet_number_length token token_length ->
      B.loc_buffer token
    | BRetry unused odcid odcil ->
      B.loc_buffer odcid
    | _ -> B.loc_none
    end

let header_live_loc_not_unused_in_footprint (h: header) (m: HS.mem) : Lemma
  (requires (header_live h m))
  (ensures (B.loc_not_unused_in m `B.loc_includes` header_footprint h))
= ()

module FB = FStar.Bytes

let g_header (h: header) (m: HS.mem) (packet_number: PN.packet_number_t) : GTot Spec.header =
  match h with
  | BShort rb spin phase cid cid_len packet_number_length ->
    MShort (Secret.reveal rb) spin (Secret.v phase = 1) (FB.hide (B.as_seq m cid)) packet_number_length packet_number
  | BLong version dcid dcil scid scil spec ->
    MLong version (FB.hide (B.as_seq m dcid)) (FB.hide (B.as_seq m scid))
      begin match spec with
      | BInitial rb payload_length packet_number_length token token_length ->
        MInitial (Secret.reveal rb) (FB.hide (B.as_seq m token)) payload_length packet_number_length packet_number
      | BZeroRTT rb payload_length packet_number_length ->
        MZeroRTT (Secret.reveal rb) payload_length packet_number_length packet_number
      | BHandshake rb payload_length packet_number_length ->
        MHandshake (Secret.reveal rb) payload_length packet_number_length packet_number
      | BRetry unused odcid odcil ->
        MRetry (Secret.reveal unused) (FB.hide (B.as_seq m odcid))
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
  (packet_number: PN.packet_number_t)
  (l: B.loc)
  (m1 m2: HS.mem)
: Lemma
  (requires (
    header_live h m1 /\
    B.modifies l m1 m2 /\
    B.loc_disjoint l (header_footprint h)
  ))
  (ensures (header_live h m2 /\ g_header h m2 packet_number == g_header h m1 packet_number))
= ()

(* Length computations need to be transparent because the precondition
to QUIC.Impl.encrypt requires the user to provide a destination buffer
large enough to contain the byte representation of the header *)

(* Length of the header without the packet number. It is enough to
check that an output buffer needs at least (public_header_len h + 4)
bytes to serialize a header. *)

module Cast = FStar.Int.Cast

let public_header_len
  (h: header)
: Tot U32.t
= match h with
  | BShort _ spin phase cid cid_len packet_number_length ->
    1ul `U32.add` cid_len
  | BLong version dcid dcil scid scil spec ->
    7ul `U32.add` dcil `U32.add` scil `U32.add`
    begin match spec with
    | BInitial _ payload_and_pn_length packet_number_length token token_length ->
      varint_len (Cast.uint32_to_uint64 token_length) `U32.add` token_length `U32.add` varint_len (payload_and_pn_length)
    | BZeroRTT _ payload_and_pn_length packet_number_length ->
      varint_len (payload_and_pn_length)
    | BHandshake _ payload_and_pn_length packet_number_length ->
      varint_len (payload_and_pn_length)
    | BRetry unused odcid odcil ->
      1ul `U32.add` odcil
    end

(* The actual header length, which is secret because of pn_length *)

#push-options "--z3rlimit 16"

let header_len
  (h: header)
: Tot (x: Secret.uint32 { Secret.v x == U32.v (public_header_len h) + (if is_retry h then 0 else Secret.v (pn_length h)) })
= Secret.to_u32 (public_header_len h) `Secret.add` (if is_retry h then Secret.to_u32 0ul else pn_length h)

#pop-options

(* One can experience trouble reasoning with secrets and the embedded `if` above, hence the following two helpers: *)

let header_len_is_retry
  (h: header { is_retry h })
: Lemma
  (Secret.v (header_len h) == U32.v (public_header_len h))
= ()

let header_len_not_is_retry
  (h: header { ~ (is_retry h) })
: Lemma
  (Secret.v (header_len h) == U32.v (public_header_len h) + Secret.v (pn_length h))
= ()

let header_len_v
  (h: header)
: Lemma
  (Secret.v (header_len h) == U32.v (public_header_len h) + (if is_retry h then 0 else Secret.v (pn_length h)))
= ()


// Callers allocate this type prior to calling decrypt. The contents are only
// meaningful, and plain is only non-null, if the decryption was a success.
noeq
type result = {
  pn: PN.packet_number_t;
  header: header;
  header_len: Secret.uint32;
  plain_len: Secret.uint32;
  total_len: Secret.uint32; (* NOTE: this DOES include the tag *)
}
