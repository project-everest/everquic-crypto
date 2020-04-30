module QUIC.Impl.Header.Parse

open QUIC.Spec.Header.Parse
open QUIC.Impl.Header.Base

friend QUIC.Spec.Header.Parse

module LP = LowParse.Low.Base
module Public = QUIC.Impl.Header.Public
module U8 = FStar.UInt8

[@"opaque_to_smt"]
let impl_short_protected_bits
  (reserved_bits: secret_bitfield 2)
  (key_phase: secret_bitfield 1)
  (pnl: PN.packet_number_length_t)
: Tot (x: Secret.uint8 { Secret.reveal x == mk_short_protected_bits (Secret.reveal reserved_bits) (Secret.v key_phase = 1) pnl })
= Secret.set_bitfield #Secret.U8 (Secret.set_bitfield #Secret.U8 (Secret.set_bitfield #Secret.U8 (Secret.to_u8 0uy) 0ul 2ul (Secret.to_u8 pnl `Secret.sub` Secret.to_u8 1uy)) 2ul 3ul key_phase) 3ul 5ul reserved_bits

[@"opaque_to_smt"]
let impl_long_protected_bits
  (reserved_bits: secret_bitfield 2)
  (pnl: PN.packet_number_length_t)
: Tot (x: Secret.uint8 { Secret.reveal x == mk_long_protected_bits (Secret.reveal reserved_bits) pnl })
= Secret.set_bitfield #Secret.U8 (Secret.set_bitfield #Secret.U8 (Secret.to_u8 0uy) 0ul 2ul (Secret.to_u8 pnl `Secret.sub` Secret.to_u8 1uy)) 2ul 4ul reserved_bits

let p_header
  (h: header)
: Tot Public.header
= match h with
  | BShort rb spin phase cid cid_len pnl ->
    Public.PShort (impl_short_protected_bits rb phase pnl) spin cid cid_len
  | BLong version dcid dcil scid scil spec ->
    begin match spec with
    | BInitial rb payload_and_pn_length pnl token token_length ->
      Public.PLong (impl_long_protected_bits rb pnl) version dcid dcil scid scil (Public.PInitial payload_and_pn_length token token_length)
    | BZeroRTT rb payload_and_pn_length pnl ->
      Public.PLong (impl_long_protected_bits rb pnl) version dcid dcil scid scil (Public.PZeroRTT payload_and_pn_length)
    | BHandshake rb payload_and_pn_length pnl ->
      Public.PLong (impl_long_protected_bits rb pnl) version dcid dcil scid scil (Public.PHandshake payload_and_pn_length)
    | BRetry unused odcid odcil ->
      Public.PLong unused version dcid dcil scid scil (Public.PRetry odcid odcil)
    end

let public_header_len_correct
  (h: header)
: Lemma
  (public_header_len h == Public.header_len (p_header h))
= ()

module Spec = QUIC.Spec.Header.Parse

#push-options "--z3rlimit 1024 --query_stats"

let public_g_header_p_header
  (h: header)
  (m: HS.mem)
  (pn: PN.packet_number_t)
: Lemma (
    let gh = g_header h m pn in
    let cid_len = dcid_len h in
    let last = last_packet_number gh in
    let (| ph, pn' |) = synth_header_recip cid_len last gh in
    Public.g_header (p_header h) m == ph
  )
= ()

#restart-solver

let header_len_correct
  h m pn
=
  allow_inversion header;
  allow_inversion long_header_specifics;
  let gh = g_header h m pn in
  let cid_len = dcid_len h in
  let last = last_packet_number gh in
  let (| ph, pn' |) = synth_header_recip cid_len last gh in
  public_g_header_p_header h m pn;
  assert (Public.g_header (p_header h) m == ph);
  serialize_header_eq cid_len last gh;
  Public.header_len_correct cid_len m (p_header h);
  public_header_len_correct h;
  assert (Seq.length (LP.serialize (Public.serialize_header cid_len) ph) == U32.v (public_header_len h));
  if is_retry h
  then
    assert (Secret.v (header_len h) == Spec.header_len (g_header h m pn))
  else begin
    assert (pn_offset gh + Secret.v (Spec.pn_length gh) == Spec.header_len gh);
    assert (pn_offset gh == Seq.length (LP.serialize (Public.serialize_header cid_len) ph));
    assert (Secret.v (header_len h) == Spec.header_len (g_header h m pn))
  end

#pop-options
