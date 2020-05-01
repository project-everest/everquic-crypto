module QUIC.Impl.Header.Parse

open QUIC.Spec.Header.Parse
open QUIC.Impl.Header.Base

friend QUIC.Spec.Header.Parse

module LP = LowParse.Low.Base
module Public = QUIC.Impl.Header.Public
module U8 = FStar.UInt8
module SecretBuffer = QUIC.Secret.Buffer
module Spec = QUIC.Spec.Header.Parse
module PN = QUIC.Impl.PacketNumber

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

let public_header_len_correct'
  (h: header)
  (m: HS.mem)
  (pn: PN.packet_number_t)
: Lemma (
    let gh = g_header h m pn in
    let cid_len = dcid_len h in
    let last = last_packet_number gh in
    let (| ph, pn' |) = synth_header_recip cid_len last gh in
    Public.g_header (p_header h) m == ph /\
    U32.v (public_header_len h) == Seq.length (LP.serialize (Public.serialize_header cid_len) ph) 
  )
= public_header_len_correct h;
  public_g_header_p_header h m pn;
  Public.header_len_correct (dcid_len h) m (p_header h)

#restart-solver

let public_header_len_is_pn_offset
  h m pn
= public_header_len_correct' h m pn

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
  public_header_len_correct' h m pn;
  assert (Seq.length (LP.serialize (Public.serialize_header cid_len) ph) == U32.v (public_header_len h));
  if is_retry h
  then
    assert (Secret.v (header_len h) == Spec.header_len (g_header h m pn))
  else begin
    assert (pn_offset gh + Secret.v (Spec.pn_length gh) == Spec.header_len gh);
    assert (pn_offset gh == Seq.length (LP.serialize (Public.serialize_header cid_len) ph));
    assert (Secret.v (header_len h) == Spec.header_len (g_header h m pn))
  end

let last_pn
  (is_retry: bool)
  (pn: PN.packet_number_t)
: Tot PN.last_packet_number_t
= if is_retry
  then Secret.to_u64 0uL
  else
    let cond = Secret.lognot_one_bit (pn `Secret.secrets_are_equal_62` Secret.to_u64 0uL) in
    pn `Secret.sub` cond

let last_pn_correct
  (h: header)
  (m: HS.mem)
  (pn: PN.packet_number_t)
: Lemma
  (last_packet_number (g_header h m pn) == last_pn (is_retry h) pn)
= ()

let write_header
  h pn out out_len
= let m = HST.get () in
  public_header_len_correct' h m pn;
  let cid_len = dcid_len h in
  let last = last_pn (is_retry h) pn in
  last_pn_correct h m pn;
  let ph = p_header h in
  serialize_header_eq cid_len last (g_header h m pn);
  let len = Public.write_header cid_len ph out out_len in
  if is_retry h
  then ()
  else begin
    assert (len == Public.header_len ph);
    let pn_len = pn_length h in
    let m1 = HST.get () in
    SecretBuffer.with_buffer_hide
      #unit
      out
      len
      (len `U32.add` 4ul)
      m1
      B.loc_none
      B.loc_none
      0ul 0ul 0ul 4ul 0ul 0ul
      (fun _ contl cont _ _ ->
        contl == LP.serialize (Public.serialize_header cid_len) (Public.g_header ph m) /\
        Seq.slice cont 0 (Secret.v pn_len) `Seq.equal` LP.serialize (PN.serialize_packet_number last pn_len) pn
      )
      (fun _ _ bs _ ->
        PN.write_packet_number last pn_len pn bs
      )
  end
  
#pop-options

#push-options "--z3rlimit 64"

#restart-solver

let putative_pn_offset
  cid_len b b_len
=
  let h = HST.get () in
  let input = LP.make_slice b b_len in
  assert (LP.bytes_of_slice_from h input 0ul `Seq.equal` B.as_seq h b);
  LP.valid_facts (Public.parse_header cid_len) h input 0ul;
  let res = LP.validate_bounded_strong_prefix (Public.validate_header cid_len) input 0ul in
  if res `U32.gt` LP.validator_max_length
  then None
  else Some res

#pop-options
