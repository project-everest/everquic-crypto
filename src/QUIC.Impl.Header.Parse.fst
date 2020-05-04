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
      let spec' = (Public.PInitial payload_and_pn_length token token_length) in
      Public.PLong (impl_long_protected_bits rb pnl) version dcid dcil scid scil spec'
    | BZeroRTT rb payload_and_pn_length pnl ->
      let spec' = (Public.PZeroRTT payload_and_pn_length) in
      Public.PLong (impl_long_protected_bits rb pnl) version dcid dcil scid scil spec'
    | BHandshake rb payload_and_pn_length pnl ->
      let spec' = (Public.PHandshake payload_and_pn_length) in
      Public.PLong (impl_long_protected_bits rb pnl) version dcid dcil scid scil spec'
    | BRetry unused odcid odcil ->
      let spec' = (Public.PRetry odcid odcil) in
      Public.PLong unused version dcid dcil scid scil spec'
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

#pop-options

#push-options "--z3rlimit 16 --query_stats --z3cliopt smt.arith.nl=false"

#restart-solver

let header_len_correct
  h m pn
=
  allow_inversion header;
  allow_inversion long_header_specifics;
  let gh = g_header h m pn in
  let cid_len = dcid_len h in
  let last = last_packet_number gh in
  in_window_last_packet_number gh;
  let (| ph, pn' |) = synth_header_recip cid_len last gh in
  public_g_header_p_header h m pn;
  assert (Public.g_header (p_header h) m == ph);
  serialize_header_eq cid_len last gh;
  Public.header_len_correct cid_len m (p_header h);
  public_header_len_correct h;
  public_header_len_correct' h m pn;
  assert (Seq.length (LP.serialize (Public.serialize_header cid_len) ph) == U32.v (public_header_len h));
  if is_retry h
  then begin
    header_len_is_retry h;
    assert (Secret.v (header_len h) == Spec.header_len (g_header h m pn))
  end else begin
    header_len_not_is_retry h;
    assert (pn_offset gh + Secret.v (Spec.pn_length gh) == Spec.header_len gh);
    assert (pn_offset gh == Seq.length (LP.serialize (Public.serialize_header cid_len) ph));
    assert (Secret.v (header_len h) == Spec.header_len (g_header h m pn))
  end

#pop-options

let last_pn
  (is_retry: bool)
  (pn: PN.packet_number_t)
: Tot PN.last_packet_number_t
= if is_retry
  then Secret.to_u64 0uL
  else
    let cond = Secret.lognot_one_bit (pn `Secret.secrets_are_equal_62` Secret.to_u64 0uL) in
    pn `Secret.sub` cond

#push-options "--z3rlimit 64 --query_stats"

let last_pn_correct
  (h: header)
  (m: HS.mem)
  (pn: PN.packet_number_t)
: Lemma
  (last_packet_number (g_header h m pn) == last_pn (is_retry h) pn)
= ()

#pop-options

#push-options "--z3rlimit 128 --query_stats"

#restart-solver

let write_header
  h pn out out_len
= let m = HST.get () in
  header_len_correct h m pn;
  public_header_len_correct' h m pn;
  let cid_len = dcid_len h in
  let last = last_pn (is_retry h) pn in
  last_pn_correct h m pn;
  let ph = p_header h in
  in_window_last_packet_number (g_header h m pn);
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
      1ul 0ul 0ul 4ul 1ul 0ul
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

let impl_protected_bits_pn_length
  (is_short: bool)
  (pb: secret_bitfield (if is_short then 5 else 4))
: Tot (y: PN.packet_number_length_t { y == protected_bits_pn_length is_short (Secret.reveal pb) })
= Secret.to_u32 #Secret.U8 (Secret.to_u8 1uy `Secret.add` Secret.get_bitfield #Secret.U8 pb 0ul 2ul)

let impl_protected_bits_reserved
  (is_short: bool)
  (pb: secret_bitfield (if is_short then 5 else 4))
: Tot (y: secret_bitfield 2 { Secret.reveal y == protected_bits_reserved is_short (Secret.reveal pb) })
= if is_short
  then Secret.get_bitfield #Secret.U8 pb 3ul 5ul
  else Secret.get_bitfield #Secret.U8 pb 2ul 4ul

let impl_protected_bits_key_phase
  (x: secret_bitfield 5)
: Tot (y: secret_bitfield 1 { protected_bits_key_phase (Secret.reveal x) == (Secret.v y = 1) })
= Secret.get_bitfield #Secret.U8 x 2ul 3ul

let header_p
  (h: Public.header)
: Tot header
= match h with
  | Public.PShort pb spin cid cid_len ->
    let rb = impl_protected_bits_reserved true pb in
    let phase = impl_protected_bits_key_phase pb in
    let pnl = impl_protected_bits_pn_length true pb in
    BShort rb spin phase cid cid_len pnl
  | Public.PLong pb version dcid dcil scid scil spec ->
    let rb = impl_protected_bits_reserved false pb in
    let pnl = impl_protected_bits_pn_length false pb in
    BLong version dcid dcil scid scil
    begin match spec with
    | Public.PInitial payload_and_pn_length token token_length ->
      BInitial rb payload_and_pn_length pnl token token_length
    | Public.PHandshake payload_and_pn_length ->
      BHandshake rb payload_and_pn_length pnl
    | Public.PZeroRTT payload_and_pn_length ->
      BZeroRTT rb payload_and_pn_length pnl
    | Public.PRetry odcid odcil ->
      BRetry pb odcid odcil
    end

#push-options "--z3rlimit 16"

let g_header_header_p
  (cid_len: short_dcid_len_t)
  (last: PN.last_packet_number_t)
  (m: HS.mem)
  (ph: Public.header { Public.parse_header_prop cid_len (Public.g_header ph m) })
  (pn: PN.packet_number_t)
: Lemma (
    let h = header_p ph in
    let gh = Public.g_header ph m in
    if
      if Public.is_retry ph
      then true
      else
        let pn_len = pn_length h in
        PN.in_window (Secret.v pn_len - 1) (Secret.v last) (Secret.v pn)
    then
      let h' = synth_header cid_len last (| gh, (if Public.is_retry ph then () else pn) |) in
      g_header (header_p ph) m pn == h'
    else
      True
  )
= ()

#pop-options

let parse_public_header_consumes
  (cid_len: short_dcid_len_t)
  (x: bytes)
  (ph: Public.header)
  (m: HS.mem)
: Lemma
  (requires (
    match LP.parse (Public.parse_header cid_len) x with
    | None -> False
    | Some (ph0, _) -> Public.g_header ph m == ph0
  ))
  (ensures (
    let Some (ph0, consumed) = LP.parse (Public.parse_header cid_len) x in
    consumed == U32.v (Public.header_len ph)
  ))
= let Some (ph0, consumed) = LP.parse (Public.parse_header cid_len) x in
  Public.header_len_correct cid_len m ph;
  LP.parse_serialize (Public.serialize_header cid_len) ph0;
  LP.parse_injective (Public.parse_header cid_len) x (LP.serialize (Public.serialize_header cid_len) ph0)

let public_header_len_complete
  (h: Public.header)
: Lemma
  (public_header_len (header_p h) == Public.header_len h)
= ()

#push-options "--z3rlimit 64"

let read_header
  packet packet_len cid_len last
=
  let m = HST.get () in
  assert (Some? (Spec.putative_pn_offset (U32.v cid_len) (B.as_seq m packet)));
  parse_header_exists (U32.v cid_len) (Secret.v last) (B.as_seq m packet);
  lp_parse_header_eq cid_len last (B.as_seq m packet);
  let ph = Public.read_header packet packet_len cid_len in
  let m1 = HST.get () in
  public_header_len_complete ph;
  parse_public_header_consumes cid_len (B.as_seq m packet) ph m1;
  let h = header_p ph in
  if Public.is_retry ph
  then begin
    g_header_header_p cid_len last m ph last;
    (h, last)
  end else begin
    let len = Public.header_len ph in
    LP.parsed_data_is_serialize (Public.serialize_header cid_len) (B.as_seq m packet);
    assert (Seq.index (B.as_seq m packet) 0 == Seq.index (LP.serialize (Public.serialize_header cid_len) (Public.g_header ph m1)) 0);
    Public.serialize_header_is_retry cid_len (Public.g_header ph m1);
    assert (U32.v len + 4 <= B.length packet);
    let pn_len = pn_length h in
    let pn = SecretBuffer.with_buffer_hide
      #PN.packet_number_t
      packet
      len
      packet_len
      m1
      B.loc_none
      B.loc_none
      1ul 0ul 1ul 0ul 1ul 0ul
      (fun pn _ cont _ _ ->
        match LP.parse (PN.parse_packet_number last pn_len) cont with
        | None -> False
        | Some (pn', _) -> pn == pn'
      )
      (fun _ _ bs _ ->
        PN.read_packet_number last pn_len bs
      )
    in
    (h, pn)
  end

#pop-options
