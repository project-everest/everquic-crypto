module QUIC.Spec.Header.Parse

module PN = QUIC.Spec.PacketNumber
module Public = QUIC.Spec.Header.Public
module LP = LowParse.Spec.Combinators
module Secret = QUIC.Secret.Int
module BF = LowParse.BitFields
module U8 = FStar.UInt8
module Seq = QUIC.Secret.Seq
module U64 = FStar.UInt64
module Cast = FStar.Int.Cast

let protected_bits_pn_length
  (is_short: bool)
  (pb: bitfield (if is_short then 5 else 4))
: Tot PN.packet_number_length_t
= Secret.to_u32 #Secret.U8 (1uy `Secret.add` Secret.get_bitfield #Secret.U8 pb 0ul 2ul)

let get_pn_length
  (h: Public.header)
: Tot PN.packet_number_length_t 
= protected_bits_pn_length (Public.PShort? h) (Public.get_protected_bits h)

let protected_bits_reserved
  (is_short: bool)
  (pb: bitfield (if is_short then 5 else 4))
: Tot (bitfield 2)
= if is_short
  then BF.uint8.BF.get_bitfield pb 3 5
  else BF.uint8.BF.get_bitfield pb 2 4

let get_reserved_bits
  (h: Public.header)
: Tot (bitfield 2)
= protected_bits_reserved (Public.PShort? h) (Public.get_protected_bits h)

let packet_number_opt
  (cid_len: short_dcid_len_t)
  (last: PN.last_packet_number_t)
  (h: Public.header' cid_len)
: Tot Type0
= if Public.is_retry h
  then unit
  else PN.packet_number_t' last (get_pn_length h)

let parse_packet_number_opt_kind = LP.strong_parser_kind 0 4 None

let parse_packet_number_opt
  (cid_len: short_dcid_len_t)
  (last: PN.last_packet_number_t)
  (h: Public.header' cid_len)
: Tot (LP.parser parse_packet_number_opt_kind (packet_number_opt cid_len last h))
= if Public.is_retry h
  then LP.weaken parse_packet_number_opt_kind LP.parse_empty
  else LP.weaken parse_packet_number_opt_kind (PN.parse_packet_number last (get_pn_length h))

let serialize_packet_number_opt
  (cid_len: short_dcid_len_t)
  (last: PN.last_packet_number_t)
  (h: Public.header' cid_len)
: Tot (LP.serializer (parse_packet_number_opt cid_len last h))
= if Public.is_retry h
  then LP.serialize_weaken parse_packet_number_opt_kind LP.serialize_empty
  else LP.serialize_weaken parse_packet_number_opt_kind (PN.serialize_packet_number last (get_pn_length h))

let packet_number_prop
  (last: PN.last_packet_number_t)
  (h: header)
: GTot bool
= if not (is_retry h)
  then PN.in_window (Secret.v (pn_length h) - 1) (Secret.v last) (Secret.v (packet_number h))
  else true

module U32 = FStar.UInt32

let short_dcid_len_prop
  (short_dcid_len: short_dcid_len_t)
  (h: header)
: Tot bool
= if MShort? h
  then dcid_len h = U32.v short_dcid_len
  else true

unfold
let parse_header_prop
  (short_dcid_len: short_dcid_len_t)
  (last: PN.last_packet_number_t)
  (m: header)
: GTot bool
= short_dcid_len_prop short_dcid_len m &&
  packet_number_prop last m

inline_for_extraction
type header'
  (short_dcid_len: short_dcid_len_t)
  (last: PN.last_packet_number_t)
= LP.parse_filter_refine (parse_header_prop short_dcid_len last)

let protected_bits_key_phase
  (x: bitfield 5)
: GTot bool
= BF.uint8.BF.get_bitfield x 2 3 = 1uy

let mk_short_protected_bits
  (reserved_bits: bitfield 2)
  (key_phase: bool)
  (pnl: PN.packet_number_length_t)
: GTot (bitfield 5)
= BF.set_bitfield_bound #8 0 5 0 2 (Secret.v pnl - 1);
  BF.set_bitfield_bound #8 (BF.set_bitfield #8 0 0 2 (Secret.v pnl - 1)) 5 2 3 (if key_phase then 1 else 0);
  BF.set_bitfield_bound #8 (BF.set_bitfield #8 (BF.set_bitfield #8 0 0 2 (Secret.v pnl - 1)) 2 3 (if key_phase then 1 else 0)) 5 3 5 (U8.v reserved_bits);
  BF.uint8.BF.set_bitfield (BF.uint8.BF.set_bitfield (BF.uint8.BF.set_bitfield 0uy 0 2 (U8.uint_to_t (Secret.v pnl - 1))) 2 3 (if key_phase then 1uy else 0uy)) 3 5 reserved_bits

let protected_bits_pn_length_prop
  (is_short: bool)
  (pb: bitfield (if is_short then 5 else 4))
: Lemma
  (Secret.v (protected_bits_pn_length is_short pb) == U8.v (BF.uint8.BF.get_bitfield pb 0 2) + 1)
  [SMTPat (protected_bits_pn_length is_short pb)]
= ()

#push-options "--z3rlimit 16 --max_fuel 2"

let mk_short_protected_bits_correct
  (reserved_bits: bitfield 2)
  (key_phase: bool)
  (pnl: PN.packet_number_length_t)
: Lemma
  (
    let b = mk_short_protected_bits reserved_bits key_phase pnl in
    protected_bits_pn_length true b == pnl /\
    protected_bits_reserved true b == reserved_bits /\
    protected_bits_key_phase b == key_phase /\
    True
  )
= ()

let mk_short_protected_bits_complete
  (pb: bitfield 5)
: Lemma
  (
    mk_short_protected_bits (protected_bits_reserved true pb) (protected_bits_key_phase pb) (protected_bits_pn_length true pb) == pb
  )
= let pb' = mk_short_protected_bits (protected_bits_reserved true pb) (protected_bits_key_phase pb) (protected_bits_pn_length true pb) in
  BF.get_bitfield_full #5 (U8.v pb');
  BF.get_bitfield_full #5 (U8.v pb);
  BF.get_bitfield_size 5 8 (U8.v pb) 0 5;
  BF.get_bitfield_size 5 8 (U8.v pb') 0 5;
  assert_norm (BF.get_bitfield_partition_prop #8 (U8.v pb) (U8.v pb') 0 5 [2; 3] <==> (
    (BF.uint8.BF.v (BF.uint8.BF.get_bitfield pb 0 2) == BF.uint8.BF.v (BF.uint8.BF.get_bitfield pb' 0 2)) /\
    (BF.uint8.BF.v (BF.uint8.BF.get_bitfield pb 2 3) == BF.uint8.BF.v (BF.uint8.BF.get_bitfield pb' 2 3)) /\
    (BF.uint8.BF.v (BF.uint8.BF.get_bitfield pb 3 5) == BF.uint8.BF.v (BF.uint8.BF.get_bitfield pb' 3 5))
  ));
  BF.get_bitfield_partition #8 (U8.v pb) (U8.v pb') 0 5 [2; 3]

#pop-options

let mk_long_protected_bits
  (reserved_bits: bitfield 2)
  (pnl: PN.packet_number_length_t)
: GTot (bitfield 4)
= BF.set_bitfield_bound #8 0 4 0 2 (Secret.v pnl - 1);
  BF.set_bitfield_bound #8 (BF.set_bitfield #8 0 0 2 (Secret.v pnl - 1)) 4 2 4 (U8.v reserved_bits);
  BF.uint8.BF.set_bitfield (BF.uint8.BF.set_bitfield 0uy 0 2 (U8.uint_to_t (Secret.v pnl - 1))) 2 4 reserved_bits

let mk_long_protected_bits_correct
  (reserved_bits: bitfield 2)
  (pnl: PN.packet_number_length_t)
: Lemma
  (
    let b = mk_long_protected_bits reserved_bits pnl in
    protected_bits_pn_length false b == pnl /\
    protected_bits_reserved false b == reserved_bits
  )
= ()

let mk_long_protected_bits_complete
  (pb: bitfield 4)
: Lemma
  (
    mk_long_protected_bits (protected_bits_reserved false pb) (protected_bits_pn_length false pb) == pb
  )
= let pb' = mk_long_protected_bits (protected_bits_reserved false pb) (protected_bits_pn_length false pb) in
  BF.get_bitfield_full #4 (U8.v pb');
  BF.get_bitfield_full #4 (U8.v pb);
  BF.get_bitfield_size 4 8 (U8.v pb) 0 4;
  BF.get_bitfield_size 4 8 (U8.v pb') 0 4;
  assert (
      (BF.uint8.BF.v (BF.uint8.BF.get_bitfield pb 0 2) == BF.uint8.BF.v (BF.uint8.BF.get_bitfield pb' 0 2)) /\
    (BF.uint8.BF.v (BF.uint8.BF.get_bitfield pb 2 4) == BF.uint8.BF.v (BF.uint8.BF.get_bitfield pb' 2 4))
  );
  BF.get_bitfield_partition_2_gen #8 0 2 4 (U8.v pb) (U8.v pb')

let synth_header
  (short_dcid_len: short_dcid_len_t)
  (last: PN.last_packet_number_t)
  (x: dtuple2 (Public.header' short_dcid_len) (packet_number_opt short_dcid_len last))
: GTot (header' short_dcid_len last)
= let (| h, pn |) = x in
  match h with
  | Public.PShort protected_bits spin dcid ->
    MShort (protected_bits_reserved true protected_bits) spin (protected_bits_key_phase protected_bits) dcid (protected_bits_pn_length true protected_bits) pn
  | Public.PLong protected_bits version dcid scid spec ->
    let pnl = protected_bits_pn_length false protected_bits in
    let rb = protected_bits_reserved false protected_bits in
    MLong version dcid scid
      begin match spec with
      | Public.PRetry odcid ->
        MRetry protected_bits odcid
      | Public.PInitial token payload_and_pn_length ->
        MInitial rb token payload_and_pn_length pnl pn
      | Public.PHandshake payload_and_pn_length ->
        MHandshake rb payload_and_pn_length pnl pn
      | Public.PZeroRTT payload_and_pn_length ->
        MZeroRTT rb payload_and_pn_length pnl pn
      end

let synth_header_recip
  (short_dcid_len: short_dcid_len_t)
  (last: PN.last_packet_number_t)
  (x: header' short_dcid_len last)
: GTot (dtuple2 (Public.header' short_dcid_len) (packet_number_opt short_dcid_len last))
= match x with
  | MShort rb spin key_phase dcid pnl pn ->
    mk_short_protected_bits_correct rb key_phase pnl;
    (| Public.PShort (mk_short_protected_bits rb key_phase pnl) spin dcid, pn |)
  | MLong version dcid scid spec ->
    begin match spec with
    | MRetry unused odcid ->
      (| Public.PLong unused version dcid scid (Public.PRetry odcid), () |)
    | MInitial rb token payload_and_pn_length pnl pn ->
      mk_long_protected_bits_correct rb pnl;
      (| Public.PLong (mk_long_protected_bits rb pnl) version dcid scid (Public.PInitial token payload_and_pn_length), pn |)
    | MHandshake rb payload_and_pn_length pnl pn ->
      mk_long_protected_bits_correct rb pnl;
      (| Public.PLong (mk_long_protected_bits rb pnl) version dcid scid (Public.PHandshake payload_and_pn_length), pn |)
    | MZeroRTT rb payload_and_pn_length pnl pn ->
      mk_long_protected_bits_correct rb pnl;
      (| Public.PLong (mk_long_protected_bits rb pnl) version dcid scid (Public.PZeroRTT payload_and_pn_length), pn |)
    end

let synth_header_injective
  (short_dcid_len: short_dcid_len_t)
  (last: PN.last_packet_number_t)
: Lemma
  (LP.synth_injective #(dtuple2 (Public.header' short_dcid_len) (packet_number_opt short_dcid_len last)) #(header' short_dcid_len last)  (synth_header short_dcid_len last))
  [SMTPat (LP.synth_injective #(dtuple2 (Public.header' short_dcid_len) (packet_number_opt short_dcid_len last)) #(header' short_dcid_len last) (synth_header short_dcid_len last))]
= LP.synth_inverse_intro' (synth_header_recip short_dcid_len last) (synth_header short_dcid_len last) (fun (x: dtuple2 (Public.header' short_dcid_len) (packet_number_opt short_dcid_len last)) ->
    let (| h, pn |) = x in
    match h with
    | Public.PShort protected_bits spin dcid ->
      mk_short_protected_bits_complete protected_bits
    | Public.PLong protected_bits version dcid scid spec ->
      begin match spec with
      | Public.PRetry odcid -> ()
      | _ -> mk_long_protected_bits_complete protected_bits
      end
  );
  LP.synth_inverse_synth_injective (synth_header short_dcid_len last) (synth_header_recip short_dcid_len last)

let synth_header_inverse
  (short_dcid_len: short_dcid_len_t)
  (last: PN.last_packet_number_t)
: Lemma
  (LP.synth_inverse #(dtuple2 (Public.header' short_dcid_len) (packet_number_opt short_dcid_len last)) #(header' short_dcid_len last) (synth_header short_dcid_len last) (synth_header_recip short_dcid_len last))
  [SMTPat (LP.synth_inverse #(dtuple2 (Public.header' short_dcid_len) (packet_number_opt short_dcid_len last)) #(header' short_dcid_len last) (synth_header short_dcid_len last) (synth_header_recip short_dcid_len last))]
= LP.synth_inverse_intro' (synth_header short_dcid_len last) (synth_header_recip short_dcid_len last) (fun (x: header' short_dcid_len last) ->
    match x with
    | MShort rb spin key_phase dcid pnl pn ->
      mk_short_protected_bits_correct rb key_phase pnl
    | MLong version dcid scid spec ->
      begin match spec with
      | MRetry unused odcid -> ()
      | MInitial rb token payload_and_pn_length pnl pn ->
        mk_long_protected_bits_correct rb pnl
      | MHandshake rb payload_and_pn_length pnl pn ->
        mk_long_protected_bits_correct rb pnl
      | MZeroRTT rb payload_and_pn_length pnl pn ->
        mk_long_protected_bits_correct rb pnl
      end
  )

let parse_header_kind
  (short_dcid_len: short_dcid_len_t)
: Tot (k: LP.parser_kind {
    k.LP.parser_kind_subkind == Some LP.ParserStrong /\
    k.LP.parser_kind_low > 0 /\
    begin match k.LP.parser_kind_high with
    | None -> False
    | Some max -> max < header_len_bound
    end
  })
= LP.parse_filter_kind (Public.parse_header_kind short_dcid_len) `LP.and_then_kind` parse_packet_number_opt_kind

let parse_header_dtuple
  (short_dcid_len: short_dcid_len_t)
  (last: PN.last_packet_number_t)
: Tot (LP.parser (parse_header_kind short_dcid_len) (dtuple2 (Public.header' short_dcid_len) (packet_number_opt short_dcid_len last)))
= LP.parse_dtuple2
    #_ #(Public.header' short_dcid_len)
    (Public.parse_header short_dcid_len)
    #_ #(packet_number_opt short_dcid_len last)
    (parse_packet_number_opt short_dcid_len last)

let lp_parse_header
  (short_dcid_len: short_dcid_len_t)
  (last: PN.last_packet_number_t)
: Tot (LP.parser (parse_header_kind short_dcid_len) (header' short_dcid_len last))
=
  LP.parse_synth
    #_
    #(dtuple2 (Public.header' short_dcid_len) (packet_number_opt short_dcid_len last))
    #(header' short_dcid_len last)
    (parse_header_dtuple short_dcid_len last)
    (synth_header short_dcid_len last)

let serialize_header_dtuple
  (short_dcid_len: short_dcid_len_t)
  (last: PN.last_packet_number_t)
: Tot (LP.serializer (parse_header_dtuple short_dcid_len last))
= 
  LP.serialize_dtuple2
    #_ #(Public.header' short_dcid_len)
    (Public.serialize_header short_dcid_len)
    #_ #(packet_number_opt short_dcid_len last)
    #(parse_packet_number_opt short_dcid_len last)
    (serialize_packet_number_opt short_dcid_len last)

let serialize_header
  (short_dcid_len: short_dcid_len_t)
  (last: PN.last_packet_number_t)
: Tot (LP.serializer (lp_parse_header short_dcid_len last))
=
  LP.serialize_synth
    #_
    #(dtuple2 (Public.header' short_dcid_len) (packet_number_opt short_dcid_len last))
    #(header' short_dcid_len last)
    _
    (synth_header short_dcid_len last)
    (serialize_header_dtuple short_dcid_len last)
    (synth_header_recip short_dcid_len last)
    ()

let serialize_header_dtuple_eq
  (short_dcid_len: short_dcid_len_t)
  (last: PN.last_packet_number_t)
  (phpn : dtuple2 (Public.header' short_dcid_len) (packet_number_opt short_dcid_len last))
: Lemma (
    LP.serialize (serialize_header_dtuple short_dcid_len last) phpn ==
    LP.bare_serialize_dtuple2
      #_ #(Public.header' short_dcid_len)
      (Public.serialize_header short_dcid_len)
      #_ #(packet_number_opt short_dcid_len last)
      #(parse_packet_number_opt short_dcid_len last)
      (serialize_packet_number_opt short_dcid_len last)
      phpn
  )
= assert (
    LP.serialize (serialize_header_dtuple short_dcid_len last) phpn ==
    LP.serialize
      #_ #(dtuple2 (Public.header' short_dcid_len) (packet_number_opt short_dcid_len last))
      (LP.serialize_dtuple2
        #_ #(Public.header' short_dcid_len)
        (Public.serialize_header short_dcid_len)
        #_ #(packet_number_opt short_dcid_len last)
        #(parse_packet_number_opt short_dcid_len last)
        (serialize_packet_number_opt short_dcid_len last)
      )
      phpn
  );
  LP.serialize_dtuple2_eq'
    #_ #(Public.header' short_dcid_len)
    (Public.serialize_header short_dcid_len)
    #_ #(packet_number_opt short_dcid_len last)
    #(parse_packet_number_opt short_dcid_len last)
    (serialize_packet_number_opt short_dcid_len last)
    phpn

let serialize_header_eq_1
  (short_dcid_len: short_dcid_len_t)
  (last: PN.last_packet_number_t)
  (h: header' short_dcid_len last)
: Lemma
  (LP.serialize (serialize_header short_dcid_len last) h ==
    LP.bare_serialize_synth
    #_
    #(dtuple2 (Public.header' short_dcid_len) (packet_number_opt short_dcid_len last))
    #(header' short_dcid_len last)
    _
    (synth_header short_dcid_len last)
    (serialize_header_dtuple short_dcid_len last)
    (synth_header_recip short_dcid_len last)
    h
  )
=
  LP.serialize_synth_eq
    #_
    #(dtuple2 (Public.header' short_dcid_len) (packet_number_opt short_dcid_len last))
    #(header' short_dcid_len last)
    _
    (synth_header short_dcid_len last)
    (serialize_header_dtuple short_dcid_len last)
    (synth_header_recip short_dcid_len last)
    ()
    h

let serialize_header_eq_2
  (short_dcid_len: short_dcid_len_t)
  (last: PN.last_packet_number_t)
  (h: header' short_dcid_len last)
: Lemma
  (LP.serialize (serialize_header short_dcid_len last) h == (
    let phpn : dtuple2 (Public.header' short_dcid_len) (packet_number_opt short_dcid_len last) = synth_header_recip short_dcid_len last h in
    LP.serialize
      (serialize_header_dtuple short_dcid_len last)
      phpn
  ))
= serialize_header_eq_1 short_dcid_len last h

let serialize_header_eq_3
  (short_dcid_len: short_dcid_len_t)
  (last: PN.last_packet_number_t)
  (h: header' short_dcid_len last)
: Lemma
  (LP.serialize (serialize_header short_dcid_len last) h == (
    let phpn : dtuple2 (Public.header' short_dcid_len) (packet_number_opt short_dcid_len last) = synth_header_recip short_dcid_len last h in
    LP.bare_serialize_dtuple2
      #_ #(Public.header' short_dcid_len)
      (Public.serialize_header short_dcid_len)
      #_ #(packet_number_opt short_dcid_len last)
      #(parse_packet_number_opt short_dcid_len last)
      (serialize_packet_number_opt short_dcid_len last)
      phpn
  ))
= serialize_header_eq_2 short_dcid_len last h;
  let phpn : dtuple2 (Public.header' short_dcid_len) (packet_number_opt short_dcid_len last) = synth_header_recip short_dcid_len last h in
  serialize_header_dtuple_eq short_dcid_len last phpn

#push-options "--z3rlimit 32"

let serialize_header_eq
  (short_dcid_len: short_dcid_len_t)
  (last: PN.last_packet_number_t)
  (h: header' short_dcid_len last)
: Lemma
  (LP.serialize (serialize_header short_dcid_len last) h == (
    let (| ph, pn |) = synth_header_recip short_dcid_len last h in
    LP.serialize (Public.serialize_header short_dcid_len) ph `Seq.append`
    (if is_retry h
     then Seq.empty
     else LP.serialize (PN.serialize_packet_number last (pn_length h)) pn 
  )))
= serialize_header_eq_3 short_dcid_len last h

#pop-options

#push-options "--z3rlimit 16"

let serialize_header_ext
  (short_dcid_len1 short_dcid_len2: short_dcid_len_t)
  (last1 last2: PN.last_packet_number_t)
  (h: header)
: Lemma
  (requires (
    parse_header_prop short_dcid_len1 last1 h /\
    parse_header_prop short_dcid_len2 last2 h
  ))
  (ensures (
    parse_header_prop short_dcid_len1 last1 h /\
    parse_header_prop short_dcid_len2 last2 h /\
    LP.serialize (serialize_header short_dcid_len1 last1) h == LP.serialize (serialize_header short_dcid_len2 last2) h
  ))
= serialize_header_eq short_dcid_len1 last1 h;
  serialize_header_eq short_dcid_len2 last2 h;
  let (| ph, pn |) = synth_header_recip short_dcid_len1 last1 h in
  Public.serialize_header_ext short_dcid_len1 short_dcid_len2 ph;
  if not (is_retry h)
  then PN.serialize_packet_number_ext last1 last2 (pn_length h) pn

let last_packet_number
  (h: header)
: GTot PN.last_packet_number_t
= if is_retry h then Secret.to_u64 0uL else let pn = packet_number h in if Secret.v pn = 0 then Secret.to_u64 0uL else pn `Secret.sub` Secret.to_u64 1uL

let in_window_last_packet_number
  (h: header)
: Lemma
  ((~ (is_retry h)) ==> PN.in_window (Secret.v (pn_length h) - 1) (Secret.v (last_packet_number h)) (Secret.v (packet_number h)))
= ()

(* Fulfill the interface now *)

let header_len
  h
= 
  let s = serialize_header (U32.uint_to_t (dcid_len h)) (last_packet_number h) in
  LP.serialize_length s h;
  Seq.length (LP.serialize s h)

let format_header
  h
= LP.serialize (serialize_header (U32.uint_to_t (dcid_len h)) (last_packet_number h)) h

let format_header_is_short
  h
= let cid_len = U32.uint_to_t (dcid_len h) in
  let last = last_packet_number h in
  serialize_header_eq cid_len last h;
  let (| ph, _ |) = synth_header_recip cid_len last h in
  Public.serialize_header_is_short cid_len ph

let format_header_is_retry
  h
= let cid_len = U32.uint_to_t (dcid_len h) in
  let last = last_packet_number h in
  serialize_header_eq cid_len last h;
  let (| ph, _ |) = synth_header_recip cid_len last h in
  Public.serialize_header_is_retry cid_len ph

#push-options "--z3rlimit 32"

let format_header_pn_length
  h
= let cid_len = U32.uint_to_t (dcid_len h) in
  let last = last_packet_number h in
  serialize_header_eq cid_len last h;
  let (| ph, _ |) = synth_header_recip cid_len last h in
  let x = Seq.index (format_header h) 0 in
  assert (x == Seq.index (LP.serialize (Public.serialize_header cid_len) ph) 0);
  assert (Public.PShort? ph == MShort? h);
  Public.serialize_get_protected_bits cid_len ph;
  BF.get_bitfield_get_bitfield #8 (U8.v x) 0 (if Public.PShort? ph then 5 else 4) 0 2;
  assert (BF.uint8.BF.v (BF.uint8.BF.get_bitfield x 0 2) == Secret.v (pn_length h) - 1)

#pop-options

let pn_offset'
  (h: header)
: GTot nat
= let cid_len = U32.uint_to_t (dcid_len h) in
  let last = last_packet_number h in
  let (| ph, _ |) = synth_header_recip cid_len last h in
  Seq.length (LP.serialize (Public.serialize_header cid_len) ph)

let pn_offset_prop
  (h: header)
: Lemma
  (requires (~ (is_retry h)))
  (ensures (
    0 < pn_offset' h /\
    pn_offset' h + Secret.v (pn_length h) == Seq.length (format_header h)
  ))
=
  let cid_len = U32.uint_to_t (dcid_len h) in
  let last = last_packet_number h in
  serialize_header_eq cid_len last h;
  let pn_len = pn_length h in
  PN.parse_packet_number_kind'_correct last pn_len;
  let (| ph, pn |) = synth_header_recip cid_len last h in
  LP.serialize_length (Public.serialize_header cid_len) ph;
  LP.serialize_length #(PN.parse_packet_number_kind' pn_len) #_ #(PN.parse_packet_number last pn_len <: LP.bare_parser (PN.packet_number_t' last pn_len)) (PN.serialize_packet_number last pn_len <: LP.bare_serializer (PN.packet_number_t' last pn_len)) pn

let pn_offset
  h
= pn_offset_prop h;
  pn_offset' h

let putative_pn_offset
  cid_len x
= if cid_len > 20
  then None
  else
    match LP.parse (Public.parse_header (U32.uint_to_t cid_len)) x with
    | None -> None
    | Some (_, consumed) ->
      LP.parser_kind_prop_equiv (Public.parse_header_kind (U32.uint_to_t cid_len)) (Public.parse_header (U32.uint_to_t cid_len));
      Some (consumed <: nat)

let putative_pn_offset_frame
  cid_len x1 x2
= let Some off = putative_pn_offset cid_len x1 in
  let h1 = Seq.index x1 0 in
  let h2 = Seq.index x2 0 in
  assert (Seq.slice x2 0 off `Seq.equal` (h2 `Seq.cons` Seq.tail (Seq.slice x1 0 off)));
  let is_short = BF.get_bitfield (U8.v h1) 7 8 = 0 in
  let number_of_protected_bits = if is_short then 5 else 4 in
  let new_pb = BF.uint8.BF.get_bitfield h2 0 number_of_protected_bits in
  let h1' = BF.uint8.BF.set_bitfield h1 0 number_of_protected_bits new_pb in
  assert (BF.uint8.BF.v (BF.uint8.BF.get_bitfield h2 0 number_of_protected_bits) == BF.uint8.BF.v (BF.uint8.BF.get_bitfield h1' 0 number_of_protected_bits));
  assert (BF.uint8.BF.v (BF.uint8.BF.get_bitfield h2 number_of_protected_bits 8) == BF.uint8.BF.v (BF.uint8.BF.get_bitfield h1' number_of_protected_bits 8));
  BF.get_bitfield_partition_2 #8 number_of_protected_bits (BF.uint8.BF.v h2) (BF.uint8.BF.v h1');
  let cid_len' = U32.uint_to_t cid_len in
  let p = Public.parse_header cid_len' in
  let s = Public.serialize_header cid_len' in
  let Some (ph, consumed) = LP.parse p x1 in
  assert (consumed == off);
  LP.parse_serialize s ph;
  LP.parse_strong_prefix p x1 (Seq.slice x1 0 off);
  LP.parse_injective p (Seq.slice x1 0 off) (LP.serialize s ph);
  assert (LP.serialize s ph == Seq.slice x1 0 off);
  Public.serialize_header_is_short cid_len' ph;
  Public.serialize_set_protected_bits cid_len' ph new_pb;
  let ph2 = Public.set_protected_bits ph new_pb in
  assert (LP.serialize s ph2 == Seq.slice x2 0 off);
  LP.parse_strong_prefix p (Seq.slice x2 0 off) x2

let putative_pn_offset_correct
  h cid_len
= admit ()

let parse_header
  cid_len last b
= match LP.parse (lp_parse_header (U32.uint_to_t cid_len) (Secret.to_u64 (U64.uint_to_t last))) b with
  | None -> H_Failure
  | Some (h, consumed) -> H_Success h (Seq.slice b consumed (Seq.length b))

let lemma_header_parsing_correct
  h c cid_len last
=
  let s = format_header h in
  in_window_last_packet_number h;
  FStar.Math.Lemmas.pow2_le_compat 64 62;
  let cid_len' = (U32.uint_to_t cid_len) in
  let last' = (Secret.to_u64 (U64.uint_to_t last)) in
  serialize_header_ext (U32.uint_to_t (dcid_len h)) cid_len' (last_packet_number h) last' h;
  LP.parse_serialize (serialize_header cid_len' last') h;
  LP.parse_strong_prefix (lp_parse_header cid_len' last') s (s `Seq.append` c);
  assert (c `Seq.equal` Seq.slice (s `Seq.append` c) (Seq.length s) (Seq.length (s `Seq.append` c)))

let lemma_header_parsing_safe
  cid_len last b1 b2
=
  let cid_len' = (U32.uint_to_t cid_len) in
  let last' = (Secret.to_u64 (U64.uint_to_t last)) in
  match LP.parse (lp_parse_header cid_len' last') b1 with
  | None -> ()
  | Some (h, consumed) ->
    LP.parse_injective (lp_parse_header cid_len' last') b1 b2;
    Seq.lemma_split b1 consumed;
    Seq.lemma_split b2 consumed
