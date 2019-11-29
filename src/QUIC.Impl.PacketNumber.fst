module QUIC.Impl.PacketNumber
open QUIC.Spec.Base
open LowParse.Low.Combinators
open LowParse.Low.BoundedInt
open LowParse.Low.Writers.Instances

friend QUIC.Spec.PacketNumber

module Cast = FStar.Int.Cast
module U64 = FStar.UInt64
module U32 = FStar.UInt32
module U16 = FStar.UInt16
module U8 = FStar.UInt8

let validate_packet_number
  (last: last_packet_number_t)
  (pn_len: packet_number_length_t)
: Tot (validator (parse_packet_number last pn_len))
= validate_synth
    (validate_bounded_integer' pn_len)
    (synth_packet_number last pn_len)
    ()

let jump_packet_number
  last pn_len
= jump_synth
    (jump_bounded_integer' pn_len)
    (synth_packet_number last pn_len)
    ()

let read_packet_number
  last pn_len #rrel #rel sl pos
= let h = HST.get () in
  valid_synth h (parse_bounded_integer (U32.v pn_len)) (synth_packet_number last pn_len) sl pos;
  let x = read_bounded_integer_ct pn_len sl pos in
  synth_packet_number last pn_len x

let swrite_packet_number
  last pn_len pn h0 sout pout_from0
= [@inline_let]
  let _ = synth_packet_number_recip_inverse last pn_len in
  swrite_synth
    (swrite_bounded_integer_ct h0 sout pn_len pout_from0 (synth_packet_number_recip last pn_len pn))
    (synth_packet_number last pn_len)
    (synth_packet_number_recip last pn_len)
    ()
