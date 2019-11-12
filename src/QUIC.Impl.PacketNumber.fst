module QUIC.Impl.PacketNumber
open QUIC.Spec.Base
open LowParse.Low.Combinators
open LowParse.Low.BoundedInt

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
  last pn_len
= read_synth
    _
    (synth_packet_number last pn_len)
    (fun x -> synth_packet_number last pn_len x)
    (read_bounded_integer' pn_len)
    ()
