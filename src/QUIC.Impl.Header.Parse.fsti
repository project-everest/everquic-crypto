module QUIC.Impl.Header.Parse
open QUIC.Spec.Header.Parse
include QUIC.Impl.Header.Base

module HS = FStar.HyperStack
module U32 = FStar.UInt32
module Seq = FStar.Seq
module PN = QUIC.Spec.PacketNumber.Base
module Secret = QUIC.Secret.Int
module Spec = QUIC.Spec.Header.Parse

val header_len_correct
  (h: header)
  (m: HS.mem)
  (pn: PN.packet_number_t)
: Lemma
  (Secret.v (header_len h) == Spec.header_len (g_header h m pn))
