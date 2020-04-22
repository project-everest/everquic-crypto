module QUIC.SecretBuffer

friend Lib.IntTypes

module Secret = QUIC.Secret
module B = LowStar.Buffer
module U8 = FStar.UInt8
module HS = FStar.HyperStack
module HST = FStar.HyperStack.ST
module Seq = FStar.Seq
module Ghost = FStar.Ghost

let seq_reveal x = x

let seq_reveal_length #t #sec x = ()

let seq_reveal_index #t #sec x i = ()

let with_buffer_hide #t b lin lout modifies_b pre post f =
  let h0 = HST.get () in
  f h0 (Ghost.hide (B.loc_buffer b)) b
