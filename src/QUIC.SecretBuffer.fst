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

let with_buffer_hide #t b from to h0 lin lout x1 x2 x3 x4 x5 x6 post f =
  let bl = B.sub b 0ul from in
  let bs = B.sub b from (to `U32.sub` from) in
  let br = B.offset b to in
  f (Ghost.hide (B.loc_buffer b)) bl bs br
