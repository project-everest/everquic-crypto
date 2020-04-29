module QUIC.Secret.Buffer

friend Lib.IntTypes

module Secret = QUIC.Secret.Int
module B = LowStar.Buffer
module U8 = FStar.UInt8
module HS = FStar.HyperStack
module HST = FStar.HyperStack.ST
module Seq = QUIC.Secret.Seq
module Ghost = FStar.Ghost

#set-options "--z3rlimit 64" // --query_stats"

#restart-solver

let seq_hide_eq
  (#t: Secret.inttype { Secret.unsigned t })
  (#sec: Secret.secrecy_level)
  (x: Seq.seq (Secret.uint_t t sec))
: Lemma
  (Seq.seq_hide x `Seq.equal` x)
  [SMTPat (Seq.seq_hide x)]
= ()

let seq_reveal_eq
  (#t: Secret.inttype { Secret.unsigned t })
  (#sec: Secret.secrecy_level)
  (x: Seq.seq (Secret.uint_t t sec))
: Lemma
  (Seq.seq_reveal x `Seq.equal` x)
  [SMTPat (Seq.seq_reveal x)]
= ()

let with_buffer_hide #t b from to h0 lin lout x1 x2 x3 x4 x5 x6 post f =
  let bl = B.sub b 0ul from in
  let bs = B.sub b from (to `U32.sub` from) in
  let br = B.offset b to in
  f (Ghost.hide (B.loc_buffer b)) bl bs br
