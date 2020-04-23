module QUIC.SecretBuffer

module Secret = QUIC.Secret
module B = LowStar.Buffer
module U8 = FStar.UInt8
module HS = FStar.HyperStack
module HST = FStar.HyperStack.ST
module Seq = FStar.Seq
module Ghost = FStar.Ghost

val seq_reveal
  (#t: Secret.inttype { Secret.unsigned t })
  (#sec: Secret.secrecy_level)
  (x: Seq.seq (Secret.uint_t t sec))
: GTot (Seq.seq (Secret.uint_t t Secret.PUB))

val seq_reveal_length
  (#t: Secret.inttype { Secret.unsigned t })
  (#sec: Secret.secrecy_level)
  (x: Seq.seq (Secret.uint_t t sec))
: Lemma
  (Seq.length (seq_reveal x) == Seq.length x)
  [SMTPat (Seq.length (seq_reveal x))]

val seq_reveal_index
  (#t: Secret.inttype { Secret.unsigned t })
  (#sec: Secret.secrecy_level)
  (x: Seq.seq (Secret.uint_t t sec))
  (i: nat)
: Lemma
  (requires (i < Seq.length x))
  (ensures (
    Secret.v (Seq.index (seq_reveal x) i) == Secret.v (Seq.index x i)
  ))
  [SMTPat (Seq.index (seq_reveal x) i)]

let seq_reveal_pub
  (#t: Secret.inttype { Secret.unsigned t })
  (x: Seq.seq (Secret.uint_t t Secret.PUB))
: Lemma
  (seq_reveal x `Seq.equal` x)
= ()

let seq_reveal_inj
  (#t: Secret.inttype { Secret.unsigned t })
  (#sec: Secret.secrecy_level)
  (x1 x2: Seq.seq (Secret.uint_t t sec))
: Lemma
  (requires (seq_reveal x1 `Seq.equal` seq_reveal x2))
  (ensures (x1 `Seq.equal` x2))
= assert (Seq.length (seq_reveal x1) == Seq.length (seq_reveal x2));
  assert (forall (i: nat { i < Seq.length x1 }) . Seq.index (seq_reveal x1) i == Seq.index (seq_reveal x2) i);
  assert (forall (i: nat { i < Seq.length x1 }) . Secret.v (Seq.index x1 i) == Secret.v (Seq.index x2 i))

module U32 = FStar.UInt32

inline_for_extraction
noextract
val with_buffer_hide
  (#t: Type)
  (b: B.buffer U8.t)
  (from: U32.t)
  (to: U32.t { U32.v from <= U32.v to /\ U32.v to <= B.length b })
  (h0: HS.mem)
  (lin: Ghost.erased B.loc { B.loc_disjoint (Ghost.reveal lin) (B.loc_buffer b) })
  (lout: Ghost.erased B.loc { B.loc_disjoint (Ghost.reveal lout) (B.loc_buffer b) })
  (post: (res: t) ->  (contl: Seq.lseq U8.t (U32.v from)) ->  (cont: Seq.lseq U8.t (U32.v to - U32.v from)) ->  (contr: Seq.lseq U8.t (B.length b - U32.v to)) -> (h: HS.mem) -> GTot Type0)
  (f: (
    (l: Ghost.erased B.loc) ->
    (bl: B.buffer U8.t { B.length bl == (U32.v from) }) ->
    (bs: B.buffer Secret.uint8 { B.length bs == (U32.v to - U32.v from) }) ->
    (br: B.buffer U8.t { B.length br == (B.length b - U32.v to) }) ->
    HST.Stack t
    (requires (fun h ->
      B.modifies l h0 h /\
      B.loc_disjoint (B.loc_buffer bl `B.loc_union` B.loc_buffer bs) (B.loc_buffer br) /\
      B.loc_disjoint (B.loc_buffer bl) (B.loc_buffer bs) /\
      B.loc_disjoint (Ghost.reveal lin `B.loc_union` Ghost.reveal lout) (Ghost.reveal l `B.loc_union` B.loc_buffer bl `B.loc_union` B.loc_buffer bs `B.loc_union` B.loc_buffer br) /\
      B.live h bl /\ B.live h bs /\ B.live h br /\
      B.as_seq h bl == B.as_seq h0 (B.gsub b 0ul from) /\
      seq_reveal (B.as_seq h bs) == B.as_seq h0 (B.gsub b from (to `U32.sub` from)) /\
      B.as_seq h br == B.as_seq h0 (B.gsub b to (B.len b `U32.sub` to))
    ))
    (ensures (fun h res h' ->
      B.modifies (Ghost.reveal lout `B.loc_union` B.loc_buffer bl `B.loc_union` B.loc_buffer bs `B.loc_union` B.loc_buffer br) h h' /\
      post res (B.as_seq h' bl) (seq_reveal (B.as_seq h' bs)) (B.as_seq h' br) h'
    ))
  ))
: HST.Stack t
  (requires (fun h ->
    B.live h b /\
    h0 == h
  ))
  (ensures (fun h res h' ->
    B.modifies (Ghost.reveal lout `B.loc_union` B.loc_buffer b) h h' /\
    post res (B.as_seq h' (B.gsub b 0ul from)) (B.as_seq h' (B.gsub b from (to `U32.sub` from))) (B.as_seq h' (B.gsub b to (B.len b `U32.sub` to))) h'
  ))
