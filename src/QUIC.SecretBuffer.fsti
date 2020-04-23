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

inline_for_extraction
noextract
val with_buffer_hide
  (#t: Type)
  (b: B.buffer U8.t)
  (lin: Ghost.erased B.loc { B.loc_disjoint (Ghost.reveal lin) (B.loc_buffer b) })
  (lout: Ghost.erased B.loc { B.loc_disjoint (Ghost.reveal lout) (B.loc_buffer b) })
  (modifies_b: Ghost.erased bool)
  (pre: (cont: Seq.seq U8.t) -> (h: HS.mem) -> GTot Type0)
  (post: (res: t) -> (cont: Seq.seq U8.t) -> (h: HS.mem) -> GTot Type0)
  (f: (
    (h0: HS.mem) ->
    (l: Ghost.erased B.loc) ->
    (bs: B.buffer Secret.uint8 {B.length bs == B.length b}) ->
    HST.Stack t
    (requires (fun h ->
      pre (seq_reveal (B.as_seq h bs)) h0 /\
      B.modifies l h0 h /\
      B.loc_disjoint (Ghost.reveal lin) (Ghost.reveal l) /\
      B.live h bs
    ))
    (ensures (fun h res h' ->
      B.modifies (Ghost.reveal lout `B.loc_union` (if Ghost.reveal modifies_b then B.loc_buffer bs else B.loc_none)) h h' /\
      post res (seq_reveal (B.as_seq h' bs)) h'
    ))
  ))
: HST.Stack t
  (requires (fun h ->
    B.live h b /\
    pre (B.as_seq h b) h
  ))
  (ensures (fun h res h' ->
    B.modifies (Ghost.reveal lout `B.loc_union` (if Ghost.reveal modifies_b then B.loc_buffer b else B.loc_none)) h h' /\
    post res (B.as_seq h' b) h'
  ))
