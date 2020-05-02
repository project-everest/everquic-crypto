module QUIC.Secret.Buffer

module Secret = QUIC.Secret.Int
module B = LowStar.Buffer
module U8 = FStar.UInt8
module HS = FStar.HyperStack
module HST = FStar.HyperStack.ST
module Seq = QUIC.Secret.Seq
module Ghost = FStar.Ghost

module U32 = FStar.UInt32

#set-options "--z3rlimit 16"

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
  (x1 x2 x3 x4 x5: Ghost.erased U32.t)
  (x6: Ghost.erased U32.t {
    U32.v x1 <= U32.v x2 /\ U32.v x2 <= U32.v from /\
    U32.v x3 <= U32.v x4 /\ U32.v x4 <= U32.v to - U32.v from /\
    U32.v x5 <= U32.v x6 /\ U32.v x6 <= B.length b - U32.v to
  })
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
      B.as_seq h bs == Seq.seq_hide #Secret.U8 (B.as_seq h0 (B.gsub b from (to `U32.sub` from))) /\
      B.as_seq h br == B.as_seq h0 (B.gsub b to (B.len b `U32.sub` to))
    ))
    (ensures (fun h res h' ->
      B.modifies (Ghost.reveal lout `B.loc_union` (if U32.v x1 = U32.v x2 then B.loc_none else B.loc_buffer (B.gsub bl x1 (x2 `U32.sub` x1))) `B.loc_union` (if U32.v x3 = U32.v x4 then B.loc_none else B.loc_buffer (B.gsub bs x3 (x4 `U32.sub` x3))) `B.loc_union` (if U32.v x5 = U32.v x6 then B.loc_none else B.loc_buffer (B.gsub br x5 (x6 `U32.sub` x5)))) h h' /\
      post res (B.as_seq h' bl) (Seq.seq_reveal (B.as_seq h' bs)) (B.as_seq h' br) h'
    ))
  ))
: HST.Stack t
  (requires (fun h ->
    B.live h b /\
    h0 == h
  ))
  (ensures (fun h res h' ->
    B.modifies (Ghost.reveal lout `B.loc_union` (if U32.v x1 = U32.v x2 then B.loc_none else B.loc_buffer (B.gsub b x1 (x2 `U32.sub` x1))) `B.loc_union` (if U32.v x3 = U32.v x4 then B.loc_none else B.loc_buffer (B.gsub b (from `U32.add` x3) (x4 `U32.sub` x3))) `B.loc_union` (if U32.v x5 = U32.v x6 then B.loc_none else B.loc_buffer (B.gsub b (to `U32.add` x5) (x6 `U32.sub` x5)))) h h' /\
    post res (B.as_seq h' (B.gsub b 0ul from)) (B.as_seq h' (B.gsub b from (to `U32.sub` from))) (B.as_seq h' (B.gsub b to (B.len b `U32.sub` to))) h'
  ))

(* NOTE: this CANNOT be derived from with_buffer_hide, because the footprint of a zero-length buffer is not B.loc_none *)

inline_for_extraction
noextract
val with_buffer_hide_weak_modifies
  (#t: Type)
  (b: B.buffer U8.t)
  (from: U32.t)
  (to: U32.t { U32.v from <= U32.v to /\ U32.v to <= B.length b })
  (h0: HS.mem)
  (lin: Ghost.erased B.loc { B.loc_disjoint (Ghost.reveal lin) (B.loc_buffer b) })
  (lout: Ghost.erased B.loc { B.loc_disjoint (Ghost.reveal lout) (B.loc_buffer b) })
  (modifies_left modifies_secret modifies_right: Ghost.erased bool)
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
      B.as_seq h bs == Seq.seq_hide #Secret.U8 (B.as_seq h0 (B.gsub b from (to `U32.sub` from))) /\
      B.as_seq h br == B.as_seq h0 (B.gsub b to (B.len b `U32.sub` to))
    ))
    (ensures (fun h res h' ->
      B.modifies (Ghost.reveal lout `B.loc_union` (if Ghost.reveal modifies_left then B.loc_buffer bl else B.loc_none) `B.loc_union` (if Ghost.reveal modifies_secret then B.loc_buffer bs else B.loc_none) `B.loc_union` (if Ghost.reveal modifies_right then B.loc_buffer br else B.loc_none)) h h' /\
      post res (B.as_seq h' bl) (Seq.seq_reveal (B.as_seq h' bs)) (B.as_seq h' br) h'
    ))
  ))
: HST.Stack t
  (requires (fun h ->
    B.live h b /\
    h0 == h
  ))
  (ensures (fun h res h' ->
    B.modifies (Ghost.reveal lout `B.loc_union` (if Ghost.reveal modifies_left then B.loc_buffer (B.gsub b 0ul from) else B.loc_none) `B.loc_union` (if Ghost.reveal modifies_secret then B.loc_buffer (B.gsub b from (to `U32.sub` from)) else B.loc_none) `B.loc_union` (if Ghost.reveal modifies_right then B.loc_buffer (B.gsub b to (B.len b `U32.sub` to)) else B.loc_none)) h h' /\
    post res (B.as_seq h' (B.gsub b 0ul from)) (B.as_seq h' (B.gsub b from (to `U32.sub` from))) (B.as_seq h' (B.gsub b to (B.len b `U32.sub` to))) h'
  ))

inline_for_extraction
noextract
val with_buffer_hide_from
  (#t: Type)
  (b: B.buffer U8.t)
  (from: U32.t { U32.v from <= B.length b })
  (h0: HS.mem)
  (lin: Ghost.erased B.loc { B.loc_disjoint (Ghost.reveal lin) (B.loc_buffer b) })
  (lout: Ghost.erased B.loc { B.loc_disjoint (Ghost.reveal lout) (B.loc_buffer b) })
  (x1 x2 x3: Ghost.erased U32.t)
  (x4: Ghost.erased U32.t {
    U32.v x1 <= U32.v x2 /\ U32.v x2 <= U32.v from /\
    U32.v x3 <= U32.v x4 /\ U32.v x4 <= B.length b - U32.v from
  })
  (post: (res: t) ->  (contl: Seq.lseq U8.t (U32.v from)) ->  (cont: Seq.lseq U8.t (B.length b - U32.v from)) -> (h: HS.mem) -> GTot Type0)
  (f: (
    (l: Ghost.erased B.loc) ->
    (bl: B.buffer U8.t { B.length bl == (U32.v from) }) ->
    (bs: B.buffer Secret.uint8 { B.length bs == (B.length b - U32.v from) }) ->
    HST.Stack t
    (requires (fun h ->
      B.modifies l h0 h /\
      B.loc_disjoint (B.loc_buffer bl) (B.loc_buffer bs) /\
      B.loc_disjoint (Ghost.reveal lin `B.loc_union` Ghost.reveal lout) (Ghost.reveal l `B.loc_union` B.loc_buffer bl `B.loc_union` B.loc_buffer bs) /\
      B.live h bl /\ B.live h bs /\
      B.as_seq h bl == B.as_seq h0 (B.gsub b 0ul from) /\
      B.as_seq h bs == Seq.seq_hide #Secret.U8 (B.as_seq h0 (B.gsub b from (B.len b `U32.sub` from)))
    ))
    (ensures (fun h res h' ->
      B.modifies (Ghost.reveal lout `B.loc_union` (if U32.v x1 = U32.v x2 then B.loc_none else B.loc_buffer (B.gsub bl x1 (x2 `U32.sub` x1))) `B.loc_union` (if U32.v x3 = U32.v x4 then B.loc_none else B.loc_buffer (B.gsub bs x3 (x4 `U32.sub` x3)))) h h' /\
      post res (B.as_seq h' bl) (Seq.seq_reveal (B.as_seq h' bs)) h'
    ))
  ))
: HST.Stack t
  (requires (fun h ->
    B.live h b /\
    h0 == h
  ))
  (ensures (fun h res h' ->
    B.modifies (Ghost.reveal lout `B.loc_union` (if U32.v x1 = U32.v x2 then B.loc_none else B.loc_buffer (B.gsub b x1 (x2 `U32.sub` x1))) `B.loc_union` (if U32.v x3 = U32.v x4 then B.loc_none else B.loc_buffer (B.gsub b (from `U32.add` x3) (x4 `U32.sub` x3)))) h h' /\
    post res (B.as_seq h' (B.gsub b 0ul from)) (B.as_seq h' (B.gsub b from (B.len b `U32.sub` from))) h'
  ))

inline_for_extraction
noextract
val with_buffer_hide_from_weak_modifies
  (#t: Type)
  (b: B.buffer U8.t)
  (from: U32.t { U32.v from <= B.length b })
  (h0: HS.mem)
  (lin: Ghost.erased B.loc { B.loc_disjoint (Ghost.reveal lin) (B.loc_buffer b) })
  (lout: Ghost.erased B.loc { B.loc_disjoint (Ghost.reveal lout) (B.loc_buffer b) })
  (modifies_left modifies_secret: Ghost.erased bool)
  (post: (res: t) ->  (contl: Seq.lseq U8.t (U32.v from)) ->  (cont: Seq.lseq U8.t (B.length b - U32.v from)) -> (h: HS.mem) -> GTot Type0)
  (f: (
    (l: Ghost.erased B.loc) ->
    (bl: B.buffer U8.t { B.length bl == (U32.v from) }) ->
    (bs: B.buffer Secret.uint8 { B.length bs == (B.length b - U32.v from) }) ->
    HST.Stack t
    (requires (fun h ->
      B.modifies l h0 h /\
      B.loc_disjoint (B.loc_buffer bl) (B.loc_buffer bs) /\
      B.loc_disjoint (Ghost.reveal lin `B.loc_union` Ghost.reveal lout) (Ghost.reveal l `B.loc_union` B.loc_buffer bl `B.loc_union` B.loc_buffer bs) /\
      B.live h bl /\ B.live h bs /\
      B.as_seq h bl == B.as_seq h0 (B.gsub b 0ul from) /\
      B.as_seq h bs == Seq.seq_hide #Secret.U8 (B.as_seq h0 (B.gsub b from (B.len b `U32.sub` from)))
    ))
    (ensures (fun h res h' ->
      B.modifies (Ghost.reveal lout `B.loc_union` (if Ghost.reveal modifies_left then B.loc_buffer bl else B.loc_none) `B.loc_union` (if Ghost.reveal modifies_secret then B.loc_buffer bs else B.loc_none)) h h' /\
      post res (B.as_seq h' bl) (Seq.seq_reveal (B.as_seq h' bs)) h'
    ))
  ))
: HST.Stack t
  (requires (fun h ->
    B.live h b /\
    h0 == h
  ))
  (ensures (fun h res h' ->
    B.modifies (Ghost.reveal lout `B.loc_union` (if Ghost.reveal modifies_left then B.loc_buffer (B.gsub b 0ul from) else B.loc_none) `B.loc_union` (if Ghost.reveal modifies_secret then B.loc_buffer (B.gsub b from (B.len b `U32.sub` from)) else B.loc_none)) h h' /\
    post res (B.as_seq h' (B.gsub b 0ul from)) (B.as_seq h' (B.gsub b from (B.len b `U32.sub` from))) h'
  ))

inline_for_extraction
noextract
let with_whole_buffer_hide_weak_modifies
  (#t: Type)
  (b: B.buffer U8.t)
  (h0: HS.mem)
  (lin: Ghost.erased B.loc { B.loc_disjoint (Ghost.reveal lin) (B.loc_buffer b) })
  (lout: Ghost.erased B.loc { B.loc_disjoint (Ghost.reveal lout) (B.loc_buffer b) })
  (modifies_b: Ghost.erased bool)
  (post: (res: t) -> (cont: Seq.lseq U8.t (B.length b)) -> (h: HS.mem) -> GTot Type0)
  (f: (
    (l: Ghost.erased B.loc) ->
    (bs: B.buffer Secret.uint8 { B.length bs == B.length b }) ->
    HST.Stack t
    (requires (fun h ->
      B.modifies l h0 h /\
      B.loc_disjoint (Ghost.reveal lin `B.loc_union` Ghost.reveal lout) (Ghost.reveal l `B.loc_union` B.loc_buffer bs) /\
      B.live h bs /\
      B.as_seq h bs == Seq.seq_hide #Secret.U8 (B.as_seq h0 b)
    ))
    (ensures (fun h res h' ->
      B.modifies (Ghost.reveal lout `B.loc_union` (if Ghost.reveal modifies_b then B.loc_buffer bs else B.loc_none)) h h' /\
      post res (Seq.seq_reveal (B.as_seq h' bs)) h'
    ))
  ))
: HST.Stack t
  (requires (fun h ->
    B.live h b /\
    h0 == h
  ))
  (ensures (fun h res h' ->
    B.modifies (Ghost.reveal lout `B.loc_union` (if Ghost.reveal modifies_b then B.loc_buffer b else B.loc_none)) h h' /\
    post res (B.as_seq h' b) h'
  ))
= let sq : squash (B.gsub b 0ul (B.len b) == b) =
    B.gsub_zero_length b
  in
  let h0 = HST.get () in
  with_buffer_hide_from_weak_modifies
    b
    0ul
    h0
    lin
    lout
    (Ghost.hide false) modifies_b
    (fun res _ cont h -> post res cont h)
    (fun l bl bs ->
      f l bs
    )

inline_for_extraction
noextract
let with_whole_buffer_hide_weak_modifies'
  (#t: Type)
  (b: B.buffer U8.t)
  (h0: HS.mem)
  (lin: Ghost.erased B.loc { B.loc_disjoint (Ghost.reveal lin) (B.loc_buffer b) })
  (lout: Ghost.erased B.loc { B.loc_disjoint (Ghost.reveal lout) (B.loc_buffer b) })
  (modifies_b: Ghost.erased bool)
  (post: (res: t) -> (cont: Seq.lseq Secret.uint8 (B.length b)) -> (h: HS.mem) -> GTot Type0)
  (f: (
    (l: Ghost.erased B.loc) ->
    (bs: B.buffer Secret.uint8 { B.length bs == B.length b }) ->
    HST.Stack t
    (requires (fun h ->
      B.modifies l h0 h /\
      B.loc_disjoint (Ghost.reveal lin `B.loc_union` Ghost.reveal lout) (Ghost.reveal l `B.loc_union` B.loc_buffer bs) /\
      B.live h bs /\
      B.as_seq h bs == Seq.seq_hide #Secret.U8 (B.as_seq h0 b)
    ))
    (ensures (fun h res h' ->
      B.modifies (Ghost.reveal lout `B.loc_union` (if Ghost.reveal modifies_b then B.loc_buffer bs else B.loc_none)) h h' /\
      post res (B.as_seq h' bs) h'
    ))
  ))
: HST.Stack t
  (requires (fun h ->
    B.live h b /\
    h0 == h
  ))
  (ensures (fun h res h' ->
    B.modifies (Ghost.reveal lout `B.loc_union` (if Ghost.reveal modifies_b then B.loc_buffer b else B.loc_none)) h h' /\
    post res (Seq.seq_hide (B.as_seq h' b)) h'
  ))
= let h0 = HST.get () in
  with_whole_buffer_hide_weak_modifies
    b
    h0
    lin
    lout
    modifies_b
    (fun res cont h -> post res (Seq.seq_hide #Secret.U8 cont) h)
    (fun l bs ->
      f l bs
    )

module E = FStar.Endianness

inline_for_extraction noextract
val load32_be
  (b:B.buffer Secret.uint8{B.length b == 4}):
  HST.Stack Secret.uint32
    (requires (fun h -> B.live h b))
    (ensures  (fun h0 z h1 -> h0 == h1 /\ B.live h1 b /\
                           E.be_to_n (Seq.seq_reveal (B.as_seq h1 b)) == Secret.v z))

inline_for_extraction noextract
val load32_le
  (b:B.buffer Secret.uint8 {B.length b == 4}):
  HST.Stack Secret.uint32
    (requires (fun h -> B.live h b))
    (ensures  (fun h0 z h1 -> h0 == h1 /\ B.live h1 b /\
                           E.le_to_n (Seq.seq_reveal (B.as_seq h1 b)) == Secret.v z))

inline_for_extraction noextract
val store32_be
  (b:B.buffer Secret.uint8 {B.length b == 4})
  (z:Secret.uint32)
: HST.Stack unit
    (requires (fun h -> B.live h b))
    (ensures  (fun h0 _ h1 -> B.(modifies (loc_buffer b) h0 h1) /\ B.live h1 b /\
                           E.be_to_n (Seq.seq_reveal (B.as_seq h1 b)) == Secret.v z))

inline_for_extraction noextract
val store32_le
  (b:B.buffer Secret.uint8 {B.length b == 4})
  (z:Secret.uint32)
: HST.Stack unit
    (requires (fun h -> B.live h b))
    (ensures  (fun h0 _ h1 -> B.(modifies (loc_buffer b) h0 h1) /\ B.live h1 b /\
                           E.le_to_n (Seq.seq_reveal (B.as_seq h1 b)) == Secret.v z))

(* Not secret-related, but very useful for footprints *)

inline_for_extraction
let buffer_update_strong
  (#t: Type0)
  (b: B.buffer t)
  (i: U32.t { U32.v i < B.length b })
  (v: t)
: HST.Stack unit
  (requires (fun h -> B.live h b))
  (ensures (fun h _ h' ->
    B.modifies (B.loc_buffer (B.gsub b i 1ul)) h h' /\
    B.as_seq h' b `Seq.equal` Seq.upd (B.as_seq h b) (U32.v i) v
  ))
= let b' = B.sub b i 1ul in
  let h = HST.get () in
  B.upd b' 0ul v;
  let h' = HST.get () in
  let f
    (j: nat { j < B.length b })
  : Lemma
    (Seq.index (B.as_seq h' b) j == Seq.index (Seq.upd (B.as_seq h b) (U32.v i) v) j)
  = let (b_, j_) =
      if j < U32.v i
      then B.gsub b 0ul i, j
      else if j = U32.v i
      then B.gsub b i 1ul, 0
      else B.gsub b (i `U32.add` 1ul) (B.len b `U32.sub` (i `U32.add` 1ul)), j - (U32.v i + 1)
    in
    assert (Seq.index (B.as_seq h b) j == Seq.index (B.as_seq h b_) j_);
    assert (Seq.index (B.as_seq h' b) j == Seq.index (B.as_seq h' b_) j_)
  in
  Classical.forall_intro f
