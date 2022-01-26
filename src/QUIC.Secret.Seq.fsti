module QUIC.Secret.Seq
include FStar.Seq

module Secret = QUIC.Secret.Int
module U8 = FStar.UInt8
module Ghost = FStar.Ghost

noextract
val seq_hide
  (#t: Secret.inttype { Secret.unsigned t })
  (x: seq (Secret.uint_t t Secret.PUB))
: Tot (seq (Secret.uint_t t Secret.SEC))

val seq_hide_length
  (#t: Secret.inttype { Secret.unsigned t })
  (x: seq (Secret.uint_t t Secret.PUB))
: Lemma
  (length (seq_hide x) == length x)
  [SMTPat (length (seq_hide x))]

val seq_hide_index
  (#t: Secret.inttype { Secret.unsigned t })
  (x: seq (Secret.uint_t t Secret.PUB))
  (i: nat)
: Lemma
  (requires (i < length x))
  (ensures (
    Secret.v (index (seq_hide x) i) == Secret.v (index x i)
  ))

let seq_hide_index'
  (#t: Secret.inttype { Secret.unsigned t })
  (x: seq (Secret.uint_t t Secret.PUB))
  (i: nat)
: Lemma
  (requires (i < length x))
  (ensures (
    index (seq_hide x) i == Secret.hide #t (index x i)
  ))
  [SMTPat (index (seq_hide x) i)]
= seq_hide_index x i

val seq_reveal
  (#t: Secret.inttype { Secret.unsigned t })
  (#sec: Secret.secrecy_level)
  (x: seq (Secret.uint_t t sec))
: GTot (seq (Secret.uint_t t Secret.PUB))

val seq_reveal_length
  (#t: Secret.inttype { Secret.unsigned t })
  (#sec: Secret.secrecy_level)
  (x: seq (Secret.uint_t t sec))
: Lemma
  (length (seq_reveal x) == length x)
  [SMTPat (length (seq_reveal x))]

val seq_reveal_index
  (#t: Secret.inttype { Secret.unsigned t })
  (#sec: Secret.secrecy_level)
  (x: seq (Secret.uint_t t sec))
  (i: nat)
: Lemma
  (requires (i < length x))
  (ensures (
    Secret.v (index (seq_reveal x) i) == Secret.v (index x i)
  ))

let seq_reveal_index'
  (#t: Secret.inttype { Secret.unsigned t })
  (#sec: Secret.secrecy_level)
  (x: seq (Secret.uint_t t sec))
  (i: nat)
: Lemma
  (requires (i < length x))
  (ensures (
    index (seq_reveal x) i == Secret.reveal (index x i)
  ))
  [SMTPat (index (seq_reveal x) i)]
= seq_reveal_index x i

let seq_reveal_pub
  (#t: Secret.inttype { Secret.unsigned t })
  (x: seq (Secret.uint_t t Secret.PUB))
: Lemma
  (seq_reveal x `equal` x)
= ()

let seq_reveal_hide
  (#t: Secret.inttype { Secret.unsigned t })
  (x: seq (Secret.uint_t t Secret.PUB))
: Lemma
  (seq_reveal (seq_hide x) `equal` x)
  [SMTPat (seq_reveal (seq_hide x))]
= ()

let seq_hide_reveal
  (#t: Secret.inttype { Secret.unsigned t })
  (x: seq (Secret.uint_t t Secret.SEC))
: Lemma
  (seq_hide (seq_reveal x) `equal` x)
  [SMTPat (seq_hide (seq_reveal x))]
= ()

let seq_reveal_inj
  (#t: Secret.inttype { Secret.unsigned t })
  (#sec: Secret.secrecy_level)
  (x1 x2: seq (Secret.uint_t t sec))
: Lemma
  (requires (seq_reveal x1 `equal` seq_reveal x2))
  (ensures (x1 `equal` x2))
= match sec with
  | Secret.PUB -> seq_reveal_pub #t x1; seq_reveal_pub #t x2
  | Secret.SEC -> seq_hide_reveal #t x1; seq_hide_reveal #t x2

let seq_hide_inj
  (#t: Secret.inttype { Secret.unsigned t })
  (x1 x2: seq (Secret.uint_t t Secret.PUB))
: Lemma
  (requires (seq_hide x1 `equal` seq_hide x2))
  (ensures (x1 `equal` x2))
= seq_reveal_hide #t x1; seq_reveal_hide #t x2

(* Properties *)

let slice_seq_hide
  (#t: Secret.inttype { Secret.unsigned t })
  (x: seq (Secret.uint_t t Secret.PUB))
  (from: nat)
  (to: nat { from <= to /\ to <= length x })
: Lemma
  (slice (seq_hide x) from to == seq_hide (slice x from to))
  [SMTPat (slice (seq_hide x) from to)]
= assert (slice (seq_hide x) from to `equal` seq_hide (slice x from to))

let reveal_seq_slice
  (#t: Secret.inttype { Secret.unsigned t })
  (#sec: Secret.secrecy_level)
  (x: seq (Secret.uint_t t sec))
  (from: nat)
  (to: nat { from <= to /\ to <= length x })
: Lemma
  (slice (seq_reveal x) from to == seq_reveal (slice x from to))
  [SMTPat (slice (seq_reveal x) from to)]
= assert (slice (seq_reveal x) from to `equal` seq_reveal (slice x from to))

let cons_seq_hide
  (#t: Secret.inttype { Secret.unsigned t })
  (a: Secret.uint_t t Secret.PUB)
  (x: seq (Secret.uint_t t Secret.PUB))
: Lemma
  (cons (Secret.hide a) (seq_hide x) == seq_hide (cons a x))
= assert (cons (Secret.hide a) (seq_hide x) `equal` seq_hide (cons a x))

let cons_seq_reveal
  (#t: Secret.inttype { Secret.unsigned t })
  (#sec: Secret.secrecy_level)
  (a: Secret.uint_t t sec)
  (x: seq (Secret.uint_t t sec))
: Lemma
  (cons (Secret.reveal a) (seq_reveal x) == seq_reveal (cons a x))
= assert (cons (Secret.reveal a) (seq_reveal x) `equal` seq_reveal (cons a x))
