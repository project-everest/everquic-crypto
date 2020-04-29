module QUIC.Secret.Seq
include FStar.Seq

module Secret = QUIC.Secret.Int
module U8 = FStar.UInt8
module Ghost = FStar.Ghost

noextract
val seq_hide
  (#t: Secret.inttype { Secret.unsigned t })
  (#sec: Secret.secrecy_level)
  (x: seq (Secret.uint_t t sec))
: Tot (seq (Secret.uint_t t Secret.SEC))

val seq_hide_length
  (#t: Secret.inttype { Secret.unsigned t })
  (#sec: Secret.secrecy_level)
  (x: seq (Secret.uint_t t sec))
: Lemma
  (length (seq_hide x) == length x)
  [SMTPat (length (seq_hide x))]

val seq_hide_index
  (#t: Secret.inttype { Secret.unsigned t })
  (#sec: Secret.secrecy_level)
  (x: seq (Secret.uint_t t sec))
  (i: nat)
: Lemma
  (requires (i < length x))
  (ensures (
    Secret.v (index (seq_hide x) i) == Secret.v (index x i)
  ))
  [SMTPat (index (seq_hide x) i)]

let seq_hide_sec
  (#t: Secret.inttype { Secret.unsigned t })
  (x: seq (Secret.uint_t t Secret.SEC))
: Lemma
  (seq_hide x `equal` x)
= ()

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
  [SMTPat (index (seq_reveal x) i)]

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
= ()

let seq_hide_reveal
  (#t: Secret.inttype { Secret.unsigned t })
  (x: seq (Secret.uint_t t Secret.SEC))
: Lemma
  (seq_hide (seq_reveal x) `equal` x)
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
  (#sec: Secret.secrecy_level)
  (x1 x2: seq (Secret.uint_t t sec))
: Lemma
  (requires (seq_hide x1 `equal` seq_hide x2))
  (ensures (x1 `equal` x2))
= match sec with
  | Secret.SEC -> seq_hide_sec #t x1; seq_hide_sec #t x2
  | Secret.PUB -> seq_reveal_hide #t x1; seq_reveal_hide #t x2
