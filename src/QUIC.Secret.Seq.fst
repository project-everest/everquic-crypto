module QUIC.Secret.Seq
open FStar.Seq

module Secret = QUIC.Secret.Int
module U8 = FStar.UInt8
module Ghost = FStar.Ghost

(* NOTE: abstraction is NOT broken here *)

noextract
let rec seq_map
  (#t1 #t2: Type)
  (f: (t1 -> Tot t2))
  (x: seq t1)
: Tot (lseq t2 (length x))
  (decreases (length x))
= if length x = 0
  then empty
  else cons (f (head x)) (seq_map f (tail x))

let rec seq_map_index
  (#t1 #t2: Type)
  (f: (t1 -> Tot t2))
  (x: seq t1)
  (i: nat { i < length x })
: Lemma
  (ensures (index (seq_map f x) i == f (index x i)))
  (decreases (length x))
  [SMTPat (index (seq_map f x) i)]
= if i = 0
  then ()
  else seq_map_index f (tail x) (i - 1)

let seq_hide
  #t #sec x
= seq_map (Secret.cast t Secret.SEC) x

let seq_hide_length
  #t #sec x
= ()

#push-options "--z3rlimit 16"

let seq_hide_index
  #t #seq x i
= ()

#pop-options

noextract
let rec seq_gmap
  (#t1 #t2: Type)
  (f: (t1 -> GTot t2))
  (x: seq t1)
: GTot (lseq t2 (length x))
  (decreases (length x))
= if length x = 0
  then empty
  else cons (f (head x)) (seq_gmap f (tail x))

let rec seq_gmap_index
  (#t1 #t2: Type)
  (f: (t1 -> GTot t2))
  (x: seq t1)
  (i: nat { i < length x })
: Lemma
  (ensures (index (seq_gmap f x) i == f (index x i)))
  (decreases (length x))
  [SMTPat (index (seq_gmap f x) i)]
= if i = 0
  then ()
  else seq_gmap_index f (tail x) (i - 1)

let uint_reveal
  (t: Secret.inttype { Secret.unsigned t })
  (sec_from sec_to: Secret.secrecy_level)
  (x: Secret.uint_t t sec_from)
: GTot (Secret.uint_t t sec_to)
= Secret.mk_int (Secret.v x)

let seq_reveal
  #t #sec x
= seq_gmap (uint_reveal t sec Secret.PUB) x

let seq_reveal_length
  #t #sec x
= ()

let seq_reveal_index
  #t #sec x i
= ()
