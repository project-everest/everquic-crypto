module Model.PNE

open FStar.HyperStack
open FStar.Seq
open FStar.Monotonic.Seq

open FStar.Bytes
open FStar.UInt32
open Mem

module M = LowStar.Modifies
module HS = FStar.HyperStack
module I = Model.Indexing
module U32 = FStar.UInt32
module U128 = FStar.UInt128

type id = I.pne_id
let is_safe (i:id) = I.is_pne_honest i && I.ideal_PRF
type safeid = i:id{is_safe i}
type unsafeid = i:id{not (is_safe i)}

let samplelen = 16
type sample = lbytes samplelen
type pne_plainlen = l:nat {l >= 2 /\ l <= 5}
type pne_cipher (l:pne_plainlen) = lbytes l
type pne_cipherpad = lbytes 5

val clip_cipherpad : (cp:pne_cipherpad) -> (l:pne_plainlen) -> pne_cipher l

noeq type pne_plain_pkg =
  | PNEPlainPkg:
    pne_plain: (j:id -> l:pne_plainlen -> (t:Type0{hasEq t})) ->
    as_bytes: (j:id -> l:pne_plainlen -> pne_plain j l -> GTot (lbytes l)) ->
    repr: (j:unsafeid -> l:pne_plainlen -> n:pne_plain j l -> Tot (b:lbytes l{b == as_bytes j l n})) ->
    pne_plain_pkg

let info = pne_plain_pkg

let pne_plain (u:info) (j:id) (l:pne_plainlen) =
  PNEPlainPkg?.pne_plain u j l

type entry (j:id) (u:info) =
  | Entry :
    s:sample ->
    #l:pne_plainlen ->
    n:pne_plain u j l ->
    c:pne_cipher l ->
    entry j u

val pne_state : (j:id) -> (u:info) -> Type0

val table : (#j:id) -> (#u:info) -> (st:pne_state j u) -> (h:mem) -> GTot (Seq.seq (entry j u))

val footprint : #j:id -> #u:info -> st:pne_state j u -> M.loc

val frame_table: #j:safeid -> #u:info -> st:pne_state j u -> l:Seq.seq (entry j u) ->
  h0:mem -> r:M.loc -> h1:mem ->
  Lemma
    (requires
      table st h0 == l /\
      M.modifies r h0 h1 /\
      r `M.loc_disjoint` (footprint st))
    (ensures table st h1 == l)

let sample_filter (j:id) (u:info) (s:sample) (e:entry j u) : bool =
  Entry?.s e = s

let entry_for_sample (#j:id) (#u:info) (s:sample) (st:pne_state j u) (h:mem) :
  GTot (option (entry j u)) =
  Seq.find_l (sample_filter j u s) (table st h)
  
let fresh_sample (#j:id) (#u:info) (s:sample) (st:pne_state j u) (h:mem) :
  GTot bool =
  None? (entry_for_sample s st h)

let find_sample (#j:id) (#u:info) (s:sample) (st:pne_state j u) (h:mem) :
  GTot bool =
  Some? (entry_for_sample s st h)

let sample_cipher_filter (j:id) (u:info) (s:sample) (#l:pne_plainlen) (c:pne_cipher l) (e:entry j u) : bool =
  Entry?.s e = s && Entry?.l e = l && Entry?.c e = c

let entry_for_sample_cipher (#j:id) (#u:info) (s:sample) (#l:pne_plainlen) (c:pne_cipher l) (st:pne_state j u) (h:mem) :
  GTot (option (entry j u)) =
  Seq.find_l (sample_cipher_filter j u s #l c) (table st h)
  
let find_sample_cipher (#j:id) (#u:info) (s:sample) (#l:pne_plainlen) (c:pne_cipher l) (st:pne_state j u) (h:mem) :
  GTot bool =
  Some? (entry_for_sample_cipher s #l c st h)

let sample_cipherpad_filter (j:id) (u:info) (s:sample) (cp:pne_cipherpad) (e:entry j u) : bool =
  Entry?.s e = s && clip_cipherpad cp (Entry?.l e) = Entry?.c e

let entry_for_sample_cipherpad (#j:id) (#u:info) (s:sample) (cp:pne_cipherpad) (st:pne_state j u) (h:mem) :
  GTot (option (entry j u)) =
  Seq.find_l (sample_cipherpad_filter j u s cp) (table st h)
  
let find_sample_cipherpad (#j:id) (#u:info) (s:sample) (cp:pne_cipherpad) (st:pne_state j u) (h:mem) :
  GTot bool =
  Some? (entry_for_sample_cipher s cp st h)

val create (j:id) (u:info) : ST (pne_state j u)
  (requires fun _ -> True)
  (ensures fun h0 st h1 ->
    modifies_none h0 h1 /\
    table st h1 == Seq.empty)

val encrypt :
  (#j:id) ->
  (#u:info) ->
  (st:pne_state j u) ->
  (#l:pne_plainlen) ->
  (n:pne_plain u j l) ->
  (s:sample) ->
  ST (pne_cipher l)
  (requires fun h0 ->
    fresh_sample s st h0)
  (ensures fun h0 c h1 ->
    M.modifies (footprint st) h0 h1 /\
    (is_safe j ==>
      table st h1 == Seq.snoc (table st h0) (Entry s #l n c)))

#reset-options "--z3rlimit 50"

val decrypt :
  (#j:id) ->
  (#u:info) ->
  (st:pne_state j u) ->
  (cp:pne_cipherpad) ->
  (s:sample) ->
  ST (l:pne_plainlen & pne_plain u j l)
  (requires fun h0 -> True)
  (ensures fun h0 (|l, n|) h1 ->
    modifies_none h0 h1 /\
    ((is_safe j /\ find_sample s st h0) ==>
     (match entry_for_sample s st h0 with
        | Some (Entry _ #l' n' c') ->
        (l = l' /\ n = n') <==>
        (l = l' /\ c' = clip_cipherpad cp l))
    )
  ) 
