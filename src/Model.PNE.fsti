module Model.PNE

module B = LowStar.Buffer
module HS = FStar.HyperStack
module I = Model.Indexing
module U32 = FStar.UInt32
module U128 = FStar.UInt128
module Spec = Spec.Agile.Cipher

#set-options "--fuel 0 --ifuel 0"

open FStar.HyperStack
open Mem
open Model.Helpers

/// Abbreviations for idealization
/// ------------------------------

type id = I.pne_id
type alg = I.ca

let is_safe (i:id) =
  I.is_pne_honest i && I.ideal_PRF

type safe_id =
  i:id{is_safe i}

type unsafe_id =
  i:id{not (is_safe i)}

/// QUIC payload sampling
/// --------------------

let sample_length = 16
let sample = lbytes sample_length
let pne_plain_length = l:nat {l >= 2 /\ l <= 5}
let pne_cipher (l:pne_plain_length) = lbytes l
let pne_cipherpad = lbytes 5

/// Restrict a generated cipherpad to the length of the encoded packet number.
val clip_cipherpad : (cp:pne_cipherpad) -> (l:pne_plain_length) -> pne_cipher l

// We have to locally redefine the plain package since the one in AEAD has a
// notion of minimum length, and a maximum length related to Spec.Agile.AEAD. We
// could conceivably share definitions via some added type parameters or
// refinements.
noeq type pne_plain_pkg =
  | PNEPlainPkg:
    pne_plain: (j:id -> l:pne_plain_length -> (t:Type0{hasEq t})) ->
    as_bytes: (j:id -> l:pne_plain_length -> pne_plain j l -> GTot (lbytes l)) ->
    repr: (j:unsafe_id -> l:pne_plain_length -> n:pne_plain j l -> Tot (b:lbytes l{b == as_bytes j l n})) ->
    pne_plain_pkg

// JP: not sure why we don't have the same mechanism as for Model.AEAD with the index for `info`
noeq type info' = {
  calg: alg;
  plain: pne_plain_pkg;
}

let info (j:id) =
  info:info'{I.pne_id_ginfo j == info.calg}

let pne_plain (#j:id) (u:info j) (l:pne_plain_length) =
  PNEPlainPkg?.pne_plain u.plain j l

noeq
type entry (#j:id) (u:info j) =
  | Entry :
    s:sample ->
    #l:pne_plain_length ->
    n:pne_plain u l ->
    c:pne_cipher l ->
    entry u

val pne_state : (#j:id) -> (u:info j) -> Type0

val table : (#j:id) -> (#u:info j) -> (st:pne_state u) -> (h:mem) -> GTot (Seq.seq (entry u))

val footprint : #j:id -> #u:info j -> st:pne_state u -> B.loc

val invariant: #j:id -> #u:info j -> st:pne_state u -> mem -> Type0

val frame_invariant: #j:id -> #u:info j -> st:pne_state u -> l:B.loc -> h0:mem -> h1:mem -> Lemma
  (requires (
    invariant st h0 /\
    B.modifies l h0 h1 /\
    B.loc_disjoint l (footprint st)))
  (ensures (
    invariant st h1))

val frame_table: #j:safe_id -> #u:info j -> st:pne_state u ->
  r:B.loc -> h0:mem -> h1:mem ->
  Lemma
    (requires
      B.modifies r h0 h1 /\
      r `B.loc_disjoint` (footprint st))
    (ensures table st h1 == table st h0)

let sample_filter (#j:id) (u:info j) (s:sample) (e:entry u) : bool =
  Entry?.s e `lbytes_eq` s

let entry_for_sample (#j:id) (#u:info j) (s:sample) (st:pne_state u) (h:mem) :
  GTot (option (entry u)) =
  Seq.find_l (sample_filter u s) (table st h)

let fresh_sample (#j:id) (#u:info j) (s:sample) (st:pne_state u) (h:mem) :
  GTot bool =
  None? (entry_for_sample s st h)

let find_sample (#j:id) (#u:info j) (s:sample) (st:pne_state u) (h:mem) :
  GTot bool =
  Some? (entry_for_sample s st h)

let sample_cipher_filter (j:id) (u:info j) (s:sample) (#l:pne_plain_length) (c:pne_cipher l) (e:entry u) : bool =
  Entry?.s e `lbytes_eq` s && Entry?.l e = l && Entry?.c e `lbytes_eq` c

let entry_for_sample_cipher (#j:id) (#u:info j) (s:sample) (#l:pne_plain_length) (c:pne_cipher l) (st:pne_state u) (h:mem) :
  GTot (option (entry u)) =
  Seq.find_l (sample_cipher_filter j u s #l c) (table st h)

let find_sample_cipher (#j:id) (#u:info j) (s:sample) (#l:pne_plain_length) (c:pne_cipher l) (st:pne_state u) (h:mem) :
  GTot bool =
  Some? (entry_for_sample_cipher s #l c st h)

let sample_cipherpad_filter (#j:id) (#u:info j) (s:sample) (cp:pne_cipherpad) (e:entry u) : bool =
  Entry?.s e `lbytes_eq` s && clip_cipherpad cp (Entry?.l e) `lbytes_eq` Entry?.c e

let entry_for_sample_cipherpad (#j:id) (#u:info j) (s:sample) (cp:pne_cipherpad) (st:pne_state u) (h:mem) :
  GTot (option (entry u)) =
  Seq.find_l (sample_cipherpad_filter s cp) (table st h)

let find_sample_cipherpad (#j:id) (#u:info j) (s:sample) (cp:pne_cipherpad) (st:pne_state u) (h:mem) :
  GTot bool =
  Some? (entry_for_sample_cipher s cp st h)

val create (j:id) (u:info j) : ST (pne_state u)
  (requires fun _ -> True)
  (ensures fun h0 st h1 ->
    invariant st h1 /\
    B.modifies B.loc_none h0 h1 /\
    B.fresh_loc (footprint st) h0 h1 /\
    B.(loc_includes (loc_pne_region ()) (footprint st)) /\

    (I.ideal_PRF && I.is_pne_honest j ==> table st h1 == Seq.empty))

val encrypt :
  (#j:id) ->
  (#u:info j) ->
  (st:pne_state u) ->
  (#l:pne_plain_length) ->
  (n:pne_plain u l) ->
  (s:sample) ->
  ST (pne_cipher l)
  (requires fun h0 ->
    fresh_sample s st h0)
  (ensures fun h0 c h1 ->
    B.modifies (footprint st) h0 h1 /\
    (is_safe j ==>
      table st h1 == Seq.snoc (table st h0) (Entry s #l n c)) /\
    True
// FIXME(adl) need to merge Tahina's branch with QUIC.Spec.Header.Public
//    (~(is_safe j) ==>
//      c == Spec.header_encrypt encrypt )
  )

val decrypt :
  (#j:id) ->
  (#u:info j) ->
  (st:pne_state u) ->
  (cp:pne_cipherpad) ->
  (s:sample) ->
  ST (l:pne_plain_length & pne_plain u l)
  (requires fun h0 -> True)
  (ensures fun h0 (|l, n|) h1 ->
    modifies_none h0 h1 /\
    ((is_safe j /\ find_sample s st h0) ==>
     (match entry_for_sample s st h0 with
        | Some (Entry _ #l' n' c') ->
        (l = l' /\ n = n') <==>
        (l = l' /\ c' `lbytes_eq` clip_cipherpad cp l))
    )
  )
