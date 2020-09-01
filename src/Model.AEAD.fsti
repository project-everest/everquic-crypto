module Model.AEAD

module HS = FStar.HyperStack
module I = Model.Indexing
module U32 = FStar.UInt32
module U128 = FStar.UInt128
module B = LowStar.Buffer
module Spec = Spec.Agile.AEAD

#set-options "--fuel 0 --ifuel 0"

open Mem

/// Abbreviations for idealization
/// ------------------------------

// In this module, id is an AEAD id.
let id = I.ae_id

// ea = encryption alg
let alg = I.ea

let is_safe i =
  I.ideal_AEAD && I.is_ae_honest i

let safe_id =
  i:id{is_safe i}

let unsafe_id =
  i:id{~ (is_safe i)}

/// Some redefinitions, using Spec
/// ------------------------------

// Trying to follow the conventions: _len for machine lengths,
// _length for spec (nat) lengths.
let tag_len: x:U32.t { forall (a: alg). {:pattern Spec.tag_length a} U32.v x == Spec.tag_length a } =
  16ul

// This duplicates a fair amount of definitions from Spec.Agile.AEAD, but here
// the bounds are tighter and force plain texts to not overflow 32 bits once
// encrypted and tagged.
//
// Introducing a minimum length allows making sure that there are enough bytes
// to sample out of the ciphertext, as the tag can be too small for that purpose
// for some AEAD ciphersuites.
type plain_length = l:nat{l + U32.v tag_len < pow2 32}
type plain_length_at_least (lmin: plain_length) = l:plain_length{lmin <= l}

/// Packages, info (?)
/// ------------------

noeq
type plain_pkg (min_len:plain_length) (idt: eqtype) (safe: idt -> bool) =
  | PlainPkg:
    plain: (i:idt -> plain_length_at_least min_len -> eqtype) ->
    as_bytes: (i:idt -> l:plain_length_at_least min_len -> plain i l -> GTot (Spec.lbytes l)) ->
    repr: (i:idt{not (safe i)} -> l:plain_length_at_least min_len -> p:plain i l -> Tot (b:Spec.lbytes l{b == as_bytes i l p})) ->
    mk: (i:idt{not (safe i)} -> l:plain_length_at_least min_len -> p:Spec.lbytes l -> p':plain i l { as_bytes i l p' == p }) ->
    plain_pkg min_len idt safe

noeq type info' = {
  alg: alg;
  halg: I.ha;
  min_len: plain_length;
  plain_pkg: plain_pkg min_len id is_safe;
}

let info (i:id) =
  info:info'{
    I.ae_id_ginfo i == info.alg /\
    I.ae_id_ghash i == info.halg
  }

/// Accessors for info
/// ------------------

// Accessor for the info type.
let at_least (#i:id) (u:info i) =
  plain_length_at_least u.min_len

let plain (#i:id) (u:info i) (l: at_least u) =
  u.plain_pkg.plain i l

let plain_as_bytes (#i:id) (#u:info i) (#l:at_least u) (p:plain u l) : GTot (Spec.lbytes l) =
  u.plain_pkg.as_bytes i l p

let plain_repr (#i: unsafe_id) (#u:info i) (#l:at_least u) (p:plain u l) : Tot (r:Spec.lbytes l{r == plain_as_bytes p}) =
  u.plain_pkg.repr i l p

/// Plains, ciphers and entries in the log
/// --------------------------------------

let cipher (#i:id) (u:info i) (l:at_least u) =
  Spec.lbytes (l + UInt32.v tag_len)

let ad #i (u: info i) =
  Spec.ad u.alg

let nonce : eqtype = b:Seq.seq UInt8.t{Seq.length b == 12}

noeq
type entry (i:id) (u:info i) =
  | Entry:
    n: nonce ->
    ad: ad u ->
    #l: at_least u ->
    p: plain u l ->
    c: cipher u l ->
    entry i u

/// Readers & writers
/// -----------------

val aead_writer: i:id -> Type u#1
val aead_reader: #i:id -> w:aead_writer i -> Type u#1

val wgetinfo: #i:id -> aead_writer i -> Tot (info i)
val rgetinfo: #i:id -> #w:aead_writer i -> aead_reader w -> Tot (u:info i{u == wgetinfo w})

val wlog: #i:safe_id -> w:aead_writer i -> mem -> GTot (Seq.seq (entry i (wgetinfo w)))
let rlog (#i:safe_id) (#w: aead_writer i) (r:aead_reader w) (h:mem) = wlog w h

val wkey: #i:unsafe_id -> w:aead_writer i -> Tot (Spec.kv (wgetinfo w).alg)

val wfootprint: #i:id -> aead_writer i -> GTot B.loc

val winvariant : #i:id -> aead_writer i -> mem -> Type0
//let rinvariant (#i:I.id) (#w:aead_writer i) (r:aead_reader w) (h:mem) =
//  winvariant w h

val wframe_invariant: #i:id -> l:B.loc -> w:aead_writer i -> h0:mem -> h1:mem ->
  Lemma
    (requires (
      winvariant w h0 /\
      B.modifies l h0 h1 /\
      B.loc_disjoint l (wfootprint w)))
    (ensures
      winvariant w h1)

val frame_log: #i:safe_id -> l:B.loc -> w:aead_writer i -> h0:mem -> h1:mem ->
  Lemma
    (requires
      winvariant w h0 /\
      B.modifies l h0 h1 /\
      B.loc_disjoint l (wfootprint w))
    (ensures wlog w h1 == wlog w h0)

/// Derivation (QUIC-specific)

let lemma_max_hash_len ha
  : Lemma (Spec.Hash.Definitions.hash_length ha <= 64 /\
  Spec.Hash.Definitions.max_input_length ha >=  pow2 61 - 1 /\
  pow2 61 - 1 > 64)
  [SMTPat (Spec.Hash.Definitions.hash_length ha)]
  =
  assert_norm (pow2 61 < pow2 125);
  assert_norm (pow2 61 - 1 > 64);
  assert_norm (pow2 64 > pow2 61);
  assert_norm (pow2 128 > pow2 64)

let traffic_secret ha =
  Spec.lbytes (Spec.Hash.Definitions.hash_length ha)

/// Main stateful API
/// -----------------

(** Allocating a writer **)
val gen (i:id) (u:info i) : ST (aead_writer i)
  (requires (fun h -> True))
  (ensures (fun h0 w h1 ->
    winvariant w h1 /\

    B.modifies B.loc_none h0 h1 /\
    B.fresh_loc (wfootprint w) h0 h1 /\
    B.(loc_includes (loc_ae_region ()) (wfootprint w)) /\

    wgetinfo w == u /\
    (I.ideal_AEAD && I.is_ae_honest i ==> wlog w h1 == Seq.empty)))

(** Building a reader from a writer **)
val gen_reader (#i: id) (w: aead_writer i) : ST (aead_reader w)
  (requires (fun h -> winvariant w h))
  (ensures (fun h0 r h1 -> h0 == h1))

val coerce (#i:unsafe_id) (u:info i)
  (kv:Spec.kv u.alg)
  : ST (aead_writer i)
  (requires fun h0 -> True)
  (ensures fun h0 w h1 ->
    winvariant w h1 /\
    B.modifies B.loc_none h0 h1 /\
    B.fresh_loc (wfootprint w) h0 h1 /\
    B.(loc_includes (loc_ae_region ()) (wfootprint w)) /\
    wgetinfo w == u /\
    wkey w == kv
  )

val quic_coerce (#i:unsafe_id) (u:info i)
  (ts:traffic_secret u.halg)
  : ST (aead_writer i)
  (requires fun h0 -> True)
  (ensures fun h0 w h1 ->
    winvariant w h1 /\
    B.modifies B.loc_none h0 h1 /\
    B.fresh_loc (wfootprint w) h0 h1 /\
    B.(loc_includes (loc_ae_region ()) (wfootprint w)) /\
    wgetinfo w == u /\
    wkey w ==
      QUIC.Spec.derive_secret u.halg ts
        QUIC.Spec.label_key (Spec.key_length u.alg)
  )

let nonce_filter (#i:id) (w:aead_writer i) (n:nonce) (e:entry i (wgetinfo w)) : bool =
  Entry?.n e = n

let wentry_for_nonce (#i:safe_id) (w:aead_writer i) (n:nonce) (h:mem)
  : GTot (option (entry i (wgetinfo w))) =
  Seq.find_l (nonce_filter #i w n) (wlog w h)

let fresh_nonce (#i:safe_id) (w:aead_writer i) (n:nonce) (h:mem)
  : GTot bool =
  None? (wentry_for_nonce w n h)

let fresh_nonce_snoc
  (#i:safe_id) (w:aead_writer i) (h h' :mem)
  (n1: nonce)
  (aad: ad (wgetinfo w))
  (l: at_least (wgetinfo w))
  (p: plain (wgetinfo w) l)
  (c: cipher (wgetinfo w) l)
  (n:nonce)
: Lemma
  ((fresh_nonce w n h /\ n1 <> n /\ wlog w h' == Seq.snoc (wlog w h) (Entry n1 aad p c)) ==> fresh_nonce w n h')
= Seq.find_snoc (wlog w h) (Entry n1 aad p c) (nonce_filter #i w n)

val encrypt
  (i: id)
  (w: aead_writer i)
  (n: nonce)
  (aad: ad (wgetinfo w))
  (l: at_least (wgetinfo w))
  (p: plain (wgetinfo w) l)
  : Stack (cipher (wgetinfo w) l)
  (requires (fun h0 ->
    winvariant w h0 /\
    (is_safe i ==> fresh_nonce w n h0)))
  (ensures (fun h0 c h1 ->
    B.modifies (wfootprint w) h0 h1 /\
    winvariant w h1 /\
    (is_safe i ==>
      wlog w h1 == Seq.snoc (wlog w h0) (Entry n aad p c)) /\
    (~ (is_safe i) ==> (
      let a: Spec.supported_alg = I.ae_id_ginfo i in
      let k: Spec.kv a = wkey w in
      let iv : Spec.iv a = Model.Helpers.hide n in
      let p = (wgetinfo w).plain_pkg.as_bytes i l p in
      c == Spec.encrypt #(I.ae_id_ginfo i) k iv aad p))))

val decrypt
  (i: id)
  (#w: aead_writer i)
  (r: aead_reader w)
  (aad: ad (wgetinfo w))
  (n: nonce)
  (l:at_least (wgetinfo w))
  (c:cipher (wgetinfo w) l)
  : Stack (option (plain (rgetinfo r) l))
  (requires (fun h0 ->
    winvariant w h0))
  (ensures fun h0 res h1 ->
    winvariant w h1 /\
    B.modifies B.loc_none h0 h1 /\
    (is_safe i ==>
      // feels like we should state something more interesting, e.g. if we
      // take all the entries in the log that match this nonce, then there is
      // exactly one
      (match wentry_for_nonce w n h0 with
      | None -> None? res
      | Some (Entry n' aad' #l' p' c') ->
        // We know that n == n' here, owing to the definition of wentry_for_nonce.
        let matches = aad' == aad /\ c' == c /\ l == l' in
        (matches ==> res = Some p') /\
        (~matches ==> res = None)
      )
    ) /\
    (~ (is_safe i) ==> (
      let a: Spec.supported_alg = I.ae_id_ginfo i in
      let k: Spec.kv a = wkey w in
      let iv : Spec.iv a = Helpers.hide n in
      let maybe_plain = Spec.decrypt k iv aad c in
      match maybe_plain with
      | None -> None? res
      | Some p ->
          Some? res /\ (
          let p' = (wgetinfo w).plain_pkg.as_bytes i l (Some?.v res) in
          p == p')
    ))
  )
