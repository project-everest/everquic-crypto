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

// For simplicity, we do not distinguish between long and short headers; caller
// of this module will just 0-left-pad the protected bits in the case of a long
// header.
let protected_bits: Type0 = LowParse.BitFields.ubitfield 5 5

// Note: the sample is PUBLIC so is using QUIC.Spec.lbytes which do not operate over secret integers.
let sample_length = 16
let sample = QUIC.Spec.lbytes sample_length
let pne_plain_length = l:nat {l >= 1 /\ l <= 4}
let pne_cipher (l:pne_plain_length) = lbytes l & protected_bits
let pne_cipherpad = lbytes 5 & protected_bits

/// Restrict a generated cipherpad to the length of the encoded packet number.
val clip_cipherpad : (cp:pne_cipherpad) -> (l:pne_plain_length) -> pne_cipher l

// We define a separate package type here (different from the one in AEAD). We
// idealize them separately, and there's a specific part here that's about the
// protected bits of the header.
//
// JP: why is pne_plain_pkg not parameterized over an id type and safe predicate?
noeq type pne_plain_pkg =
  | PNEPlainPkg:
    pne_plain: (j:id -> l:pne_plain_length -> t:eqtype) ->
    as_bytes: (j:id -> l:pne_plain_length -> pne_plain j l -> GTot (lbytes l & protected_bits)) ->
    repr: (j:unsafe_id -> l:pne_plain_length -> n:pne_plain j l ->
      Tot (b:(lbytes l & protected_bits) {b == as_bytes j l n})) ->
    mk: (j:unsafe_id -> l:pne_plain_length -> n:lbytes l -> b:protected_bits -> p:pne_plain j l { as_bytes j l p == (n, b) }) ->
    pne_plain_pkg

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

// Header protection key
val key: #j:unsafe_id -> #u:info j -> st:pne_state u -> h:mem -> GTot (lbytes (Spec.Agile.Cipher.key_length u.calg))

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

// Equality for the pair of (pne, protected_bits) we manipulate in this module.
let pne_bits_eq #l (x y: pne_cipher l) =
  fst x `lbytes_eq` fst y && snd x = snd y

// Finding the entry for a given sample.
let sample_filter (#j:id) (u:info j) (s:sample) (e:entry u) : bool =
  Entry?.s e = s

let entry_for_sample (#j:id) (#u:info j) (s:sample) (st:pne_state u) (h:mem) :
  GTot (option (entry u)) =
  Seq.find_l (sample_filter u s) (table st h)

/// XXX unused
let contains_sample (#j:id) (#u:info j) (s:sample) (st:pne_state u) (h:mem) :
  GTot bool =
  Some? (entry_for_sample s st h)

let fresh_sample (#j:id) (#u:info j) (s:sample) (st:pne_state u) (h:mem) :
  GTot bool =
  None? (entry_for_sample s st h)

// Finding the entry for a given cipher. Insofar as I understand, the table
// keeps a map from plain to cipher (i.e. cipher truncated to the right length,
// or "clipped"). XXX this seems to be unused.
let sample_cipher_filter (j:id) (u:info j) (s:sample) (#l:pne_plain_length) (c:pne_cipher l) (e:entry u) : bool =
  Entry?.s e = s && Entry?.l e = l && Entry?.c e `pne_bits_eq` c

let entry_for_sample_cipher (#j:id) (#u:info j) (s:sample) (#l:pne_plain_length) (c:pne_cipher l) (st:pne_state u) (h:mem) :
  GTot (option (entry u)) =
  Seq.find_l (sample_cipher_filter j u s #l c) (table st h)

let contains_sample_cipher (#j:id) (#u:info j) (s:sample) (#l:pne_plain_length) (c:pne_cipher l) (st:pne_state u) (h:mem) :
  GTot bool =
  Some? (entry_for_sample_cipher s #l c st h)

// However, for decryption, we are given a "cipherpad", which should probably be
// named "padded_cipher". Such a padded cipher may be too long, so what we do
// instead is define a successful table lookup is a match on i) the protected
// bits, ii) the sample and iii) the truncation of the cipher. XXX this seems to
// be unused as well.
let sample_cipherpad_filter (#j:id) (#u:info j) (s:sample) (cp:pne_cipherpad) (e:entry u) : bool =
  Entry?.s e = s && clip_cipherpad cp (Entry?.l e) `pne_bits_eq` Entry?.c e

let entry_for_sample_cipherpad (#j:id) (#u:info j) (s:sample) (cp:pne_cipherpad) (st:pne_state u) (h:mem) :
  GTot (option (entry u)) =
  Seq.find_l (sample_cipherpad_filter s cp) (table st h)

let contains_sample_cipherpad (#j:id) (#u:info j) (s:sample) (cp:pne_cipherpad) (st:pne_state u) (h:mem) :
  GTot bool =
  Some? (entry_for_sample_cipherpad s cp st h)

/// Stateful API
/// ------------

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
  // For confidentiality modeling, this function takes as inputs only the public
  // parts of the header.
  (s:sample) ->
  (pn_length: nat { 0 <= pn_length /\ pn_length <= 3 }) ->
  ST (pne_cipher l)
  (requires fun h0 ->
    l >= pn_length + 1 /\
    fresh_sample s st h0)
  (ensures fun h0 c h1 ->
    B.modifies (footprint st) h0 h1 /\ (
    if is_safe j then
      table st h1 == Seq.snoc (table st h0) (Entry s #l n c)
    else
      let open QUIC.Spec.Lemmas in
      // Our input is: plain packet number, plain bits to be protected
      let pn, bits = PNEPlainPkg?.as_bytes u.plain j l n in
      // We output an encrypted packet number and protected bits
      let return_pn, return_bits = c in
      // We need the packet number length in order to know where to find the mask in the cipher block.
      let mask = QUIC.Spec.block_of_sample u.calg (key st h0) s in
      let pnmask = and_inplace (Seq.slice mask 1 (pn_length + 2)) (QUIC.Spec.pn_sizemask_naive pn_length) 0 in
      // Classify, because HACL* specs require secret integers.
      let pnmask = Seq.init (Seq.length pnmask) (fun i -> Lib.IntTypes.u8 (UInt8.v (Seq.index pnmask i))) in
      // We now have enough to build the encrypted pn. Note that because our
      // input is a sliced packet number, we don't mask at an offset like
      // header_encrypt does.
      let encrypted_pn = pointwise_op (Lib.IntTypes.(logxor #U8 #SEC)) pn pnmask 0 in
      // Now on to bit protection. Since we receive as input only the protected
      // bits, there is a proof obligation for a caller, to show that get_bf
      // (header.[0] `xor` mask.[0]) == get_bf header.[0] `xor` get_bf mask.[0]
      let mask_bits: protected_bits = LowParse.BitFields.get_bitfield (UInt8.v (Seq.index mask 0)) 0 5 in
      let protected_bits = mask_bits `FStar.UInt.logxor` bits in
      return_pn == encrypted_pn /\ return_bits == protected_bits))

val decrypt :
  (#j:id) ->
  (#u:info j) ->
  (st:pne_state u) ->
  (cp:pne_cipherpad) ->
  (s:sample) ->
  ST (option(l:pne_plain_length & pne_plain u l))
  (requires fun h0 -> True)
  (ensures fun h0 r h1 ->
    modifies_none h0 h1 /\ (
    if is_safe j then
      match entry_for_sample s st h0 with
      | None -> None? r
      | Some (Entry _ #l' n' c') -> Some? r /\ (
          let Some (| l, n |) = r in
          (l = l' /\ n = n') <==>
          (l = l' /\ c' `pne_bits_eq` clip_cipherpad cp l))
    else
      let cipher, encrypted_bits = cp in
      // This mimics the specification of header_decrypt_aux starting after:
      // let sample = ...
      let mask = QUIC.Spec.block_of_sample u.calg (key st h0) s in
      // Decrypting protected bits
      let mask_bits: protected_bits = LowParse.BitFields.get_bitfield (UInt8.v (Seq.index mask 0)) 0 5 in
      let bits = mask_bits `FStar.UInt.logxor` encrypted_bits in
      // Moving on to the pn length which is part of the protected bits
      let pn_len = LowParse.BitFields.get_bitfield bits 0 2 in
      assert (0 <= pn_len /\ pn_len <= 3);
      let pnmask = QUIC.Spec.Lemmas.and_inplace (Seq.slice mask 1 (pn_len + 2)) (QUIC.Spec.pn_sizemask_naive pn_len) 0 in
      assert (let l = Seq.length pnmask in 1 <= l /\ l <= 4);
      // Classify, because HACL* specs require secret integers.
      let pnmask = Seq.init (Seq.length pnmask) (fun i -> Lib.IntTypes.u8 (UInt8.v (Seq.index pnmask i))) in
      let cipher = Seq.slice cipher 0 (pn_len + 1) in
      assert (Seq.length cipher == Seq.length pnmask /\ Seq.length cipher == pn_len + 1);
      let pn = QUIC.Spec.Lemmas.pointwise_op (Lib.IntTypes.(logxor #U8 #SEC)) cipher pnmask 0 in
      r == Some (| pn_len + 1, PNEPlainPkg?.mk u.plain j (pn_len + 1) pn bits |)
  ))
