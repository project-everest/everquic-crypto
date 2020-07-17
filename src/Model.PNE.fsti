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
  I.is_pne_honest i && I.ideal_PNE

type safe_id =
  i:id{is_safe i}

type unsafe_id =
  i:id{not (is_safe i)}

/// QUIC payload sampling
/// --------------------

// For simplicity, we do not distinguish between long and short headers; caller
// of this module will just 0-left-pad the protected bits in the case of a long
// header.
let bits: Type0 = LowParse.BitFields.ubitfield 8 5

// Note: the sample is PUBLIC so is using QUIC.Spec.lbytes which do not operate over secret integers.
let sample_length = 16
let sample = QUIC.Spec.lbytes sample_length
let pne_plain_length = l:nat {l >= 1 /\ l <= 4}

let length_bits (l: pne_plain_length) =
  b:bits { LowParse.BitFields.get_bitfield b 0 2 + 1 == l }

let pne_cipher (l:pne_plain_length) = lbytes l & bits
let pne_cipherpad = lbytes 4 & bits

/// Restrict a generated cipherpad to the length of the encoded packet number.
val clip_cipherpad : (cp:pne_cipherpad) -> (l:pne_plain_length) -> pne_cipher l

// We define a separate package type here (different from the one in AEAD). We
// idealize them separately, and there's a specific part here that's about the
// protected bits of the header.
noeq type pne_plain_pkg =
  | PNEPlainPkg:
    pne_plain: (j:id -> l:pne_plain_length -> t:eqtype) ->
    as_bytes: (j:id -> l:pne_plain_length -> pne_plain j l -> GTot (lbytes l & length_bits l)) ->
    repr: (j:unsafe_id -> l:pne_plain_length -> n:pne_plain j l ->
      Tot (b:(lbytes l & length_bits l) {b == as_bytes j l n})) ->
    mk: (j:id -> l:pne_plain_length -> n:lbytes l -> b:length_bits l -> p:pne_plain j l { as_bytes j l p == (n, b) }) ->
    xor: (j:id -> l:pne_plain_length -> p:pne_plain j l -> cp:pne_cipherpad ->
      (l': pne_plain_length & pne_plain j l')) ->
    lemma_xor: (j:id -> l:pne_plain_length -> p:pne_plain j l -> cp:pne_cipherpad -> Lemma
        (requires True)
        (ensures (
          let (| l', p' |) = xor j l p cp in
          let _, bits = as_bytes j l' p' in
          let l: pne_plain_length = LowParse.BitFields.get_bitfield bits 0 2 + 1 in
          let l': pne_plain_length = l' in
          l == l'
        ))) ->
    pne_plain_pkg

noeq type info' = {
  calg: alg;
  halg: I.ha;
  plain: pne_plain_pkg;
}

let info (j:id) =
  info:info'{
    I.pne_id_ginfo j == info.calg /\
    I.pne_id_ghash j == info.halg
  }

let pne_plain (#j:id) (u:info j) (l:pne_plain_length) =
  PNEPlainPkg?.pne_plain u.plain j l

noeq
type entry (#j:id) (u:info j) =
  | Entry :
    s:sample ->
    #l:pne_plain_length ->
    n:pne_plain u l ->
    // We do not perform truncation at encryption-time, but rather at decryption-time
    c:pne_cipherpad ->
    entry u

val pne_state : (#j:id) -> (u:info j) -> Type u#1

val table : (#j:safe_id) -> (#u:info j) -> (st:pne_state u) -> (h:mem) -> GTot (Seq.seq (entry u))

// Header protection key
let key_len (#j:id) (u:info j) = Spec.Agile.Cipher.key_length u.calg
val key: #j:unsafe_id -> #u:info j -> st:pne_state u -> lbytes (key_len u)

val footprint : #j:id -> #u:info j -> st:pne_state u -> GTot B.loc

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
      invariant st h0 /\
      B.modifies r h0 h1 /\
      r `B.loc_disjoint` (footprint st))
    (ensures table st h1 == table st h0)

// Equality for the pair of (pne, protected_bits) we manipulate in this module.
let pne_bits_eq #l (x y: pne_cipher l) =
  fst x `lbytes_eq` fst y && snd x = snd y

// Finding the entry for a given sample.
let sample_filter (#j:id) (u:info j) (s:sample) (e:entry u) : bool =
  Entry?.s e = s

let entry_for_sample (#j:safe_id) (#u:info j) (s:sample) (st:pne_state u) (h:mem) :
  GTot (option (entry u)) =
  Seq.find_l (sample_filter u s) (table st h)

/// XXX unused
let contains_sample (#j:safe_id) (#u:info j) (s:sample) (st:pne_state u) (h:mem) :
  GTot bool =
  Some? (entry_for_sample s st h)

let fresh_sample (#j:safe_id) (#u:info j) (s:sample) (st:pne_state u) (h:mem) :
  GTot bool =
  None? (entry_for_sample s st h)


/// Stateful API
/// ------------

val create (j:id) (u:info j) : ST (pne_state u)
  (requires fun _ -> True)
  (ensures fun h0 st h1 ->
    invariant st h1 /\
    B.modifies B.loc_none h0 h1 /\
    B.fresh_loc (footprint st) h0 h1 /\
    B.(loc_includes (loc_pne_region ()) (footprint st)) /\

    (is_safe j ==> table st h1 == Seq.empty))

let lemma_max_hash_len ha
  : Lemma (Spec.Hash.Definitions.hash_length ha <= 64 /\
  Spec.Hash.Definitions.max_input_length ha >=  pow2 61 - 1 /\
  pow2 61 - 1 > 64)
  [SMTPat (Spec.Hash.Definitions.hash_length ha)]
  =
  assert_norm (pow2 61 < pow2 125);
  assert_norm (pow2 61 - 1 > 64)

let traffic_secret ha =
  lbytes (Spec.Hash.Definitions.hash_length ha)

val coerce (j:unsafe_id) (u:info j)
  (k:lbytes (key_len u))
  : ST (pne_state #j u)
  (requires fun _ -> True)
  (ensures fun h0 st h1 ->
    invariant st h1 /\
    B.modifies B.loc_none h0 h1 /\
    B.fresh_loc (footprint st) h0 h1 /\
    B.(loc_includes (loc_pne_region ()) (footprint st)) /\
    key st == k)

val quic_coerce (j:unsafe_id) (u:info j)
  (ts:traffic_secret u.halg)
  : ST (pne_state #j u)
  (requires fun _ -> True)
  (ensures fun h0 st h1 ->
    invariant st h1 /\
    B.modifies B.loc_none h0 h1 /\
    B.fresh_loc (footprint st) h0 h1 /\
    B.(loc_includes (loc_pne_region ()) (footprint st)) /\
    key st ==
      QUIC.Spec.derive_secret u.halg ts
        QUIC.Spec.label_hp (key_len u))

private let lemma_logxor_lt (#n:pos) (a b:UInt.uint_t n) (k:nat{k <= n})
  : Lemma (requires a < pow2 k /\ b < pow2 k)
  (ensures a `UInt.logxor` b < pow2 k)
  = admit()

let encrypt_spec (a: Spec.cipher_alg)
  (l: pne_plain_length)
  (pn: lbytes l)
  (b: length_bits l)
  (s: sample)
  (k: Spec.key a):
  pne_cipher l
=
  let open QUIC.Spec.Lemmas in
  // We need the packet number length in order to know where to find the mask in the cipher block.
  let mask = Model.Helpers.reveal #16 (QUIC.TotSpec.block_of_sample a k (Model.Helpers.hide s)) in
  let pnmask = and_inplace (Seq.slice mask 1 (l + 1)) (QUIC.Spec.Header.pn_sizemask (l - 1)) 0 in
  // Classify, because HACL* specs require secret integers.
  let pnmask = Seq.init (Seq.length pnmask) (fun i -> Lib.IntTypes.u8 (UInt8.v (Seq.index pnmask i))) in
  assert (Seq.length pnmask == l);
  // We now have enough to build the encrypted pn. Note that because our
  // input is a sliced packet number, we don't mask at an offset like
  // header_encrypt does.
  let encrypted_pn = pointwise_op (Lib.IntTypes.(logxor #U8 #SEC)) pn pnmask 0 in
  // Now on to bit protection. Since we receive as input only the protected
  // bits, there is a proof obligation for a caller, to show that get_bf
  // (header.[0] `xor` mask.[0]) == get_bf header.[0] `xor` get_bf mask.[0]
  let mask_bits: bits = LowParse.BitFields.get_bitfield (UInt8.v (Seq.index mask 0)) 0 5 in
  let protected_bits = mask_bits `FStar.UInt.logxor` b in
  lemma_logxor_lt #8 mask_bits b 5;
  encrypted_pn, protected_bits

val encrypt :
  (#j:id) ->
  (#u:info j) ->
  (st:pne_state u) ->
  (#l:pne_plain_length) ->
  (n:pne_plain u l) ->
  // For confidentiality modeling, this function takes as inputs only the public
  // parts of the header.
  (s:sample) ->
  ST (pne_cipher l)
  (requires fun h0 ->
    invariant st h0 /\
    // cannot talk about freshness because it requires talking about the
    // table which is only available for safe id's
    (is_safe j ==> fresh_sample s st h0))
  (ensures fun h0 c h1 ->
    invariant st h1 /\
    B.modifies (footprint st) h0 h1 /\ (
    if is_safe j then
      exists (c': pne_cipherpad).
      table st h1 == Seq.snoc (table st h0) (Entry s #l n c') /\
      clip_cipherpad c' l == c
    else
      // Our input is: plain packet number, plain bits to be protected
      let pn, bits = PNEPlainPkg?.as_bytes u.plain j l n in
      let k = key st in
      // We output an encrypted packet number and protected bits
      c == encrypt_spec u.calg l pn bits s k))

let decrypt_spec
  (#j:unsafe_id)
  (#u:info j)
  (a: Spec.cipher_alg)
  (padded_cipher: lbytes 4)
  (b: bits)
  (k: Spec.key a)
  (s: sample):
  (l:pne_plain_length & pne_plain u l)
=
  // This mimics the specification of header_decrypt_aux starting after:
  // let sample = ...
  let mask = Model.Helpers.reveal #16 (QUIC.TotSpec.block_of_sample a k (Model.Helpers.hide s)) in
  // Decrypting protected bits
  let mask_bits: bits = LowParse.BitFields.get_bitfield (UInt8.v (Seq.index mask 0)) 0 5 in
  lemma_logxor_lt #8 mask_bits b 5;
  let b = mask_bits `FStar.UInt.logxor` b in
  // Moving on to the pn length which is part of the protected bits
  let pn_len = LowParse.BitFields.get_bitfield b 0 2 in
  assert (0 <= pn_len /\ pn_len <= 3);
  let pnmask = QUIC.Spec.Lemmas.and_inplace (Seq.slice mask 1 (pn_len + 2)) (QUIC.Spec.Header.pn_sizemask pn_len) 0 in
  assert (let l = Seq.length pnmask in 1 <= l /\ l <= 4);
  // Classify, because HACL* specs require secret integers.
  let pnmask = Seq.init (Seq.length pnmask) (fun i -> Lib.IntTypes.u8 (UInt8.v (Seq.index pnmask i))) in
  let cipher = Seq.slice padded_cipher 0 (pn_len + 1) in
  assert (Seq.length cipher == Seq.length pnmask /\ Seq.length cipher == pn_len + 1);
  let pn = QUIC.Spec.Lemmas.pointwise_op (Lib.IntTypes.(logxor #U8 #SEC)) cipher pnmask 0 in
  (| pn_len + 1, PNEPlainPkg?.mk u.plain j (pn_len + 1) pn b |)

let xor_cipherpad (cp1 cp2: pne_cipherpad): pne_cipherpad =
  let c1, b1 = cp1 in
  let c2, b2 = cp2 in
  let x1 = LowParse.BitFields.get_bitfield b1 0 5 in
  let x2 = LowParse.BitFields.get_bitfield b2 0 5 in
  lemma_logxor_lt #8 x1 x2 5;
  let v = x1 `UInt.logxor` x2 in
  LowParse.BitFields.set_bitfield_bound #8 0 5 0 5 v;
  Seq.init 4 (fun i -> Seq.index c1 i `Lib.IntTypes.(logxor #U8 #SEC)` Seq.index c2 i),
  LowParse.BitFields.set_bitfield #8 0 0 5 v
  
val decrypt:
  (#j:id) ->
  (#u:info j) ->
  (st:pne_state u) ->
  (cp:pne_cipherpad) ->
  (s:sample) ->
  ST (l:pne_plain_length & pne_plain u l)
  (requires fun h0 ->
    invariant st h0)
  (ensures fun h0 r h1 ->
    invariant st h1 /\
    B.modifies (footprint st) h0 h1 /\ (
    if is_safe j then
      let entry = entry_for_sample s st h1 in
      Some? entry /\ (
      let Some (Entry _ #l' n' c') = entry in
      r == PNEPlainPkg?.xor u.plain j l' n' (c' `xor_cipherpad` cp)) /\
      (Some? (entry_for_sample s st h0) ==> modifies_none h0 h1)
    else
      let cipher, encrypted_bits = cp in
      r == decrypt_spec u.calg cipher encrypted_bits (key st) s)
  )
