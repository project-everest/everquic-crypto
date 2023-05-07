module Model.QUIC

module HS = FStar.HyperStack
module I = Model.Indexing
module U8 = FStar.UInt8
module U32 = FStar.UInt32
module U64 = FStar.UInt64
module U128 = FStar.UInt128
module M = LowStar.Modifies

friend QUIC.TotSpec

module Spec = QUIC.Spec
module TSpec = QUIC.TotSpec
module QH = QUIC.Spec.Header
module AE = Model.AEAD
module SAE = Spec.Agile.AEAD
module PNE = Model.PNE
module SPNE = Spec.Agile.Cipher
module BF = LowParse.BitFields
module U62 = QUIC.UInt62
module Secret = QUIC.Secret.Int
module B = LowStar.Buffer

open FStar.HyperStack.ST
open FStar.UInt32
open Mem

let pne_plain (j:PNE.id) (l:pnl) : eqtype = Spec.lbytes l & PNE.length_bits l
let as_bytes (j:PNE.id) (l:pnl) (x:pne_plain j l) : GTot (Helpers.lbytes l & PNE.length_bits l) = let (n,b) = x in (Helpers.hide n, b)
let repr (j:PNE.unsafe_id) (l:pnl) (x:pne_plain j l) : b:(Helpers.lbytes l & PNE.length_bits l){b == as_bytes j l x} =
  let (n,b)=x in (Helpers.hide n, b)
let mk (j:PNE.id) (l:pnl) (n:Helpers.lbytes l) (b:PNE.length_bits l) : p:pne_plain j l{as_bytes j l p == (n,b)} = Helpers.reveal n,b

let extend (#l:pnl) (b:Spec.lbytes l) (l':pnl)
  : Spec.lbytes l' =
  if l' <= l then Seq.slice b 0 l'
  else Seq.append (Seq.create (l'-l) 0z) b

let pnenc (j:PNE.id) (l:pnl) (p:pne_plain j l) (c:PNE.pne_cipherpad)
  : (l':pnl & pne_plain j l') =
  let npn, bits = p in
  let pnm, bm = c in
  QUIC.UInt.lemma_logxor_lt #8 bits bm 5;
  let v = BF.get_bitfield #8 (bits `FStar.UInt.logxor` bm) 0 5 in
  BF.set_bitfield_bound bits 5 0 5 v;
  let bits' : PNE.bits = BF.set_bitfield bits 0 5 v in
  let ln : pnl = BF.get_bitfield bits' 0 2 + 1 in
  let npn' : Spec.lbytes ln = extend #l npn ln in    
  let npn'' = QUIC.Spec.Lemmas.xor_inplace npn' (Seq.slice (Helpers.reveal pnm) 0 ln) 0 in
  (| ln, (npn', bits') |)

let lemma_xor (j:PNE.id) (l:pnl) (p:(Spec.lbytes l & PNE.length_bits l)) (c:PNE.pne_cipherpad)
  : Lemma (requires True)
  (ensures (let (| l', b' |) = pnenc j l p c in
    let _, bits = as_bytes j l' b' in
    let l:pnl = LowParse.BitFields.get_bitfield bits 0 2 + 1 in
    l == (l' <: pnl)))
  = ()

// The (abstract) type of encrypted QUIC headers,
let pne_pkg =
  PNE.PNEPlainPkg pne_plain as_bytes repr mk pnenc lemma_xor

type _ctr (offset:pn) = p:pn{p >= offset}

noeq type stream_writer' (i:id) = 
| Writer:
  info: info ->
  offset: pn ->
  siv: Spec.lbytes 12 ->
  ae: AE.aead_writer (dfst i){(AEAD.wgetinfo ae).AEAD.min_len == 3} ->
  pne_info: PNE.info (dsnd i){
    pne_info.PNE.calg == Spec.Agile.AEAD.cipher_alg_of_supported_alg (AEAD.wgetinfo ae).AEAD.alg /\
    pne_info.PNE.halg == (AEAD.wgetinfo ae).AEAD.halg /\
    pne_info.PNE.plain == pne_pkg} ->
  pne: PNE.pne_state pne_info ->
  ctr: reference (_ctr offset) ->
  stream_writer' i

let stream_writer = stream_writer'

type _last (offset:pn) = p:nat{p >= offset /\ p < max_ctr}

noeq type stream_reader' (#i:id) (w:stream_writer i) = 
| Reader:
  aer: AE.aead_reader (w.ae) ->
  last: reference (_last w.offset) ->
  stream_reader' w

let stream_reader = stream_reader'

let writer_info #k w = w.info
let reader_info #k #w r = w.info

let writer_ae_info #k w = AEAD.wgetinfo w.ae
let reader_ae_info #k #w r = AEAD.rgetinfo r.aer
let writer_pne_info #k w = w.pne_info
let reader_pne_info #k #w r = w.pne_info

let writer_aead_state #k w = w.ae
let reader_aead_state #k #w r = r.aer

let writer_pne_state #k w = w.pne
let reader_pne_state #k #w r = w.pne

let nonce_of_ctr #i (w:stream_writer i) (n:nat{n < pow2 62 /\ n>=w.offset})
  : Tot AEAD.nonce
  =
  let _ = assert_norm(pow2 62 < pow2 (8 `op_Multiply` 12)) in
  let pn = FStar.Endianness.n_to_be 12 n in
  QUIC.Spec.Lemmas.xor_inplace pn w.siv 0

let nonce_of_ctr_injective
  #i (w:stream_writer i)
  (n1:nat{n1 < pow2 62 /\ n1>=w.offset})
  (n2:nat{n2 < pow2 62 /\ n2>=w.offset})
: Lemma
  (requires (nonce_of_ctr w n1 == nonce_of_ctr w n2))
  (ensures (n1 == n2))
=
  let _ = assert_norm(pow2 62 < pow2 (8 `op_Multiply` 12)) in
  let pn1 = FStar.Endianness.n_to_be 12 n1 in
  let pn2 = FStar.Endianness.n_to_be 12 n2 in
  QUIC.Spec.Lemmas.xor_inplace_involutive pn1 w.siv 0;
  QUIC.Spec.Lemmas.xor_inplace_involutive pn2 w.siv 0

let nonce_of_ctr_injective'
  #i (w:stream_writer i)
  (n1:nat{n1 < pow2 62 /\ n1>=w.offset})
  (n2:nat{n2 < pow2 62 /\ n2>=w.offset})
: Lemma
  (n1 <> n2 ==> nonce_of_ctr w n1 <> nonce_of_ctr w n2)
=
  Classical.move_requires (nonce_of_ctr_injective w n1) n2

let fresh_nonces_from
  (j: nat)
  (#k:id)
  (w:stream_writer k)
  (h:mem)
: GTot Type0
=
  (forall i. (i > j /\ safe k) ==>
    AEAD.fresh_nonce w.ae (nonce_of_ctr w i) h)

let fresh_nonces
  (#k:id)
  (w:stream_writer k)
  (h:mem)
: GTot Type0
= fresh_nonces_from (HS.sel h w.ctr) w h

let invariant #k w h =
  AEAD.winvariant w.ae h /\
  PNE.invariant w.pne h /\
  h `HS.contains` w.ctr /\
  fresh_nonces w h /\
  AEAD.wfootprint w.ae `B.loc_disjoint` (B.loc_mreference w.ctr) /\
  PNE.footprint w.pne `B.loc_disjoint` (B.loc_mreference w.ctr) /\
  PNE.footprint w.pne `B.loc_disjoint` AEAD.wfootprint w.ae

let rinvariant #k #w r h = invariant w h /\
  h `HS.contains` r.last /\
  AEAD.wfootprint w.ae `B.loc_disjoint` (B.loc_mreference w.ctr)

let writer_offset #k w = w.offset
let reader_offset #k #w r = w.offset

let wctrT #k w h = HS.sel h w.ctr
let wctr #k w = !w.ctr

let writer_static_iv #k w = w.siv
let reader_static_iv #k #w r = w.siv

let expected_pnT #k #w r h = HS.sel h r.last
let expected_pn #k #w r = !r.last

let footprint #k w = (AEAD.wfootprint w.ae)
  `B.loc_union` (PNE.footprint w.pne)
  `B.loc_union` B.loc_mreference w.ctr

let rfootprint #k #w r = footprint w `B.loc_union` B.loc_mreference r.last

let frame_invariant #k w h0 l h1 =
  AEAD.wframe_invariant l w.ae h0 h1;
  PNE.frame_invariant w.pne l h0 h1;
  if safe k then AEAD.frame_log l w.ae h0 h1

let rframe_invariant #k #w r h0 l h1 =
  AEAD.wframe_invariant l w.ae h0 h1;
  PNE.frame_invariant w.pne l h0 h1

let wframe_log #k w t h0 l h1 =
  AEAD.frame_log l w.ae h0 h1
  
let rframe_log #k #w r t h0 l h1 =
  AEAD.frame_log l w.ae h0 h1

let wframe_pnlog #k w t h0 l h1 =
  PNE.frame_table w.pne l h0 h1

let rframe_pnlog #k #w r t h0 l h1 =
  PNE.frame_table w.pne l h0 h1

(* HACK, the interleaving of `val coerce` into this file fails to verify
without increasing the rlimit, but increasing it in the fsti wouldn't
take effect here (see FStar issue #2854 and the others linked from
there. So, increase rlimit here and pop it after `let coerce`, so we are
sure to catch it. *)
#push-options "--z3rlimit 40"

let create k u u1 u2 init =
  let open Model.Helpers in
  let alg = u1.AEAD.alg in
  let siv = random 12 in
  (**) let h0 = get() in
  let ae = AEAD.gen (dfst k) u1 in
  (**) let h1 = get () in  
  let pne = PNE.create (dsnd k) u2 in
  (**) let h2 = get () in
  let ctr = ralloc u.region init in
  (**) let h3 = get () in 
  (**) AEAD.wframe_invariant M.loc_none ae h1 h3;
  (**) PNE.frame_invariant pne M.loc_none h2 h3;
  if safe k then
   begin
    (**) AEAD.frame_log M.loc_none ae h1 h3;
    (**) PNE.frame_table pne M.loc_none h2 h3
   end;
  Writer u init (reveal siv) ae u2 pne ctr

let coerce k u u1 u2 init ts =
  let open Model.Helpers in
  let alg = u1.AEAD.alg in
  let siv : Model.Helpers.lbytes 12 = Spec.derive_secret u1.AEAD.halg ts Spec.label_iv 12 in
  let h0 = get() in
  let u1 : AEAD.info (dfst k) = u1 in
  let ae = AEAD.quic_coerce u1 ts in
  let h1 = get () in
  let pne = PNE.quic_coerce (dsnd k) u2 ts in
  let h2 = get () in
  let ctr = ralloc u.region init in
  let h3 = get () in 
  AEAD.wframe_invariant M.loc_none ae h1 h3;
  PNE.frame_invariant pne M.loc_none h2 h3;
  Writer u init (reveal siv) ae u2 pne ctr

#push-options "--z3rlimit 400 --query_stats"

let createReader rgn #k w =
  let h0 = get () in
  let last = ralloc rgn (writer_offset w) in
  let h1 = get () in
  frame_invariant w h0 M.loc_none h1;
  let aer = AEAD.gen_reader w.ae in
  Reader aer last

(* Another HACK: set_pn gets interleaved here *)

#pop-options
#pop-options

#push-options "--z3rlimit 256 --fuel 0"
private let lemma_eq_add (a b c:nat) : Lemma (requires a == b - c)
  (ensures a + c == b) = ()

let set_pne (h:Spec.header) (#ln:pnl) (pne:PNE.pne_cipher ln) (c1:Spec.bytes)
  : Pure Spec.packet
  (requires not (Spec.is_retry h) /\ ln == Lib.RawIntTypes.uint_to_nat (TSpec.pn_length h) /\
  Seq.length c1 < pow2 32 - Spec.header_len_bound)
  (ensures fun r -> True)
  =
  let pne, bits = pne in
  let r = TSpec.format_header h in
  let pno = TSpec.pn_offset h in
  assert(pno == Seq.length r - ln);
  assert (Seq.length r <= Spec.header_len_bound);
  assert (ln == Seq.length pne);
  let protected_bits = if Spec.MShort? h then 5 else 4 in
  let f' = BF.set_bitfield (U8.v (Seq.index r 0)) 0 protected_bits (BF.get_bitfield (U8.v (Seq.index r 0) `FStar.UInt.logxor` bits) 0 protected_bits) in
  let r' = Seq.cons (U8.uint_to_t f') (Seq.slice r 1 pno `Seq.append` Helpers.reveal pne `Seq.append` c1) in
  assert (Seq.length r' == Seq.length r + Seq.length c1);
  r'

#pop-options

#restart-solver
#push-options "--z3rlimit 64 --fuel 0"
let encrypt #k w h #l p =
  let open Model.Helpers in
  let alg = (writer_ae_info w).AEAD.alg in
  let h0 = get () in
  let ln = Lib.RawIntTypes.uint_to_nat (TSpec.pn_length h) in
  let iv = TSpec.iv_for_encrypt_decrypt alg (hide w.siv) h in
  let iv0 = Helpers.reveal #12 iv in
  assert (iv0 == nonce_of_ctr w (wctrT w h0 + 1));
  let aad = TSpec.format_header h in
  let f = Seq.index aad 0 in
  let bits' = BF.get_bitfield (UInt8.v f) 0 5 in  
  QUIC.Spec.Header.Parse.format_header_pn_length h;
  BF.get_bitfield_get_bitfield (UInt8.v f) 0 5 0 2;
  // SMT needs some help
  lemma_eq_add (BF.get_bitfield bits' 0 2) ln 1;
  let bits : PNE.length_bits ln = bits' in
  let pno = TSpec.pn_offset h in
  let rpn : Helpers.lbytes ln = Helpers.hide (Seq.slice aad pno (pno+ln)) in
  assert(AEAD.is_safe (dfst k) ==> AEAD.fresh_nonce w.ae iv0 h0);
  let c1 = AEAD.encrypt (dfst k) w.ae iv0 (Helpers.hide aad) l p in
  let h1 = get () in
  PNE.frame_invariant w.pne (AEAD.wfootprint w.ae) h0 h1;
  if safe k then begin
    Classical.forall_intro (AEAD.fresh_nonce_snoc w.ae h0 h1 iv0 (Helpers.hide aad) l p c1);
    Classical.forall_intro (nonce_of_ctr_injective' w (wctrT w h0 + 1))
  end;
  assert (fresh_nonces_from (wctrT w h0 + 1) w h1);
  let sample : PNE.sample = Helpers.reveal #16 (Seq.slice c1 (4-ln) (20-ln)) in
  let npn = mk (dsnd k) ln rpn bits in
  // N.B. see paper for justification of this assumption
  assume(PNE.is_safe (dsnd k) ==> PNE.fresh_sample sample w.pne h1);
  let pnc : PNE.pne_cipher ln = PNE.encrypt w.pne #ln npn sample in
  let pne, bits = pnc in
  let h2 = get () in
  AEAD.wframe_invariant (PNE.footprint w.pne) w.ae h1 h2;
  if safe k then AEAD.frame_log (PNE.footprint w.pne) w.ae h1 h2;
  assert (fresh_nonces_from (wctrT w h0 + 1) w h2);
  w.ctr := !w.ctr + 1;
  let h3 = get() in
  AEAD.wframe_invariant (M.loc_mreference w.ctr) w.ae h2 h3;
  PNE.frame_invariant w.pne (M.loc_mreference w.ctr) h2 h3;
  if safe k then AEAD.frame_log (M.loc_mreference w.ctr) w.ae h2 h3;
  assert (fresh_nonces w h3);
  assert(invariant w h3);
  if safe k then
    set_pne h pnc (Helpers.reveal #(Seq.length c1) c1)
  else
    let k1, k2 = writer_leak w in
    let plain = (writer_ae_info w).AEAD.plain_pkg.AEAD.repr (dfst k) l p in
    TSpec.encrypt alg (hide k1) (hide w.siv) (hide k2) h (reveal #l plain)

/// Decrypt follows in a similar fashion. A complete proof will be provided for the final version.

let decrypt #_ #_ _ _ _ = admit ()

#pop-options
