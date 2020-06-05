module Model.QUIC

module HS = FStar.HyperStack
module I = Model.Indexing
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

type _ctr (offset:pn) = p:pn{p >= offset}

let pne_plain (j:PNE.id) (l:pnl) : eqtype = Spec.lbytes l & PNE.length_bits l
let as_bytes (j:PNE.id) (l:pnl) (x:pne_plain j l) : GTot (Helpers.lbytes l & PNE.length_bits l) = let (n,b) = x in (Helpers.hide n, b)
let repr (j:PNE.unsafe_id) (l:pnl) (x:pne_plain j l) : b:(Helpers.lbytes l & PNE.length_bits l){b == as_bytes j l x} =
  let (n,b)=x in (Helpers.hide n, b)
let mk (j:PNE.id) (l:pnl) (n:Helpers.lbytes l) (b:PNE.length_bits l) : p:pne_plain j l{as_bytes j l p == (n,b)} = Helpers.reveal n,b

let pnenc (j:PNE.id) (l:pnl) (p:pne_plain j l) (c:PNE.pne_cipherpad)
  : (l':pnl & pne_plain j l') =
  let npn, bits = p in
  let pnm, bm = c in
  let npn' = QUIC.Spec.Lemmas.xor_inplace npn (Seq.slice (Helpers.reveal pnm) 0 l) in
  let bits' = BF.set_bitfield bits 0 5 (BF.get_bitfield (bits `FStar.UInt.logxor` bm) 0 5) in
  let ln = BF.get_bitfield bits' 0 2 + 1 in
  (| ln, (npn', bits') |)
  
  admit()

(*
    let protected_bits = if MShort? h then 5 else 4 in
    let f' = BF.set_bitfield (U8.v f) 0 protected_bits (BF.get_bitfield (U8.v f `FStar.UInt.logxor` U8.v (Seq.index mask 0)) 0 protected_bits) in

    let r = Seq.cons (U8.uint_to_t f') (Seq.slice r 1 (Seq.length r)) in

  admit()
*)

let lemma_xor (j:PNE.id) (l:pnl) (p:(Spec.lbytes l & PNE.length_bits l)) (c:PNE.pne_cipherpad)
  : Lemma (requires True)
  (ensures (let (| l', b' |) = pnenc j l p c in
    let _, bits = as_bytes j l' b' in
    let l:pnl = LowParse.BitFields.get_bitfield bits 0 2 + 1 in
    l == (l' <: pnl)))
  = admit()

let pne_pkg : PNE.pne_plain_pkg =
 PNE.PNEPlainPkg pne_plain as_bytes repr mk pnenc lemma_xor

noeq type stream_writer' (i:id) = 
| Writer:
  info: info ->
  offset: pn ->
  siv: Spec.lbytes 12 ->
  ae: AE.aead_writer (dfst i){(AEAD.wgetinfo ae).AEAD.min_len == 3} ->
  pne_info: PNE.info (dsnd i){
    pne_info.PNE.calg == Spec.Agile.AEAD.cipher_alg_of_supported_alg (AEAD.wgetinfo ae).AEAD.alg /\
    pne_info.PNE.halg == (AEAD.wgetinfo ae).AEAD.halg} ->
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

let invariant #k w h =
  AEAD.winvariant w.ae h /\
  PNE.invariant w.pne h /\
  h `HS.contains` w.ctr /\
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
  PNE.frame_invariant w.pne l h0 h1

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

let create k u u1 u2 init =
  let open Model.Helpers in
  let alg = u1.AEAD.alg in
  let siv = random 12 in
  let h0 = get() in
  let ae = AEAD.gen (dfst k) u1 in
  let h1 = get () in  
  let pne = PNE.create (dsnd k) u2 in
  let h2 = get () in
  let ctr = ralloc u.region init in
  let h3 = get () in 
  AEAD.wframe_invariant M.loc_none ae h1 h3;
  PNE.frame_invariant pne M.loc_none h2 h3;
  if safe k then
   begin
    AEAD.frame_log M.loc_none ae h1 h3;
    PNE.frame_table pne M.loc_none h2 h3
   end;
  let r = Writer u init (reveal siv) ae u2 pne ctr in
  r

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
  let r = Writer u init (reveal siv) ae u2 pne ctr in
  r

let createReader rgn #k w =
  let h0 = get () in
  let last = ralloc rgn (writer_offset w) in
  let h1 = get () in
  frame_invariant w h0 M.loc_none h1;
  let aer = AEAD.gen_reader w.ae in
  Reader aer last

#push-options "--z3rlimit 30"
let encrypt #k w h #l p =
  let open Model.Helpers in
  let alg = (writer_ae_info w).AEAD.alg in
  if safe k then
    let h0 = get () in
    let ln = Lib.RawIntTypes.uint_to_nat (TSpec.pn_length h) - 1 in
    let iv = TSpec.iv_for_encrypt_decrypt alg (hide w.siv) h in
    let iv = Helpers.reveal #12 iv in
    let aad = Helpers.hide (TSpec.format_header h) in
    let pno = TSpec.pn_offset h in
    assume(AEAD.fresh_nonce w.ae iv h0);
    let c1 = AEAD.encrypt (dfst k) w.ae iv aad l p in
    let h1 = get () in
    PNE.frame_invariant w.pne (AEAD.wfootprint w.ae) h0 h1;
    let sample = (Seq.slice c1 (3-ln) (19-ln)) in
//    let npn = mk (dsnd k) (ln+1) (Helpers.reveal #(ln+1) (Seq.slice aad pno (pno+ln+1))) ln in
    admit()
//    PNE.encrypt w.pne
  else admit()

(*
    let k1, k2 = writer_leak w in
    let plain : Spec.pbytes' (Spec.is_retry h) = (writer_ae_info w).AEAD.plain_pkg.AEAD.repr (dfst k) l p in
    let r = TSpec.encrypt alg
    (hide k1) (hide w.siv) (hide k2) h plain in
    let h0 = get () in
    w.ctr := !w.ctr + 1;
    let h1 = get () in
    AEAD.wframe_invariant (M.loc_mreference w.ctr) w.ae h0 h1;
    PNE.frame_invariant w.pne (M.loc_mreference w.ctr) h0 h1;
    r
#pop-options
*)
let decrypt #k #w r cid_len packet =
  if safe k then
    admit()
  else
    let open Model.Helpers in
    let k1, k2 = reader_leak r in
    let expected = expected_pn r in
    let ea = (writer_ae_info w).AE.alg in
    match QUIC.TotSpec.decrypt ea (hide k1)
      (hide (reader_static_iv r)) (hide k2)
      expected cid_len packet with
    | Spec.Failure -> M_Failure
    | _ -> admit()
 
