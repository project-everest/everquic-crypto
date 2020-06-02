module Model.PNE

module B = LowStar.Buffer
module HS = FStar.HyperStack
module I = Model.Indexing
module U32 = FStar.UInt32
module U128 = FStar.UInt128
module Spec = Spec.Agile.Cipher

module ST = FStar.HyperStack.ST

#set-options "--fuel 0 --ifuel 0"

open FStar.HyperStack
open Mem
open Model.Helpers
open LowStar.BufferOps

let clip_cipherpad cp l =
  let cipher, bits = cp in
  Seq.slice cipher 0 l, bits

let log (#i: id) (u: info i): Type0 =
  Seq.seq (entry #i u)

let model_state j =
  u:info j & B.pointer (log #j u)

let unsafe_state j =
  // JP: I don't understand why we have to go through model.indexing here when
  // the algorithm is readily available in the info
  info j & Spec.key (I.pne_id_ginfo j)

// JP: why is this type parameterized over the info?
let pne_state #j u =
  if is_safe j then
    s:model_state j { dfst s == u }
  else
    s:unsafe_state j { fst s == u }

let table #j #u st h =
  let (| u, p |) = st <: model_state j in
  B.deref h p

let key #j #u st =
  snd (st <: unsafe_state j)

let footprint #i #u w =
  if is_safe i then
    B.loc_addr_of_buffer (dsnd (w <: model_state i))
  else
    B.loc_none

let invariant #i #u st h =
  if is_safe i then
    B.live h (dsnd (st <: model_state i))
  else
    True

let frame_invariant #_ #_ _ _ _ _ =
  ()

let frame_table #_ #_ _ _ _ _ =
  ()

let create j u =
  if is_safe j then
    let l: log #j u = Seq.empty #(entry #j u) in
    ((| u, B.malloc q_pne_region l 1ul |) <: model_state j)
  else
    (u, random (Spec.key_length u.calg)) <: unsafe_state j

let coerce j u k =
  (u, k) <: unsafe_state j

let quic_coerce j u ts =
  let k =
    (QUIC.Spec.derive_secret u.halg ts
        QUIC.Spec.label_hp (key_len u)) in
  coerce j u k

let random_bits (): bits =
  LowParse.BitFields.get_bitfield #8 (UInt8.v (Lib.RawIntTypes.u8_to_UInt8 (Seq.index (random 1) 0))) 0 5

let encrypt #j #u st #l n s =
  let h0 = ST.get () in
  if is_safe j then
    let (| u, p |) = st <: model_state j in
    let log = !*p in
    assert (log == table st h0);
    let cipher: pne_cipherpad = random 5, random_bits () in
    p *= Seq.snoc log (Entry s #l n cipher);
    clip_cipherpad cipher l
  else
    let open QUIC.Spec.Lemmas in
    let pn, bits = PNEPlainPkg?.repr u.plain j l n in
    let k = snd (st <: unsafe_state j) in
    let alg = (fst (st <: unsafe_state j)).calg in
    encrypt_spec alg l pn bits s k

#push-options "--fuel 1"
let snoc_find #a (s: Seq.seq a) (f: a -> bool) (x: a): Lemma
  (requires f x /\ None? FStar.Seq.(find_l f s))
  (ensures FStar.Seq.(find_l f (snoc s x)) == Some x)
=
  assert (Seq.snoc s x `Seq.equal` Seq.append s (Seq.create 1 x));
  Seq.find_append_none s (Seq.create 1 x) f;
  ()
#pop-options

let decrypt #j #u st cp s =
  if is_safe j then
    let (| info, p |) = st <: model_state j in
    let log = !*p in
    match Seq.find_l (sample_filter u s) log with
    | Some (Entry _ #l' n' c') ->
        // The sample is present in the table, cipher may or may not match, it's
        // up to the caller to prove that when there's a match (i.e. c' == cp)
        // then c'' == zeroes which then entails that the returns value is the
        // plaintext that was in the table
        let c'' = c' `xor_cipherpad` cp in
        PNEPlainPkg?.xor u.plain j l' n' c''
    | None ->
        // Need to add into the table:
        let bits = random_bits () in
        let l = LowParse.BitFields.get_bitfield bits 0 2 + 1 in
        let c' = random 5, bits in
        // let n' = clip_cipherpad (c' `xor_cipherpad` cp) l in
        let n = PNEPlainPkg?.mk u.plain j l (random l) bits in
        let new_log = Seq.snoc log (Entry s #l n c') in
        p *= new_log;
        snoc_find log (sample_filter u s) (Entry s #l n c');
        PNEPlainPkg?.xor u.plain j l n (c' `xor_cipherpad` cp)
  else
    let info, k = st <: unsafe_state j in
    decrypt_spec info.calg (fst cp) (snd cp) k s
