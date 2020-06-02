module Model.AEAD

module HS = FStar.HyperStack
module I = Model.Indexing
module U32 = FStar.UInt32
module U128 = FStar.UInt128
module B = LowStar.Buffer
module Spec = Spec.Agile.AEAD

#set-options "--fuel 0 --ifuel 0"

open Mem
open LowStar.BufferOps
open Model.Helpers

let log #i (u: info i): Type0 =
  Seq.seq (entry i u)

let model_writer i =
  u:info i & B.pointer (log #i u)

let unsafe_writer i =
  info i & Spec.kv (I.ae_id_ginfo i)

let aead_writer (i: id): Type u#1 =
  if is_safe i then
    model_writer i
  else
    unsafe_writer i

let aead_reader #i (w: aead_writer i): Type u#1 =
  w':aead_writer i { w' == w }

let wgetinfo #i (u: aead_writer i) =
  if is_safe i then
    dfst (u <: model_writer i)
  else
    fst (u <: unsafe_writer i)

let rgetinfo #_ #w _ =
  wgetinfo w

let wlog #i w h =
  B.deref h (dsnd (w <: model_writer i))

let wkey #i w =
  snd (w <: unsafe_writer i)

let wfootprint #i w =
  if is_safe i then
    B.loc_addr_of_buffer (dsnd (w <: model_writer i))
  else
    B.loc_none

let winvariant #i w h =
  if is_safe i then
    B.live h (dsnd (w <: model_writer i))
  else
    True

let wframe_invariant #_ w h0 l h1 =
  ()

let frame_log #_ w h0 l h1 =
  ()

let gen i u =
  if is_safe i then
    let l: log #i u = Seq.empty #(entry i u) in
    ((| u, B.malloc q_ae_region l 1ul |) <: model_writer i)
  else
    let key_l = Spec.key_length u.alg in
    (u, random key_l) <: unsafe_writer i

let gen_reader #i w =
  w

let coerce #i u kv =
  (u, kv) <: unsafe_writer i

// With QUIC-specific derivation of key from transport secret
let quic_coerce #i u ts =
  coerce u
    (QUIC.Spec.derive_secret u.halg ts
      QUIC.Spec.label_key (Spec.key_length u.alg))

let encrypt i w nonce aad plain_length plain =
  if is_safe i then
    let a = (wgetinfo w).alg in
    let w: model_writer i = w in
    let p = dsnd w in
    let log = !*p in
    let cipher_length = (plain_length <: nat) + Spec.tag_length a in
    let cipher = random cipher_length in
    p *= Seq.snoc log (Entry #i #(wgetinfo w) nonce aad #plain_length plain cipher);
    cipher
  else
    let a = (wgetinfo w).alg in
    let k: Spec.kv a = wkey w in
    let iv = NoncePkg?.repr (wgetinfo w).nonce i nonce in
    let p = PlainPkg?.repr (wgetinfo w).plain i plain_length plain in
    Spec.encrypt #a k iv aad p

let decrypt i #w r aad n l c =
  if is_safe i then
    let w: model_writer i = w in
    let log = !*(dsnd w) in
    match Seq.find_l (nonce_filter n) log with
    | None -> None
    | Some (Entry n' aad' #l' p' c') ->
        assert (n == n');
        if lbytes_eq aad aad' && lbytes_eq c c' && l = l' then
          Some p'
        else
          None
  else
    let a = (wgetinfo w).alg in
    let k: Spec.kv a = wkey w in
    let iv = NoncePkg?.repr (wgetinfo w).nonce i n in
    match Spec.decrypt k iv aad c with
    | None -> None
    | Some p ->
        Some ((wgetinfo w).plain.mk i (Seq.length p) p)
