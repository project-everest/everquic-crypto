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

let rgetinfo #_ u =
  wgetinfo u

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

let random (l: nat { l < pow2 32 }): Spec.lbytes l =
  let open Lib.RandomSequence in
  snd (crypto_random entropy0 l)

let gen i u =
  if is_safe i then
    let l: log #i u = Seq.empty #(entry i u) in
    ((| u, B.malloc q_ae_region l 1ul |) <: model_writer i)
  else
    let key_l = Spec.key_length u.alg in
    u, random key_l

let gen_reader #i w =
  w

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

let rec equal (x y: Seq.seq Spec.uint8): Tot (b:bool { b <==> x `Seq.equal` y }) (decreases (Seq.length x)) =
  if Seq.length x = 0 && Seq.length y = 0 then
    true
  else if Seq.length x = 0 && Seq.length y <> 0 then
    false
  else if Seq.length x <> 0 && Seq.length y = 0 then
    false
  else
    let hx = Seq.head x in
    let hy = Seq.head y in
    let tx = Seq.tail x in
    let ty = Seq.tail y in
    if Lib.RawIntTypes.u8_to_UInt8 hx = Lib.RawIntTypes.u8_to_UInt8 hy && equal tx ty then begin
      assert (x `Seq.equal` Seq.append (Seq.create 1 hx) tx);
      assert (y `Seq.equal` Seq.append (Seq.create 1 hy) ty);
      assert (Seq.index (Seq.create 1 hx) 0 == Seq.index (Seq.create 1 hy) 0);
      assert (Seq.create 1 hx `Seq.equal` Seq.create 1 hy);
      true
    end else
      false

let decrypt i #w r aad n l c =
  if is_safe i then
    let w: model_writer i = w in
    let log = !*(dsnd w) in
    match Seq.find_l (nonce_filter n) log with
    | None -> None
    | Some (Entry n' aad' #l' p' c') ->
        assert (n == n');
        if equal aad aad' && equal c c' && l = l' then
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
