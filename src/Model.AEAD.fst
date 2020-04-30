module Model.AEAD

module HS = FStar.HyperStack
module I = Model.Indexing
module U32 = FStar.UInt32
module U128 = FStar.UInt128
module B = LowStar.Buffer
module Spec = Spec.Agile.AEAD

#set-options "--fuel 0 --ifuel 0"

open Mem

let log #i (u: info i): Type0 =
  if is_safe i then
    Seq.seq (entry i u)
  else
    unit

let model_writer i =
  u:info i & B.pointer (log #i u)

let aead_writer (i: id): Type u#1 =
  if is_safe i then
    model_writer i
  else
    info i

let aead_reader #i (w: aead_writer i): Type u#1 =
  w':aead_writer i { w' == w }

let wgetinfo #i (u: aead_writer i) =
  if is_safe i then
    dfst (u <: model_writer i)
  else
    u

// JP: is this correct?
let rgetinfo #_ u =
  wgetinfo u

let wlog #i w h =
  B.deref h (dsnd (w <: model_writer i))

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
    (u <: aead_writer i)
