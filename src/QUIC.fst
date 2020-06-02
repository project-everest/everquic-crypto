module QUIC

module QSpec = QUIC.Spec
module QImpl = QUIC.Impl
module QImplBase = QUIC.Impl.Base
module QModel = Model.QUIC

module I = Model.Indexing
module G = FStar.Ghost
module B = LowStar.Buffer
module S = FStar.Seq
module HS = FStar.HyperStack
module ST = FStar.HyperStack.ST

module U64 = FStar.UInt64
module U32 = FStar.UInt32
module U8 = FStar.UInt8

open FStar.HyperStack
open FStar.HyperStack.ST

open EverCrypt.Helpers
open EverCrypt.Error

let index =
  if I.model then QModel.id else QImpl.index

let mid (i:index{I.model}) = i <: QModel.id
let iid (i:index{not I.model}) = i <: QImpl.index

let alg (i:index) =
  if I.model then I.ae_id_ginfo (fst (mid i))
  else (iid i).QImpl.aead_alg

let halg (i:index) =
  if I.model then I.ae_id_ghash (fst (mid i))
  else (iid i).QImpl.hash_alg

let itraffic_secret (i:QModel.id) =
  Spec.Hash.Definitions.bytes_hash (I.ae_id_ghash (fst i))

module MH = Model.Helpers

let derived (#i:QModel.id) (#w:QModel.stream_writer i) (r:QModel.stream_reader w) (ts:itraffic_secret i) =
  if I.model && QModel.unsafe i then
    let ha = I.ae_id_hash (fst i) in
    let ea = I.ae_id_info (fst i) in
    let (k1, k2) = QModel.reader_leak r in
    QModel.writer_static_iv w ==
      QSpec.derive_secret ha ts QSpec.label_iv 12 /\
    k1 == QSpec.derive_secret ha ts
        QSpec.label_key (QSpec.ae_keysize ea) /\
    k2 == QUIC.Spec.derive_secret ha ts
        QUIC.Spec.label_key (QSpec.cipher_keysize ea)
  else True

noeq type mstate_t i =
| Ideal:
  writer: QModel.stream_writer i ->
  reader: QModel.stream_reader writer ->
  ts: itraffic_secret i{derived reader ts} -> // FIXME erased
  mstate_t i
  
let istate_t i = QImpl.state i

let state i =
  if I.model then mstate_t (mid i)
  else istate_t (iid i)

let mstate (#i:index{I.model}) (s:state i) = s <: mstate_t (mid i)
let istate (#i:index{not I.model}) (s:state i) = s <: istate_t (iid i)

let footprint #i h s =
  if I.model then
    QModel.rfootprint (mstate s).reader
  else QImpl.footprint h (istate s)

let invariant #i h s =
  if I.model then
    QModel.invariant (mstate s).writer h <: Type0
  else QImpl.invariant h (istate s)

let g_traffic_secret #i s h =
  if I.model then (mstate s).ts
  else
    QImpl.g_traffic_secret (B.deref h (istate s))

let g_initial_packet_number #i s h =
  if I.model then admit ()
  else
    QImpl.g_initial_packet_number (B.deref h (istate s)) h

let g_last_packet_number #i s h =
  if I.model then
    QModel.expected_pnT (mstate s).reader h
  else
    QImpl.g_last_packet_number (B.deref h (istate s)) h
