module QUIC.Impl.Crypto
include QUIC.Spec.Crypto

open EverCrypt.Error

module B = LowStar.Buffer
module HS = FStar.HyperStack
module S = FStar.Seq
module PN = QUIC.Spec.PacketNumber.Base
module HST = FStar.HyperStack.ST
module Secret = QUIC.Secret.Int
module G = FStar.Ghost
module U8 = FStar.UInt8
module IB = LowStar.ImmutableBuffer
module Spec = QUIC.Spec.Crypto



/// Globals
/// -------

val label_key : (label_key: IB.ibuffer U8.t {
  IB.frameOf label_key == HS.root /\
  IB.length label_key == Seq.length Spec.label_key /\
  IB.recallable label_key /\
  IB.witnessed label_key (IB.cpred Spec.label_key)
})

val label_iv : (label_iv : IB.ibuffer U8.t {
  IB.frameOf label_key == HS.root /\
  IB.length label_iv == Seq.length Spec.label_iv /\
  IB.recallable label_iv /\
  IB.witnessed label_iv (IB.cpred Spec.label_iv)
})

val label_hp : (label_hp : IB.ibuffer U8.t {
  IB.frameOf label_hp == HS.root /\
  IB.length label_hp == Seq.length Spec.label_hp /\
  IB.recallable label_hp /\
  IB.witnessed label_hp (IB.cpred Spec.label_hp)
})

/// Actual code
/// -----------

#push-options "--max_ifuel 1 --initial_ifuel 1 --z3rlimit 10"
/// One ifuel for inverting on the hash algorithm for computing bounds (the
/// various calls to assert_norm should help ensure this proof goes through
/// reliably). Note that I'm breaking from the usual convention where lengths
/// are UInt32's, mostly to avoid trouble reasoning with modulo when casting
/// from UInt32 to UInt8 to write the label for the key derivation. This could
/// be fixed later.
val derive_secret: a: ha ->
  dst:B.buffer Secret.uint8 ->
  dst_len: U8.t { B.length dst = U8.v dst_len /\ U8.v dst_len <= 255 } ->
  secret:B.buffer Secret.uint8 { B.length secret = Spec.Hash.Definitions.hash_length a } ->
  label:IB.ibuffer U8.t ->
  label_len:U8.t { IB.length label = U8.v label_len /\ U8.v label_len <= 244 } ->
  HST.Stack unit
    (requires fun h0 ->
      B.(all_live h0 [ buf secret; buf label; buf dst ]) /\
      B.disjoint dst secret)
    (ensures fun h0 _ h1 ->
      assert_norm (255 < pow2 61);
      assert_norm (pow2 61 < pow2 125);
      B.(modifies (loc_buffer dst) h0 h1) /\
      B.as_seq h1 dst == derive_secret a (B.as_seq h0 secret)
        (IB.as_seq h0 label) (U8.v dst_len))
#pop-options
