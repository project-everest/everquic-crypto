/// An implementation of QUIC.Spec.fst that is concerned only with functional
/// correctness (no notion of model for now).
module QUIC.Impl
include QUIC.Impl.Crypto
include QUIC.Impl.Header.Base

module QSpec = QUIC.Spec
module QImpl = QUIC.Impl.Header.Base
module PN = QUIC.Spec.PacketNumber.Base
module Secret = QUIC.Secret.Int

// This MUST be kept in sync with QUIC.Impl.fst...
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

#set-options "--max_fuel 0 --max_ifuel 0"
// ... up to here!

unfold noextract
let lbytes = QUIC.Spec.Base.lbytes

// Reexport this function, which was lost in the bundle
let header_len = QUIC.Impl.Header.Base.header_len

/// Low-level types used in this API
/// --------------------------------

type u2 = n:U8.t{U8.v n < 4}
type u4 = n:U8.t{U8.v n < 16}
type u62 = n:UInt64.t{UInt64.v n < pow2 62}

#restart-solver

(* Useful shortcuts *)

let derive_k
  (i: index)
  (s: state i)
  (h: HS.mem)
: GTot (Seq.seq Secret.uint8)
=
  let s0 = g_traffic_secret (B.deref h s) in
  derive_secret i.hash_alg s0 label_key (Spec.Agile.AEAD.key_length i.aead_alg)

let derive_iv
  (i: index)
  (s: state i)
  (h: HS.mem)
: GTot (Seq.seq Secret.uint8)
= let s0 = g_traffic_secret (B.deref h s) in
  derive_secret i.hash_alg s0 label_iv 12

let derive_pne
  (i: index)
  (s: state i)
  (h: HS.mem)
: GTot (Seq.seq Secret.uint8)
= let s0 = g_traffic_secret (B.deref h s) in
  derive_secret i.hash_alg s0 label_hp (ae_keysize i.aead_alg)


val encrypt: #i:G.erased index -> (
  let i = G.reveal i in
  s: state i ->
  dst: B.buffer U8.t ->
  dst_pn: B.pointer PN.packet_number_t ->
  h: header ->
  plain: B.buffer U8.t ->
  plain_len: U32.t ->
  Stack error_code
    (requires fun h0 ->
      // Memory & preservation
      B.live h0 plain /\ B.live h0 dst /\ B.live h0 dst_pn /\
      header_live h h0 /\
      B.(all_disjoint [ footprint h0 s; loc_buffer dst; loc_buffer dst_pn; header_footprint h; loc_buffer plain ]) /\
      invariant h0 s /\
      incrementable s h0 /\
      B.length plain == U32.v plain_len /\ (
      let clen = if is_retry h then 0 else U32.v plain_len + Spec.Agile.AEAD.tag_length i.aead_alg in
      (if is_retry h then U32.v plain_len == 0 else 3 <= U32.v plain_len /\ U32.v plain_len < QSpec.max_plain_length) /\
      (has_payload_length h ==> Secret.v (payload_length h) == clen) /\
      B.length dst == Secret.v (header_len h) + clen
    ))
    (ensures fun h0 r h1 ->
      match r with
      | Success ->
          // Memory & preservation
          B.(modifies (footprint_s h0 (deref h0 s) `loc_union` loc_buffer dst `loc_union` loc_buffer dst_pn)) h0 h1 /\
          invariant h1 s /\
          footprint_s h1 (B.deref h1 s) == footprint_s h0 (B.deref h0 s) /\ (
          // Functional correctness
          let k = derive_k i s h0 in
          let iv = derive_iv i s h0 in
          let pne = derive_pne i s h0 in
          let plain = B.as_seq h0 plain in
          let packet: packet = B.as_seq h1 dst in
          let pn = g_last_packet_number (B.deref h0 s) h0 `Secret.add` Secret.to_u64 1uL in
          B.deref h1 dst_pn == pn /\
          packet == QSpec.encrypt i.aead_alg k iv pne (g_header h h0 pn) plain /\
          g_last_packet_number (B.deref h1 s) h1 == pn)
      | _ ->
          False))

val initial_secrets (dst_client: B.buffer U8.t)
  (dst_server: B.buffer U8.t)
  (cid: B.buffer U8.t)
  (cid_len: U32.t):
  Stack unit
    (requires (fun h0 ->
      B.(all_live h0 [ buf dst_client; buf dst_server; buf cid ]) /\
      B.length dst_client = Spec.Agile.Hash.(hash_length SHA2_256) /\
      B.length dst_server = Spec.Agile.Hash.(hash_length SHA2_256) /\
      B.length cid = U32.v cid_len /\
      U32.v cid_len <= 20 /\
      B.(all_disjoint [ loc_buffer dst_client; loc_buffer dst_server; loc_buffer cid ])))
    (ensures (fun h0 _ h1 ->
      B.(modifies (loc_buffer dst_client `loc_union` loc_buffer dst_server) h0 h1)))

// Callers allocate this type prior to calling decrypt. The contents are only
// meaningful, and plain is only non-null, if the decryption was a success.
noeq
type result = {
  pn: PN.packet_number_t;
  header: header;
  header_len: U32.t;
  plain_len: n:U32.t;
  total_len: n:U32.t
}

noextract
let max (x y: nat) = if x >= y then x else y

unfold
let decrypt_post (i: index)
  (s:state i)
  (dst: B.pointer result)
  (packet: B.buffer U8.t)
  (len: U32.t)
  (cid_len: U8.t)
  (h0: HS.mem)
  (res: error_code)
  (h1: HS.mem): Pure Type0
  (requires
    U8.v cid_len <= 20 /\
    U32.v len == B.length packet /\
    invariant h0 s /\
    incrementable s h0)
  (ensures fun _ -> True)
=
  let k = derive_k i s h0 in
  let iv = derive_iv i s h0 in
  let pne = derive_pne i s h0 in
  let prev = g_last_packet_number (B.deref h0 s) h0 in
  invariant h1 s /\
  footprint_s h1 (B.deref h1 s) == footprint_s h0 (B.deref h0 s) /\
  begin
    let r = B.deref h1 dst in
    match res with
    | Success ->
      // prev is known to be >= g_initial_packet_number (see lemma invariant_packet_number)
      Secret.v (g_last_packet_number (B.deref h1 s) h1) == max (Secret.v prev) (Secret.v r.pn) /\ (

      // Lengths
      r.header_len == Secret.reveal (header_len r.header) /\
      U32.v r.header_len + U32.v r.plain_len <= U32.v r.total_len /\
      U32.v r.total_len <= B.length packet /\
      B.(loc_includes (loc_buffer (B.gsub packet 0ul r.header_len)) (header_footprint r.header)) /\
      header_live r.header h1 /\
      U32.v r.total_len <= B.length packet /\
      
      // Contents
      (
      let plain =
        S.slice (B.as_seq h1 packet) (U32.v r.header_len)
          (U32.v r.header_len + U32.v r.plain_len) in
      let rem = B.as_seq h0 (B.gsub packet r.total_len (B.len packet `U32.sub `r.total_len)) in
      match QSpec.decrypt i.aead_alg k iv pne (Secret.v prev) (U8.v cid_len) (B.as_seq h0 packet) with
      | QSpec.Success h' plain' rem' ->
        h' == g_header r.header h1 r.pn /\
        plain' == plain /\
        rem' == rem
      | _ -> False
    ))
    | DecodeError ->
      QSpec.Failure? (QSpec.decrypt i.aead_alg k iv pne (Secret.v prev) (U8.v cid_len) (B.as_seq h0 packet))
    | AuthenticationFailure ->
      QSpec.Failure? (QSpec.decrypt i.aead_alg k iv pne (Secret.v prev) (U8.v cid_len) (B.as_seq h0 packet)) /\
      U32.v r.total_len <= B.length packet
    | _ ->
      False
  end

val decrypt: #i:G.erased index -> (
  let i = G.reveal i in
  s:state i ->
  dst: B.pointer result ->
  packet: B.buffer U8.t ->
  len: U32.t{
    B.length packet == U32.v len
  } ->
  cid_len: U8.t { U8.v cid_len <= 20 } ->
  Stack error_code
    (requires fun h0 ->
      // We require clients to allocate space for a result, e.g.
      //   result r = { 0 };
      //   decrypt(s, &r, ...);
      // This means that we don't require that the pointers inside ``r`` be live
      // (i.e. NO ``header_live header`` precondition).
      // After a successful call to decrypt, ``packet`` contains the decrypted
      // data; ``header`` is modified to point within the header area of
      // ``packet``; and the plaintext is within ``packet`` in range
      // ``[header_len, header_len + plain_len)``.
      B.live h0 packet /\ B.live h0 dst /\
      B.(all_disjoint [ loc_buffer dst; loc_buffer packet; footprint h0 s ]) /\
      invariant h0 s /\
      incrementable s h0)
    (ensures fun h0 res h1 ->
      let r = B.deref h1 dst in
      decrypt_post i s dst packet len cid_len h0 res h1 /\
      begin match res with
      | Success ->
      B.(modifies (footprint_s h0 (deref h0 s) `loc_union`
        loc_buffer (gsub packet 0ul r.total_len) `loc_union` loc_buffer dst) h0 h1)
      | DecodeError ->
        B.modifies (footprint_s h0 (B.deref h0 s) `B.loc_union` B.loc_buffer packet) h0 h1
      | AuthenticationFailure ->
        B.(modifies (footprint_s h0 (deref h0 s) `loc_union`
        loc_buffer (gsub packet 0ul r.total_len) `loc_union` loc_buffer dst) h0 h1)
      | _ -> False
      end
    )
  )
