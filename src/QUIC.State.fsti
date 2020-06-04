module QUIC.State

open EverCrypt.Error
include QUIC.Spec.Crypto
include QUIC.Impl.Header.Base

module B = LowStar.Buffer
module HS = FStar.HyperStack
module Seq = QUIC.Secret.Seq
module PN = QUIC.Spec.PacketNumber.Base
module HST = FStar.HyperStack.ST
module Secret = QUIC.Secret.Int
module G = FStar.Ghost
module U8 = FStar.UInt8
module U32 = FStar.UInt32
module Base = QUIC.Impl.Header.Base
module Spec = QUIC.Spec

#set-options "--z3rlimit 16"

/// This is not a cryptographic index; rather, this is just a regular type
/// index, where instead of indexing on a single algorithm (like, say, AEAD), we
/// index on two values.
///
/// The record is here to limit the profileration of hide/reveal in the stateful
/// functions, and to give easier projectors (, ).
type index = {
  hash_alg: ha;
  aead_alg: ea
}


/// Boilerplate
/// -----------

[@CAbstractStruct]
val state_s: index -> Type0

let state i = B.pointer (state_s i)

val footprint_s: #i:index -> HS.mem -> state_s i -> GTot B.loc
let footprint (#i:index) (m: HS.mem) (s: state i) =
  B.(loc_union (loc_addr_of_buffer s) (footprint_s m (B.deref m s)))

let loc_includes_union_l_footprint_s
  (m: HS.mem)
  (l1 l2: B.loc) (#a: index) (s: state_s a)
: Lemma
  (requires (
    B.loc_includes l1 (footprint_s m s) \/ B.loc_includes l2 (footprint_s m s)
  ))
  (ensures (B.loc_includes (B.loc_union l1 l2) (footprint_s m s)))
  [SMTPat (B.loc_includes (B.loc_union l1 l2) (footprint_s m s))]
= B.loc_includes_union_l l1 l2 (footprint_s m s)

/// Ghost accessors (not needing the invariant)
/// -------------------------------------------
///
/// We need to define those, so that we can state a framing lemma for them.
/// Attempting a new convention to distinguish ghost accessors from stateful
/// functions: a ``g_`` prefix.

/// See remark for ``g_initial_packet_number`` below.
val g_traffic_secret: #i:index -> (s: state_s i) ->
  GTot (Spec.Hash.Definitions.bytes_hash i.hash_alg)

#push-options "--max_ifuel 1" // inversion on hash_alg
let hash_is_keysized #i (s: state_s i): Lemma
  (ensures (keysized i.hash_alg (Seq.length (g_traffic_secret s))))
  [ SMTPat (g_traffic_secret s) ]
=
  assert_norm (512 < pow2 61);
  assert_norm (512 < pow2 125)
#pop-options

/// Note that this one does *NOT* take the memory as an argument. (This is
/// because the initial packet number is erased in the concrete state.) Callers
/// should be able to derive, from this, that the initial packet number remains
/// the same, thanks to the precise use of footprint_s in encrypt/decrypt.
val g_initial_packet_number: #i:index -> (s: state_s i) -> GTot PN.packet_number_t

/// Invariant
/// ---------

val invariant_s: (#i:index) -> HS.mem -> state_s i -> Type0
let invariant (#i:index) (m: HS.mem) (s: state i) =
  let r = B.frameOf s in
  HST.is_eternal_region r /\
  B.loc_includes (B.loc_region_only true r) (footprint m s) /\
  B.live m s /\
  B.(loc_disjoint (loc_addr_of_buffer s) (footprint_s m (B.deref m s))) /\
  invariant_s m (B.get m s 0)

val invariant_loc_in_footprint
  (#i: index)
  (s: state i)
  (m: HS.mem)
: Lemma
  (requires (invariant m s))
  (ensures (B.loc_in (footprint m s) m))
  [SMTPat (invariant m s)]


/// Ghost accessors needing the invariant
/// -------------------------------------

val g_last_packet_number: #i:index -> (s: state_s i) -> (h: HS.mem { invariant_s h s }) ->
  GTot (pn: PN.packet_number_t {
    Secret.v pn >= Secret.v (g_initial_packet_number s)
  })

let incrementable (#i: index) (s: state i) (h: HS.mem { invariant h s }) =
  Secret.v (g_last_packet_number (B.deref h s) h) + 1 < pow2 62

/// Preserving all the ghost accessors via a single framing lemma only works
/// because we don't do stack allocation. See comments in
/// EverCrypt.Hash.Incremental.
val frame_invariant: #i:index -> l:B.loc -> s:state i -> h0:HS.mem -> h1:HS.mem -> Lemma
  (requires (
    invariant h0 s /\
    B.loc_disjoint l (footprint h0 s) /\
    B.modifies l h0 h1))
  (ensures (
    invariant h1 s /\
    footprint h0 s == footprint h1 s /\
    g_last_packet_number (B.deref h0 s) h0 == g_last_packet_number (B.deref h1 s) h0 /\
    g_traffic_secret (B.deref h0 s) == g_traffic_secret (B.deref h1 s)
    ))
  // Assertion failure: unexpected pattern term
  (*[ SMTPat (B.modifies l h0 h1); SMTPatOr [
    [ SMTPat (invariant h1 s) ];
    [ SMTPat (footprint h1 s) ];
    [ SMTPat (g_aead_key (B.deref h1 s)) ];
    [ SMTPat (g_counter (B.deref h1 s)) ]
  ]]*)



/// Actual stateful API
/// -------------------

val aead_alg_of_state (#i: G.erased index) (s: state (G.reveal i)): HST.Stack ea
  (requires (fun h0 -> invariant #(G.reveal i) h0 s))
  (ensures (fun h0 a h1 ->
    a == (G.reveal i).aead_alg /\
    h0 == h1))

val hash_alg_of_state (#i: G.erased index) (s: state (G.reveal i)): HST.Stack ha
  (requires (fun h0 -> invariant #(G.reveal i) h0 s))
  (ensures (fun h0 a h1 ->
    a == (G.reveal i).hash_alg /\
    h0 == h1))

val last_packet_number_of_state (#i: G.erased index) (s: state (G.reveal i)): HST.Stack PN.packet_number_t
  (requires fun h0 -> invariant h0 s)
  (ensures fun h0 ctr h1 ->
    ctr == g_last_packet_number (B.deref h0 s) h0 /\
    h0 == h1)

// : we could be defensive and allow callers to pass potentially unsupported
// algorithms; however, this would require a lot more machinery as we would not
// even be able to state the index type, since index currently has a refinement
// that the two algorithms are supported. We would have to separate index into
// index0 and a well-formedness refinement. Not sure it's worth it. We can
// always perform redundant tests inside the definition of create to be fully
// defensive.
inline_for_extraction noextract
let create_in_st (i:index) =
  r:HS.rid ->
  dst: B.pointer (B.pointer_or_null (state_s i)) ->
  initial_pn:PN.packet_number_t ->
  traffic_secret:B.buffer Secret.uint8 {
    B.length traffic_secret = Spec.Hash.Definitions.hash_length i.hash_alg
  } ->
  HST.ST error_code
    (requires fun h0 ->
      // : we could require that ``dst`` point to NULL prior to calling
      // ``create`` (otherwise, it's a memory leak). Other modules don't enforce
      // this (see AEAD) so for now, let's make the caller's life easier and not
      // demand anything.
      HST.is_eternal_region r /\
      B.live h0 dst /\ B.live h0 traffic_secret /\
      B.disjoint dst traffic_secret)
    (ensures (fun h0 e h1 ->
      match e with
      | UnsupportedAlgorithm ->
          B.(modifies loc_none h0 h1)
      | Success ->
          let s = B.deref h1 dst in
          not (B.g_is_null s) /\
          invariant h1 s /\

          B.(modifies (loc_buffer dst) h0 h1) /\
          B.fresh_loc (footprint h1 s) h0 h1 /\

          g_traffic_secret (B.deref h1 s) == B.as_seq h0 traffic_secret /\ 
          g_last_packet_number (B.deref h1 s) h1 == initial_pn /\

          g_initial_packet_number (B.deref h1 s) == initial_pn
      | _ ->
          False))

// The index is passed at run-time.
val create_in: i:index -> create_in_st i


(* Useful shortcuts *)

let derive_k
  (i: index)
  (s: state i)
  (h: HS.mem)
: GTot (Seq.seq Secret.uint8)
=
  let s0 = g_traffic_secret (B.deref h s) in
  Spec.derive_secret i.hash_alg s0 Spec.label_key (Spec.Agile.AEAD.key_length i.aead_alg)

let derive_iv
  (i: index)
  (s: state i)
  (h: HS.mem)
: GTot (Seq.seq Secret.uint8)
= let s0 = g_traffic_secret (B.deref h s) in
  Spec.derive_secret i.hash_alg s0 Spec.label_iv 12

let derive_pne
  (i: index)
  (s: state i)
  (h: HS.mem)
: GTot (Seq.seq Secret.uint8)
= let s0 = g_traffic_secret (B.deref h s) in
  Spec.derive_secret i.hash_alg s0 Spec.label_hp (cipher_keysize i.aead_alg)

val encrypt: #i:G.erased index -> (
  let i = G.reveal i in
  s: state i ->
  dst: B.buffer U8.t ->
  dst_pn: B.pointer PN.packet_number_t ->
  h: header ->
  plain: B.buffer Secret.uint8 ->
  plain_len: U32.t ->
  HST.Stack error_code
    (requires fun h0 ->
      // Memory & preservation
      B.live h0 plain /\ B.live h0 dst /\ B.live h0 dst_pn /\
      header_live h h0 /\
      B.(all_disjoint [ footprint h0 s; loc_buffer dst; loc_buffer dst_pn; header_footprint h; loc_buffer plain ]) /\
      invariant h0 s /\
      incrementable s h0 /\
      B.length plain == U32.v plain_len /\ (
      let clen = if is_retry h then 0 else U32.v plain_len + Spec.Agile.AEAD.tag_length i.aead_alg in
      (if is_retry h then U32.v plain_len == 0 else 3 <= U32.v plain_len /\ U32.v plain_len < Spec.max_plain_length) /\
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
          packet == Spec.encrypt i.aead_alg k iv pne (g_header h h0 pn) (Seq.seq_reveal plain) /\
          g_last_packet_number (B.deref h1 s) h1 == pn)
      | _ ->
          False))

val initial_secrets (dst_client: B.buffer Secret.uint8)
  (dst_server: B.buffer Secret.uint8)
  (cid: B.buffer Secret.uint8)
  (cid_len: U32.t):
  HST.Stack unit
    (requires (fun h0 ->
      B.(all_live h0 [ buf dst_client; buf dst_server; buf cid ]) /\
      B.length dst_client = Spec.Agile.Hash.(hash_length SHA2_256) /\
      B.length dst_server = Spec.Agile.Hash.(hash_length SHA2_256) /\
      B.length cid = U32.v cid_len /\
      U32.v cid_len <= 20 /\
      B.(all_disjoint [ loc_buffer dst_client; loc_buffer dst_server; loc_buffer cid ])))
    (ensures (fun h0 _ h1 ->
      B.(modifies (loc_buffer dst_client `loc_union` loc_buffer dst_server) h0 h1)))

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
  let max (x y: nat) : Tot nat = if x >= y then x else y in
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
      Secret.v (g_last_packet_number (B.deref h1 s) h1) == max (Secret.v prev) (Secret.v r.Base.pn) /\ (

      // Lengths
      r.header_len == header_len r.header /\
      Secret.v r.header_len + Secret.v r.plain_len <= Secret.v r.total_len /\
      Secret.v r.total_len <= B.length packet /\
      B.(loc_includes (loc_buffer (B.gsub packet 0ul (Secret.reveal r.header_len))) (header_footprint r.header)) /\
      header_live r.header h1 /\
      Secret.v r.total_len <= B.length packet /\
      
      // Contents
      (
      let fmt = B.as_seq h1 (B.gsub packet 0ul (Secret.reveal r.header_len)) in
      let plain =
        B.as_seq h1 (B.gsub packet (Secret.reveal r.header_len) (Secret.reveal r.plain_len)) in
      let rem = B.as_seq h0 (B.gsub packet (Secret.reveal r.total_len) (B.len packet `U32.sub `Secret.reveal r.total_len)) in
      match Spec.decrypt i.aead_alg k iv pne (Secret.v prev) (U8.v cid_len) (B.as_seq h0 packet) with
      | Spec.Success h' plain' rem' ->
        h' == g_header r.header h1 r.Base.pn /\
        fmt == QUIC.Spec.Header.Parse.format_header h' /\
        plain' == plain /\
        rem' == rem
      | _ -> False
    ))
    | DecodeError ->
      Spec.Failure? (Spec.decrypt i.aead_alg k iv pne (Secret.v prev) (U8.v cid_len) (B.as_seq h0 packet))
    | AuthenticationFailure ->
      Spec.Failure? (Spec.decrypt i.aead_alg k iv pne (Secret.v prev) (U8.v cid_len) (B.as_seq h0 packet)) /\
      Secret.v r.total_len <= B.length packet
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
  HST.Stack error_code
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
        loc_buffer (gsub packet 0ul (Secret.reveal r.total_len)) `loc_union` loc_buffer dst) h0 h1)
      | DecodeError ->
        B.modifies B.loc_none h0 h1
      | AuthenticationFailure ->
        B.(modifies (footprint_s h0 (deref h0 s) `loc_union`
        loc_buffer (gsub packet 0ul (Secret.reveal r.total_len)) `loc_union` loc_buffer dst) h0 h1)
      | _ -> False
      end
    )
  )
