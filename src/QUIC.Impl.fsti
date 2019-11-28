/// An implementation of QUIC.Spec.fst that is concerned only with functional
/// correctness (no notion of model for now).
module QUIC.Impl
include QUIC.Impl.Base

module QSpec = QUIC.Spec
module QImpl = QUIC.Impl.Base

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
let hash_alg = Spec.Hash.Definitions.hash_alg

unfold noextract
let aead_alg = Spec.Agile.AEAD.alg

unfold noextract
let lbytes = QSpec.lbytes

/// This is not a cryptographic index; rather, this is just a regular type
/// index, where instead of indexing on a single algorithm (like, say, AEAD), we
/// index on two values.
///
/// The record is here to limit the profileration of hide/reveal in the stateful
/// functions, and to give easier projectors (ADL, JP).
type index = {
  hash_alg: QSpec.ha;
  aead_alg: QSpec.ea
}

// Reexport this function, which was lost in the bundle
let header_len = QUIC.Impl.Base.header_len

/// Low-level types used in this API
/// --------------------------------

type u2 = n:U8.t{U8.v n < 4}
type u4 = n:U8.t{U8.v n < 16}
type u62 = n:UInt64.t{UInt64.v n < pow2 62}

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
  (ensures (QSpec.keysized i.hash_alg (S.length (g_traffic_secret s))))
  [ SMTPat (g_traffic_secret s) ]
=
  assert_norm (512 < pow2 61);
  assert_norm (512 < pow2 125)
#pop-options

/// Note that this one does *NOT* take the memory as an argument. (This is
/// because the initial packet number is erased in the concrete state.) Callers
/// should be able to derive, from this, that the initial packet number remains
/// the same, thanks to the precise use of footprint_s in encrypt/decrypt.
val g_initial_packet_number: #i:index -> (s: state_s i) -> GTot QSpec.nat62

/// Invariant
/// ---------

val invariant_s: (#i:index) -> HS.mem -> state_s i -> Type0
let invariant (#i:index) (m: HS.mem) (s: state i) =
  let r = B.frameOf s in
  ST.is_eternal_region r /\
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
  GTot (pn: QSpec.uint62_t{
    U64.v pn >= g_initial_packet_number s
  })

let incrementable (#i: index) (s: state i) (h: HS.mem { invariant h s }) =
  U64.v (g_last_packet_number (B.deref h s) h) + 1 < pow2 62

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

val aead_alg_of_state (#i: G.erased index) (s: state (G.reveal i)): Stack aead_alg
  (requires (fun h0 -> invariant #(G.reveal i) h0 s))
  (ensures (fun h0 a h1 ->
    a == (G.reveal i).aead_alg /\
    h0 == h1))

val hash_alg_of_state (#i: G.erased index) (s: state (G.reveal i)): Stack hash_alg
  (requires (fun h0 -> invariant #(G.reveal i) h0 s))
  (ensures (fun h0 a h1 ->
    a == (G.reveal i).hash_alg /\
    h0 == h1))

val last_packet_number_of_state (#i: G.erased index) (s: state (G.reveal i)): Stack U64.t
  (requires fun h0 -> invariant h0 s)
  (ensures fun h0 ctr h1 ->
    ctr == g_last_packet_number (B.deref h0 s) h0 /\
    h0 == h1)

// JP: we could be defensive and allow callers to pass potentially unsupported
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
  initial_pn:u62 ->
  traffic_secret:B.buffer U8.t {
    B.length traffic_secret = Spec.Hash.Definitions.hash_length i.hash_alg
  } ->
  ST error_code
    (requires fun h0 ->
      // JP: we could require that ``dst`` point to NULL prior to calling
      // ``create`` (otherwise, it's a memory leak). Other modules don't enforce
      // this (see AEAD) so for now, let's make the caller's life easier and not
      // demand anything.
      ST.is_eternal_region r /\
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

          g_initial_packet_number (B.deref h1 s) == U64.v initial_pn
      | _ ->
          False))

// The index is passed at run-time.
val create_in: i:index -> create_in_st i

val encrypt: #i:G.erased index -> (
  let i = G.reveal i in
  s: state i ->
  dst: B.buffer U8.t ->
  dst_pn: B.pointer u62 ->
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
      (has_payload_length h ==> U64.v (payload_length h) == clen) /\
      B.length dst == U32.v (header_len h) + clen
    ))
    (ensures fun h0 r h1 ->
      match r with
      | Success ->
          // Memory & preservation
          B.(modifies (footprint_s h0 (deref h0 s) `loc_union` loc_buffer dst `loc_union` loc_buffer dst_pn)) h0 h1 /\
          invariant h1 s /\
          footprint_s h1 (B.deref h1 s) == footprint_s h0 (B.deref h0 s) /\ (
          // Functional correctness
          let s0 = g_traffic_secret (B.deref h0 s) in
          let open QUIC.Spec in
          let k = derive_secret i.hash_alg s0 label_key (Spec.Agile.AEAD.key_length i.aead_alg) in
          let iv = derive_secret i.hash_alg s0 label_iv 12 in
          let pne = derive_secret i.hash_alg s0 label_hp (ae_keysize i.aead_alg) in
          let plain = B.as_seq h0 plain in
          let packet: packet = B.as_seq h1 dst in
          let pn = g_last_packet_number (B.deref h0 s) h0 `U64.add` 1uL in
          B.deref h1 dst_pn == pn /\
          packet == encrypt i.aead_alg k iv pne (g_header h h0 pn) plain /\
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
  pn: u62;
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
  let s0 = g_traffic_secret (B.deref h0 s) in
  let k = QSpec.(derive_secret i.hash_alg s0 label_key (Spec.Agile.AEAD.key_length i.aead_alg)) in
  let iv = QSpec.(derive_secret i.hash_alg s0 label_iv 12) in
  let pne = QSpec.(derive_secret i.hash_alg s0 label_hp (ae_keysize i.aead_alg)) in
  let prev = g_last_packet_number (B.deref h0 s) h0 in
  invariant h1 s /\
  footprint_s h1 (B.deref h1 s) == footprint_s h0 (B.deref h0 s) /\
  begin
    let r = B.deref h1 dst in
    match res with
    | Success ->
      // prev is known to be >= g_initial_packet_number (see lemma invariant_packet_number)
      U64.v (g_last_packet_number (B.deref h1 s) h1) == max (U64.v prev) (U64.v r.pn) /\ (

      // Lengths
      r.header_len == header_len r.header /\
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
      match QSpec.decrypt i.aead_alg k iv pne (U64.v prev) (U8.v cid_len) (B.as_seq h0 packet) with
      | QSpec.Success h' plain' rem' ->
        h' == g_header r.header h1 r.pn /\
        plain' == plain /\
        rem' == rem
      | _ -> False
    ))
    | DecodeError ->
      QSpec.Failure? (QSpec.decrypt i.aead_alg k iv pne (U64.v prev) (U8.v cid_len) (B.as_seq h0 packet))
    | AuthenticationFailure ->
      QSpec.Failure? (QSpec.decrypt i.aead_alg k iv pne (U64.v prev) (U8.v cid_len) (B.as_seq h0 packet)) /\
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
