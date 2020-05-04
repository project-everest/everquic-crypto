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

unfold noextract
let hash_alg = Spec.Hash.Definitions.hash_alg

unfold noextract
let aead_alg = Spec.Agile.AEAD.alg

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
  (ensures (keysized i.hash_alg (S.length (g_traffic_secret s))))
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

val aead_alg_of_state (#i: G.erased index) (s: state (G.reveal i)): HST.Stack aead_alg
  (requires (fun h0 -> invariant #(G.reveal i) h0 s))
  (ensures (fun h0 a h1 ->
    a == (G.reveal i).aead_alg /\
    h0 == h1))

val hash_alg_of_state (#i: G.erased index) (s: state (G.reveal i)): HST.Stack hash_alg
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
