module Mem

/// * Sets a uniform Low* HyperStack-based memory model, gathering
///   abbreviations and top-level regions.
///
/// * Depends on Flags, as we do not to extract the global TLS region
///   and its contents (only ideal stuff).
///
/// Coding guidelines (aligned to EverCrypt)
/// - avoid eternal refs and buffers (fstar may deprecate them in lowstar)
/// - use LowStar.Buffer
/// - use monotonic buffers
///
/// - migrate from Bytes --> Spec-level sequences or Buffer [will take a while]
/// - enable divergence checking (try it out on a Everest feature branch?)
/// - use abbreviations wisely, e.g. only those to be defined in this file
///   (no clear consensus yet)
/// - use FStar.Integers (but avoid opening it because of v n etc... IntegersOps?)
///
/// - [create parent_region ...] may allocate a private sub-region,
///   unless its state is e.g. just a single transparent reference;
///   the caller usually tracks it using locations rather than regions.

open FStar.Error

include FStar.HyperStack
include FStar.HyperStack.ST

open LowStar.Buffer
open LowStar.BufferOps

module HS = FStar.HyperStack
module ST = FStar.HyperStack.ST

#set-options "--z3rlimit 40 --max_fuel 0  --max_ifuel 0"

inline_for_extraction noextract
let model = Model.Flags.model

// START quic-specific stuff that doesn't use the rest of the infrastructure
let rgn = r:erid{r =!= root}

type fresh_subregion child parent h0 h1 =
  fresh_region child h0 h1 /\ extends child parent

type subrgn p = r:rgn{parent r == p}

let quic_region: rgn = new_region root
type subq = r:subrgn quic_region
// END quic-specific stuff

/// Top-level disjointness
/// ----------------------
///
/// We define an infrastructure for allocating a set of regions that are know
/// automatically to be disjoint from each other.

#push-options "--max_ifuel 1"

(** r `rlist_disjoint` l holds if r is disjoint from all regions in l *)
val rlist_disjoint: subq -> list subq -> Type0
let rec rlist_disjoint r = function
  | [] -> True
  | r' :: l -> r `HS.disjoint` r' /\ rlist_disjoint r l

(** r_pairwise_disjoint l holds if all regions in l are pairwise disjoint *)
val r_pairwise_disjoint: list subq -> Type0
let rec r_pairwise_disjoint = function
  | [] -> True
  | r :: l -> rlist_disjoint r l /\ r_pairwise_disjoint l

(** r_fresh l h0 h1 holds when all regions in l are fresh between h0 and h1 *)
val r_fresh: list subq -> mem -> mem -> Type0
let rec r_fresh l h0 h1 =
  match l with
  | [] -> True
  | r :: l -> fresh_region r h0 h1 /\ r_fresh l h0 h1

val fresh_back (r:rgn) (h0 h1 h2:mem) : Lemma
  (requires fresh_region r h1 h2 /\ modifies_none h0 h1)
  (ensures  fresh_region r h0 h2)
//  [SMTPat (fresh_region r h1 h2); SMTPat (modifies_none h0 h1)]
let fresh_back r h0 h1 h2 = ()

#pop-options

#push-options "--max_fuel 1 --max_ifuel 1"

val r_fresh_back (l:list subq) (h0 h1 h2:mem) : Lemma
  (requires r_fresh l h1 h2 /\ modifies_none h0 h1)
  (ensures  r_fresh l h0 h2)
let rec r_fresh_back l h0 h1 h2 =
  match l with
  | [] -> ()
  | r :: l' -> r_fresh_back l' h0 h1 h2

val r_fresh_fwd (l:list subq) (h0 h1 h2:mem) : Lemma
  (requires r_fresh l h0 h1 /\ modifies_none h1 h2)
  (ensures  r_fresh l h0 h2)
let rec r_fresh_fwd l h0 h1 h2 =
  match l with
  | [] -> ()
  | r :: l' -> r_fresh_fwd l' h0 h1 h2

val r_fresh_disjoint (r:subq) (l:list subq) (h0 h1 h2:mem) : Lemma
  (requires r_fresh l h0 h1 /\ fresh_region r h1 h2)
  (ensures  rlist_disjoint r l)
let rec r_fresh_disjoint r l h0 h1 h2 =
  match l with
  | [] -> ()
  | r' :: l' ->
    lemma_extends_disjoint quic_region r r';
    r_fresh_disjoint r l' h0 h1 h2

val r_fresh_forall: l:list subq -> h0:mem -> h1:mem -> Lemma
  ((forall r.{:pattern fresh_region r h0 h1} List.Tot.mem r l ==> fresh_region r h0 h1) <==>
   r_fresh l h0 h1)
let rec r_fresh_forall l h0 h1 =
  match l with
  | [] -> ()
  | r :: l' -> r_fresh_forall l' h0 h1

(** Allocates n pairwise disjoint subregions of tls_region *)
val r_disjoint_alloc: n:nat -> ST (l:list subq)
  (requires fun h0 -> True)
  (ensures  fun h0 l h1 ->
    modifies_none h0 h1 /\
    r_fresh l h0 h1 /\
    List.Tot.length l == n /\
    r_pairwise_disjoint l)

let rec r_disjoint_alloc n =
  if n = 0 then []
  else
    begin
    let h0 = ST.get () in
    let l = r_disjoint_alloc (n-1) in
    let h1 = ST.get () in
    let r = new_region quic_region in
    let h2 = ST.get () in
    r_fresh_disjoint r l h0 h1 h2;
    r_fresh_fwd l h0 h1 h2;
    r :: l
    end

#pop-options

// We use region disjointness as a coarse grained way of framing invariants.
let top_regions: (l:list subq{List.Tot.length l == 5 /\ r_pairwise_disjoint l})
  = r_disjoint_alloc 5

let q_ae_region = List.Tot.index top_regions 0
let q_pne_region = List.Tot.index top_regions 1
let q_idx_region = List.Tot.index top_regions 2

#push-options "--z3rlimit 40 --max_fuel 5  --max_ifuel 0"

val top_regions_disjoint: i:nat{i < 5} -> j:nat{j < 5} -> Lemma
  (requires i <> j)
  (ensures  (List.Tot.index top_regions i) `HS.disjoint` (List.Tot.index top_regions j))
  [SMTPat (List.Tot.index top_regions i); SMTPat (List.Tot.index top_regions j)]
let top_regions_disjoint i j = ()

#pop-options

/// Loc-based disjointness
///
/// `loc_region_only` has GTot effect so we need to thunk these to avoid
/// problems with top-level masked effects

val loc_ae_region: unit -> GTot loc
let loc_ae_region _ = loc_region_only true q_ae_region

val loc_pne_region: unit -> GTot loc
let loc_pne_region _ = loc_region_only true q_pne_region

val loc_idx_region: unit -> GTot loc
let loc_idx_region _ = loc_region_only true q_idx_region

(** Sanity check: this works with fuel=0, ifuel=0 because of the lemma above *)
let _ = assert (all_disjoint
  [loc_ae_region ();
   loc_pne_region ();
   loc_idx_region ();
//   loc_psk_region ();
//   loc_crf_region ()
  ])
