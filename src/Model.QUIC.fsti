module Model.QUIC

module HS = FStar.HyperStack
module I = Model.Indexing
module U32 = FStar.UInt32
module U64 = FStar.UInt64
module U128 = FStar.UInt128
module M = LowStar.Modifies

module Spec = QUIC.Spec
module QH = QUIC.Spec.Header
module AE = Model.AEAD
module SAE = Spec.Agile.AEAD
module PNE = Model.PNE
module SPNE = Spec.Agile.Cipher
module BF = LowParse.BitFields
module U62 = QUIC.UInt62
module Secret = QUIC.Secret.Int

open FStar.UInt32
open Mem

type id = AE.id * PNE.id

let safePNE (j:PNE.id) = PNE.is_safe j
let safeAE (k:AE.id) = AE.is_safe k
let safe (i:id) = safeAE (fst i) && safePNE (snd i)
let safe_id = i:id{safe i}
let unsafe (i:id) = not (safeAE (fst i) || safePNE (snd i))
let unsafe_id = i:id{unsafe i}

/// Package for QUIC plaintexts
/// (i.e. the payload of QUIC packets)
/// This would be implemented as a serializable list of frames
/// (using EverParse refined lists)

type qplain_len = n:nat{3 <= n /\ n < Spec.max_plain_length}
let pnl = PNE.pne_plain_length

// N.B. this is QUIC-specific so not index type parametric,
// unlike the universal AEAD plain package in Model.AEAD
inline_for_extraction noeq
type qplain_pkg =
  | PlainPkg:
    plain: (i:id -> l:qplain_len -> eqtype) ->
    as_bytes: (#i:id -> #l:qplain_len -> plain i l -> GTot (b:Spec.pbytes{Seq.length b == l})) ->
    repr: (#i:unsafe_id -> #l:qplain_len -> p:plain i l -> Tot (b:Spec.pbytes{Seq.length b == l /\ b == as_bytes p})) ->
    mk: (i:unsafe_id -> l:qplain_len -> p:Spec.pbytes -> p':plain i l { as_bytes #i #l p' == p }) ->
    qplain_pkg

(* TODO move to impl
let pne_plain (j:PNE.id) (l:pnl) : eqtype =
  lbytes l & PNE.length_bits l

let pne_as_bytes (j:PNE.id) (l:pnl) (n:pne_plain j l)
  : GTot (lbytes l & PNE.length_bits l) = n

let pne_repr (j:PNE.unsafe_id) (l:pnl) (n:pne_plain j l) :
  Tot (b:(lbytes l & PNE.length_bits l){b == pne_as_bytes j l n}) = n

let pne_plain_pkg = PNE.PNEPlainPkg pne_plain pne_as_bytes pne_repr

type plainlen = l:nat{l + v AEAD.taglen <= pow2 32 - 1}
type pnplainlen = l:nat{l + v AEAD.taglen <= pow2 32 - 1 /\ l + v AEAD.taglen >= samplelen + 4}

type quic_protect (k:id) (l:pnplainlen) =
  lbytes (l + v AEAD.taglen)

type quic_packet (k:id) (hl:headerlen) (l:pnplainlen{hl + l + v AEAD.taglen <= pow2 32 - 1}) =
  quic_header k hl * quic_protect k l

type cipher (i:id) (l:plainlen) = lbytes (l + v AEAD.taglen)

val plain: i:AEAD.id -> l:plainlen -> t:Type0{hasEq t}

val plain_as_bytes : i:AEAD.id -> l:plainlen -> p:plain i l -> GTot (lbytes l)

val mk_plain: i:AEAD.id -> l:plainlen -> b:lbytes l -> p:plain i l{~(AEAD.is_safe i) ==> plain_as_bytes i l p == b}

val plain_repr : i:AEAD.id{~(AEAD.is_safe i)} -> l:plainlen -> p:plain i l -> b:lbytes l{b == plain_as_bytes i l p}

type qiv (k:id) = AEAD.iv (I.ae_id_ginfo (fst k))

val nonce (i:AEAD.id) : (t:Type0{hasEq t})

val nonce_as_bytes (i:AEAD.id) (n:nonce i) : GTot (AEAD.iv (I.ae_id_ginfo i))

val nonce_repr (i:AEAD.id{not (AEAD.is_safe i)}) (n:nonce i) :
  Tot (b:AEAD.iv (I.ae_id_ginfo i){b == nonce_as_bytes i n})

let aead_nonce_pkg : AEAD.nonce_pkg AEAD.id AEAD.is_safe I.ae_id_ginfo =
  AEAD.NoncePkg nonce nonce_as_bytes nonce_repr

type sample = PNE.sample

type epn (nl:pnlen) = lbytes nl

type rpn = n:U64.t{U64.v n <= max_ctr}

let rpn_of_nat (j:nat{j<= max_ctr}) : rpn =
  U64.uint_to_t j

type npn (j:PNE.id) (nl:pnlen) = lbytes nl
**)

(*
//get the first byte of the (unprotected) header + the pn = what needs to be protected by pne
val pne_plain_of_header_pn (#k:id) (#hl:headerlen) (hd:quic_header k hl) (#nl:pnlen) (n:npn (snd k) nl) :  pne_plain (snd k) (nl+1)

//reconstruct the unprotected header (using the protected header), and the pn, from the protected header and pn
val header_pn_of_pne_plain (#k:id) (#hl:headerlen) (ph:quic_header k hl) (#ll:PNE.pne_plainlen) (pp:pne_plain (snd k) ll) : quic_header k hl * npn (snd k) (ll-1)

//val pheader_epn_of_pne_cipher (#k:quicid) (#hl:headerlen) (hd:quic_header k hl) (l:PNE.pne_plainlen) (c:PNE.pne_cipher l) : quic_header k hl * (nl:pnlen & epn nl)

//get the protected first byte from the (protected) header + the epn = a cipher for pne
val pne_cipher_of_pheader_epn (#k:id) (#hl:headerlen) (ph:quic_header k hl) (#nl:pnlen) (ne:epn nl) :
  c:PNE.pne_cipher (nl + 1)

//get the pne ciphertext assuming the largest possible pn length (ie 4)
val pne_cipherpad_of_pheader_quicprotect (#k:id) (#hl:headerlen) (ph:quic_header k hl) (#nll:pnplainlen) (qp:quic_protect k nll) :
  c:PNE.pne_cipherpad

val npn_encode : (j:PNE.id) -> (r:rpn) -> (nl:pnlen) -> (n:npn j nl)

val npn_decode : (#j:PNE.id) -> (#nl:pnlen) -> (n:npn j nl) -> (expected_pn:rpn) -> rpn

val create_nonce : #i:id -> #alg:I.ea{alg == I.ae_id_ginfo (fst i)} ->
  iv: AEAD.iv alg -> r:rpn -> Tot (nonce (fst i))
*)

noeq type info = {
  region: r:subq{r `HS.disjoint` q_ae_region};
  plain_pkg: qplain_pkg;
}

let max_ctr = pow2 62 - 1
type epn (nl:pnl) = Spec.lbytes nl
type pn = n:nat{n <= max_ctr}
type rpn = n:U64.t{U64.v n < max_ctr}
let rpn_of_nat (j:nat{j < max_ctr}) : rpn = U64.uint_to_t j

val stream_writer: (k:id) -> Type u#1
val stream_reader: #k:id -> w:stream_writer k -> Type u#1
val writer_info: #k:id -> w:stream_writer k -> info
val reader_info: #k:id -> #w:stream_writer k -> r:stream_reader w -> i:info{i == writer_info w}

val writer_ae_info: #k:id -> w:stream_writer k -> a:AEAD.info (fst k)
val reader_ae_info: #k:id -> #w:stream_writer k -> r:stream_reader w -> a:AEAD.info (fst k)
val writer_pne_info: #k:id -> w:stream_writer k -> a:PNE.info (snd k){a.PNE.calg == Spec.Agile.AEAD.cipher_alg_of_supported_alg (writer_ae_info w).AEAD.alg /\ a.PNE.halg == (writer_ae_info w).AEAD.halg}
val reader_pne_info: #k:id -> #w:stream_writer k -> r:stream_reader w -> a:PNE.info (snd k){a.PNE.calg == Spec.Agile.AEAD.cipher_alg_of_supported_alg (reader_ae_info r).AEAD.alg /\ a.PNE.halg == (reader_ae_info r).AEAD.halg}

val writer_aead_state : (#k:id) -> (w:stream_writer k) ->
  aw:AEAD.aead_writer (fst k)
val reader_aead_state : #k:id -> #w:stream_writer k -> r:stream_reader w ->
  ar:AEAD.aead_reader (writer_aead_state w)
val writer_pne_state : #k:id -> w:stream_writer k -> PNE.pne_state (writer_pne_info w)
val reader_pne_state : #k:id -> #w:stream_writer k -> r:stream_reader w -> PNE.pne_state (reader_pne_info r)

type key_t #i (w:stream_writer i) =
  Spec.lbytes (SAE.key_length (writer_ae_info w).AEAD.alg) &
  Spec.lbytes (PNE.key_len (writer_pne_info w))

let writer_leak (#k:unsafe_id) (w:stream_writer k) : key_t w =
  Model.Helpers.reveal #(SAE.key_length (writer_ae_info w).AEAD.alg) (AEAD.wkey (writer_aead_state w)),
  Model.Helpers.reveal #(PNE.key_len (writer_pne_info w)) (PNE.key (writer_pne_state w))

let reader_leak (#k:unsafe_id) (#w:stream_writer k) (r:stream_reader w) : key_t w = writer_leak w

val invariant: #k:id -> w:stream_writer k -> h:mem ->
  t:Type0{t ==> AEAD.winvariant (writer_aead_state w) h}
val rinvariant: #k:id -> #w:stream_writer k -> r:stream_reader w -> h:mem ->
  t:Type0{t ==> invariant w h}

val writer_offset: #k:id -> w:stream_writer k -> pn
val reader_offset: #k:id -> #w:stream_writer k -> stream_reader w -> pn

val wctrT: #k:id -> w:stream_writer k -> h:mem{invariant w h} -> 
  GTot (n:nat{n >= writer_offset w /\ n <= max_ctr})
  
val wctr: #k:id -> w:stream_writer k -> ST (n:nat{n >= writer_offset w /\ n <= max_ctr})
  (requires fun h0 -> invariant w h0)
  (ensures fun h0 c h1 -> h0 == h1 /\ c = wctrT w h1)

type qiv (k:id) = Spec.lbytes 12 // SAE.iv (I.ae_id_ginfo (fst k))
val writer_static_iv: #k:id -> w:stream_writer k -> qiv k
val reader_static_iv: #k:id -> #w:stream_writer k -> r:stream_reader w ->
  iv:qiv k{iv == writer_static_iv w}

val expected_pnT: #k:id -> #w:stream_writer k -> r:stream_reader w -> h:mem{rinvariant r h} ->
  GTot (n:nat{n >= writer_offset w /\ n < max_ctr})
  
val expected_pn: #k:id -> #w:stream_writer k -> r:stream_reader w ->
  ST (n:nat{n >= writer_offset w /\ n <= max_ctr})
  (requires fun h0 -> rinvariant r h0)
  (ensures fun h0 c h1 -> h0 == h1 /\
    (c == expected_pnT #k #w r h0))

let wincrementable (#k:id) (w:stream_writer k) (h:mem{invariant w h}) =
  wctrT w h < max_ctr

val footprint: #k:id -> w:stream_writer k -> GTot M.loc
val rfootprint: #k:id -> #w:stream_writer k -> r:stream_reader w -> GTot M.loc

val frame_invariant: #k:id -> w:stream_writer k -> h0:mem -> ri:M.loc -> h1:mem ->
  Lemma
  (requires
    (invariant w h0 /\
    M.modifies ri h0 h1 /\
    M.loc_disjoint ri (footprint w)))
  (ensures invariant w h1)

val rframe_invariant: #k:id -> #w:stream_writer k -> r:stream_reader w ->
  h0:mem -> ri:M.loc -> h1:mem ->
  Lemma
  (requires
    (rinvariant r h0 /\
    M.modifies ri h0 h1 /\
    M.loc_disjoint ri (rfootprint r)))
  (ensures rinvariant r h1)

val wframe_log: #k:id{AEAD.is_safe (fst k)} -> w:stream_writer k -> l:Seq.seq (AEAD.entry (fst k) (AEAD.wgetinfo (writer_aead_state w))) ->
  h0:mem -> ri:M.loc -> h1:mem ->
  Lemma
  (requires
    invariant w h0 /\
    AEAD.wlog (writer_aead_state w) h0 == l /\
    M.modifies ri h0 h1 /\
    M.loc_disjoint ri (footprint w))
  (ensures invariant w h1 ==> AEAD.wlog (writer_aead_state w) h1 == l)

val rframe_log: #k:id{AEAD.is_safe (fst k)} -> #w:stream_writer k -> r:stream_reader w -> l:Seq.seq (AEAD.entry (fst k) (AEAD.rgetinfo (reader_aead_state r))) ->
  h0:mem -> ri:M.loc -> h1:mem ->
  Lemma
  (requires
    invariant w h0 /\
    AEAD.rlog (reader_aead_state r) h0 == l /\
    M.modifies ri h0 h1 /\
    M.loc_disjoint ri (rfootprint r))
  (ensures invariant w h1 ==> AEAD.rlog (reader_aead_state r) h1 == l)

val wframe_pnlog: #k:id{PNE.is_safe (snd k)} -> w:stream_writer k -> l:Seq.seq (PNE.entry (writer_pne_info w)) ->
  h0:mem -> ri:M.loc -> h1:mem ->
  Lemma
  (requires
    PNE.table (writer_pne_state w) h0 == l /\
    M.modifies ri h0 h1 /\
    M.loc_disjoint ri (footprint w))
  (ensures PNE.table (writer_pne_state w) h1 == l)

val rframe_pnlog: #k:id{PNE.is_safe (snd k)} ->  #w:stream_writer k -> r:stream_reader w -> l:Seq.seq (PNE.entry (reader_pne_info r)) ->
  h0:mem -> ri:M.loc -> h1:mem ->
  Lemma
  (requires
    PNE.table (reader_pne_state r) h0 == l /\
    M.modifies ri h0 h1 /\
    M.loc_disjoint ri (rfootprint r))
  (ensures PNE.table (reader_pne_state r) h1 == l)

val g_last_packet_number: #k:id -> #w: stream_writer k -> r:stream_reader w -> GTot (p:pn { p >= writer_offset w })

val create: k:id -> u:info ->
  u1:AEAD.info (fst k) -> u2:PNE.info (snd k) -> init: pn ->
  ST (stream_writer k)
  (requires fun h0 -> u2.PNE.calg ==
    Spec.Agile.AEAD.cipher_alg_of_supported_alg u1.AEAD.alg /\
    u2.PNE.halg == u1.AEAD.halg)
  (ensures fun h0 w h1 ->
    invariant w h1 /\
    modifies_none h0 h1 /\
    writer_offset w == init /\
    wctrT w h1 == writer_offset w /\
    writer_ae_info w == u1 /\
    writer_pne_info w == u2 /\
    writer_info w == u /\
    (safe k ==>
      (AEAD.wlog (writer_aead_state w) h1 == Seq.empty /\
      PNE.table (writer_pne_state w) h1 == Seq.empty
    ))
  )

val coerce: k:unsafe_id -> u:info ->
  u1:AEAD.info (fst k) -> u2:PNE.info (snd k) ->  
  init: pn -> ts:AEAD.traffic_secret u1.AEAD.halg ->
  ST (stream_writer k)
  (requires fun h0 -> u2.PNE.calg ==
    Spec.Agile.AEAD.cipher_alg_of_supported_alg u1.AEAD.alg /\
    u2.PNE.halg == u1.AEAD.halg)
  (ensures fun h0 w h1 ->
    let (k1, k2) = writer_leak w in
    invariant w h1 /\
    modifies_none h0 h1 /\
    writer_offset w == init /\
    wctrT w h1 == writer_offset w /\
    writer_ae_info w == u1 /\
    writer_pne_info w == u2 /\
    writer_info w == u /\
    Model.Helpers.hide (writer_static_iv w) ==
      Spec.derive_secret u1.AEAD.halg ts
        Spec.label_iv 12 /\
    Model.Helpers.hide k1 == Spec.derive_secret u1.AEAD.halg ts
        Spec.label_key (SAE.key_length u1.AEAD.alg) /\
    Model.Helpers.hide k2 == QUIC.Spec.derive_secret u2.PNE.halg ts
        QUIC.Spec.label_hp (PNE.key_len u2)
  )

val createReader: parent:rgn -> #k:id -> w:stream_writer k ->
  ST (stream_reader w)
  (requires fun h0 -> invariant w h0)
  (ensures fun h0 r h1 ->
    invariant w h1 /\
    rinvariant r h1 /\
    modifies_none h0 h1 /\
    expected_pnT r h1 == 0)

#reset-options "--z3rlimit 50 --fuel 1"

let _ = assert_norm(Spec.max_plain_length < pow2 32)
let _ = assert_norm(pow2 32 < pow2 64)

(*
      let (ne,c) = split #k #(nl+l) nec nl in
      let rpn = rpn_of_nat (wctrT w h0) in
      let npn = npn_encode j rpn nl in
      let alg = ((AEAD.wgetinfo aw).AEAD.alg) in
      let nce:AEAD.nonce (AEAD.wgetinfo aw) = create_nonce #k #alg (writer_iv w) rpn in
      let ad:AEAD.adata = Bytes.append (bytes_of_quic_header hd) npn in
      let s:PNE.sample = sample_quic_protect nec in
      let nn = pne_plain_of_header_pn hd npn in
      let cc = pne_cipher_of_pheader_epn ph ne in
      AEAD.wlog aw h1 ==
        Seq.snoc
          (AEAD.wlog aw h0)
          (AEAD.Entry #i #(AEAD.wgetinfo aw) nce ad #l p c) /\
           PNE.table ps h1 ==
              Seq.snoc
                (PNE.table ps h0)
                (PNE.Entry #j #pne_plain_pkg s #(nl+1) nn cc))
*)

#push-options "--fuel 2 --z3rlimit 30"
val encrypt
  (#k:id)
  (w:stream_writer k)
  (h:Spec.header)
  (#l:qplain_len)
  (p:(writer_info w).plain_pkg.plain k l)
  : ST Spec.packet
  (requires fun h0 ->
    invariant w h0 /\
    wincrementable w h0 /\
    (if Spec.is_retry h then l = 0
    else (
      Spec.has_payload_length h ==>
        Secret.v (Spec.payload_length h) == l
	  + Spec.Agile.AEAD.tag_length (writer_ae_info w).AEAD.alg))
  )
  (ensures fun h0 c h1 ->
    let (i,j) = k in
    let aw = writer_aead_state w in
    let ps = writer_pne_state w in
    M.modifies (footprint w) h0 h1 /\
    invariant w h1 /\
    wctrT w h1 == wctrT w h0 + 1 /\
    (safe k ==> True) /\
    (unsafe k ==>
      (let ea = (writer_ae_info w).AE.alg in
      let k1, k2 = writer_leak w in
      let plain : Spec.pbytes = (writer_info w).plain_pkg.repr p in
      c == Spec.encrypt ea (Model.Helpers.hide k1) (Model.Helpers.hide (writer_static_iv w)) (Model.Helpers.hide k2) h
	(plain <: Spec.pbytes' (Spec.is_retry h)))
    ))

noeq type model_result (#k:id) (#w:stream_writer k) (r:stream_reader w) =
| M_Success:
  h: Spec.header{not (Spec.is_retry h)} ->
//  nl: PNE.pne_plain_length ->
//  npn: PNE.pne_plain (reader_pne_info r) nl ->
  l: qplain_len ->
  p: (reader_info r).plain_pkg.plain k l ->
  remainder: Spec.bytes ->
  model_result r
| M_Failure

let max (a b:nat) =
//  let open FStar.UInt64 in
  if a > b then a else b

module S = FStar.Seq
module BF = LowParse.BitFields
module U8 = FStar.UInt8

let get_sample (p:Spec.packet) cid_len
  : GTot (option (Spec.lbytes 16)) =
  let open QUIC.Spec in
  let open QUIC.Spec.Header in
  if S.length p = 0 then None
  else
    let f = Seq.index p 0 in
    let is_short = (BF.get_bitfield (U8.v f) 7 8 = 0) in
    let is_retry = not is_short && BF.get_bitfield (U8.v f) 4 6 = 3 in
    if is_retry then None
    else
      match QUIC.Spec.Header.Parse.putative_pn_offset cid_len p with
      | None -> None
      | Some pn_offset ->
        let sample_offset = pn_offset + 4 in
        if sample_offset + 16 > S.length p then None
        else Some (S.slice p sample_offset (sample_offset+16))

val decrypt
  (#k:id)
  (#w:stream_writer k)
  (r:stream_reader w)
  (cid_len:nat)
  (packet: Spec.packet)
  : ST (model_result r)
  (requires fun h0 ->
    rinvariant r h0 /\
    cid_len <= 20
  )
  (ensures fun h0 res h1 ->
    let (i,j) = k in
    let ar = reader_aead_state r in
    let aw = writer_aead_state w in
    let pr = reader_pne_state r in
    let pw = writer_pne_state w in
    let expected = expected_pnT r h0 in
    rinvariant r h1 /\
    M.modifies (rfootprint r) h0 h1 /\
    (match res with
    | M_Failure -> expected_pnT r h1 == expected
    | M_Success h _ _ _ ->
      expected_pnT r h1 == max (UInt64.v (Secret.reveal (Spec.packet_number h))) expected) /\
    (safe k ==> (
      match get_sample packet cid_len with
      | _ -> True
    )) /\
    (unsafe k ==>
      (let ea = (writer_ae_info w).AE.alg in
      let k1, k2 = reader_leak r in
      match Spec.decrypt ea (Model.Helpers.hide k1) (Model.Helpers.hide (writer_static_iv w)) (Model.Helpers.hide k2)
	    expected cid_len packet,
	    res
      with
      | Spec.Failure, M_Failure -> True
      | Spec.Success h plain rem, M_Success h' l p remainder ->
	  h == h' /\ rem == remainder /\
	  (reader_info r).plain_pkg.repr p == plain
      | _ -> False)
    )
  )

(*
      (let (ph,nec) = qp in
      let s = sample_quic_protect nec in
      let cp = pne_cipherpad_of_pheader_quicprotect ph nec in
      match PNE.entry_for_sample_cipherpad s cp ps h0 with
        | None -> None? res
        | Some (PNE.Entry  _ #ll n cc) ->
          let nl:pnlen = ll - 1 in
          let (hd,npn) = header_pn_of_pne_plain #k #hl ph #ll n in
	  let rpn = npn_decode #j #nl npn (expected_pnT r h0) in
          let alg = ((AEAD.rgetinfo ar).AEAD.alg) in
          let n = create_nonce #k #alg (reader_iv r) rpn in
          let ad:AEAD.adata = Bytes.append (bytes_of_quic_header hd) npn in
          match AEAD.wentry_for_nonce aw n h0 with
	    | None -> None? res
	    | Some (AEAD.Entry _  ad' #l' p' c')  ->
	      if ad' = ad && l' = nll - nl && snd (split nec nl) = c' then
	        (res = Some (|l',p'|) /\
                  (if U64.v rpn >= U64.v (expected_pnT r h0) && U64.v rpn < max_ctr then
                    expected_pnT r h1 = rpn_of_nat (U64.v rpn + 1)
                  else
                    expected_pnT r h1 = expected_pnT r h0))
	        else None? res
      )
*)


 (*   (None? res ==> pnlog r h1 == pnlog r h0) /\
    (Flag.safeId i ==> (
      let lg = wlog w h0 in
      match (Seq.find_l (epn_filter i j nl ne) lg) with
        | None -> res = None
        | Some (Entry _ rpn ad' #l' p _ c') ->
	  let npn = npn_encode j rpn nl in
          if (ad' = ad && l' = l && c' = c then
              (res = Some p /\ pnlog r h1 == Seq.snoc (pnlog r h0) rpn)
          else
            res = None)))
*)
(*
  (Flag.safePNE j ==>
    match entry_for_ne r ne h0 with
    | None -> None? res
    | Some (Entry nl' rpn' ad' l' p' _ c') ->
      if c' = c then
        let npn =
      else None? res
  | Entry:
    nl:pnlen ->
    pn:rpn ->
    ad:AEAD.adata ->
    #l:plainlen ->
    p:plain i l ->
    ne:epn nl ->
    c:cipher i l ->
    stream_entry i j
*)
(*)
    (Flag.safePNE j ==>
      let s = PNE.sample_cipher c in
      match PNE.entry_for_sample s (pne_state r) h0 with
      | None -> None? res
      | Some (Entry _ nl' ne' npn) ->
        if nl = nl' && ne = ne' then
	  let rpn = npn_decode #nl npn (highest_pn_or_zero r h0) in
	  let n = encode_nonce rpn nl static_iv in
	  match AEAD.entry_for_nonce (aead_state r) n h0 with
	  | None -> None? res
	  | Some (_, ad', l', p', c')  ->
	    if ad' = empty_bytes && l' = l && c' = c then
	      res = Some p'
	    else None? res
	else None? res

(*      let npn = 'find nl ne in pnetable' in
      let rpn = 'decode npn maxpn' in
      match 'find rpn in enctable' with
        ne' -> ne' =? ne

      let rpn = 'find nl ne in enctable' in
        rpn =? decode (encode rpn nl) maxpn
*)

(*
N(nl, rpn) = encode(nl)<<62 + rpn

N(nl1, rpn1) = N(nl2, rpn2) ==> nl1 = nl2 /\ rpn1 = rpn2

decode(npn, nl, highest_pn) = (highest_pn & ~nl) | npn

y-2^(8*len(x)-1) < decode x y < y + 2^(8*len(x)-1)
