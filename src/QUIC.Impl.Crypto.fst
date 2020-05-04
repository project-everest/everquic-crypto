module QUIC.Impl.Crypto

module Cipher = EverCrypt.Cipher
module AEAD = EverCrypt.AEAD
module HKDF = EverCrypt.HKDF
module CTR = EverCrypt.CTR
module IB = LowStar.ImmutableBuffer
module U32 = FStar.UInt32

module Seq = QUIC.Secret.Seq
module SecretBuffer = QUIC.Secret.Buffer

module SHKDF = Spec.Agile.HKDF
module SHD = Spec.Hash.Definitions

friend QUIC.Spec.Crypto (* for the _l list constants *)
module Spec = QUIC.Spec.Crypto

open LowStar.BufferOps (* for the !* notation *)


/// Helpers & globals
/// -----------------

open QUIC.Impl.Lemmas

inline_for_extraction noextract
let u32_of_u8 = FStar.Int.Cast.uint8_to_uint32
inline_for_extraction noextract
let u64_of_u8 = FStar.Int.Cast.uint8_to_uint64
inline_for_extraction noextract
let u64_of_u32 = FStar.Int.Cast.uint32_to_uint64

#push-options "--warn_error -272"
let label_key = LowStar.ImmutableBuffer.igcmalloc_of_list HS.root label_key_l
let label_iv = LowStar.ImmutableBuffer.igcmalloc_of_list HS.root label_iv_l
let label_hp = LowStar.ImmutableBuffer.igcmalloc_of_list HS.root label_hp_l
let prefix = LowStar.ImmutableBuffer.igcmalloc_of_list HS.root prefix_l
#pop-options

/// Actual code
/// -----------

#push-options "--z3rlimit 100"
let derive_secret a dst dst_len secret label label_len =
  LowStar.ImmutableBuffer.recall prefix;
  LowStar.ImmutableBuffer.recall_contents prefix Spec.prefix;
  (**) let h0 = HST.get () in

  HST.push_frame ();
  (**) let h1 = HST.get () in

  let label_len32 = FStar.Int.Cast.uint8_to_uint32 label_len in
  let dst_len32 = FStar.Int.Cast.uint8_to_uint32 dst_len in
  let info_len = U32.(1ul +^ 1ul +^ 1ul +^ 11ul +^ label_len32 +^ 1ul) in
  let info = B.alloca 0uy info_len in

  // : best way to reason about this sort of code is to slice the buffer very thinly
  let info_z = B.sub info 0ul 1ul in
  let info_lb = B.sub info 1ul 1ul in
  let info_llen = B.sub info 2ul 1ul in
  let info_prefix = B.sub info 3ul 11ul in
  let info_label = B.sub info 14ul label_len32 in
  let info_z' = B.sub info (14ul `U32.add` label_len32) 1ul in
  (**) assert (14ul `U32.add` label_len32 `U32.add` 1ul = B.len info);
  (**) assert B.(all_disjoint [ loc_buffer info_z; loc_buffer info_lb; loc_buffer info_llen;
  (**)   loc_buffer info_prefix; loc_buffer info_label; loc_buffer info_z' ]);

  info_lb.(0ul) <- dst_len;
  info_llen.(0ul) <- U8.(label_len +^ 11uy);
  B.blit prefix 0ul info_prefix 0ul 11ul;
  B.blit label 0ul info_label 0ul label_len32;

  (**) let h2 = HST.get () in
  (**) assert (
  (**)   let z = Seq.create 1 0uy in
  (**)   let lb = Seq.create 1 dst_len in // len <= 255
  (**)   let llen = Seq.create 1 (U8.uint_to_t (11 + Seq.length (B.as_seq h0 label))) in
  (**)   let info = B.as_seq h2 info in
  (**)   B.as_seq h2 info_z `Seq.equal` z /\
  (**)   B.as_seq h2 info_lb `Seq.equal` lb /\
  (**)   B.as_seq h2 info_llen `Seq.equal` llen /\
  (**)   B.as_seq h2 info_prefix `Seq.equal` Spec.prefix /\
  (**)   B.as_seq h2 info_label `Seq.equal` (B.as_seq h0 label) /\
  (**)   B.as_seq h2 info_z' `Seq.equal` z
  (**) );
  (**) (
  (**)   let z = Seq.create 1 0uy in
  (**)   let lb = Seq.create 1 dst_len in // len <= 255
  (**)   let llen = Seq.create 1 (U8.uint_to_t (11 + Seq.length (B.as_seq h0 label))) in
  (**)   let info = B.as_seq h2 info in
  (**)   lemma_five_cuts info 1 2 3 14 (14 + U8.v label_len)
  (**)     z lb llen Spec.prefix (B.as_seq h0 label) z
  (**) );
  (**) hash_is_keysized_ a;
  let h25 = HST.get () in
  SecretBuffer.with_whole_buffer_hide_weak_modifies
    #unit
    info
    h25
    (B.loc_buffer secret `B.loc_union` B.loc_buffer dst)
    (B.loc_buffer dst)
    false
    (fun _ cont m ->
      SHD.hash_length a + B.length info + 1 + SHD.block_length a <= SHD.max_input_length a /\
      B.as_seq m dst == SHKDF.expand a (B.as_seq h25 secret) (Seq.seq_hide #Secret.U8 (B.as_seq h25 info)) (U32.v dst_len32)
    )
    (fun _ bs ->
      HKDF.hash_block_length_fits a;
      HKDF.expand a dst secret (Hacl.Hash.Definitions.hash_len a) bs info_len dst_len32
    );
  (**) let h3 = HST.get () in
  HST.pop_frame ();
  (**) let h4 = HST.get () in
  (**) B.modifies_fresh_frame_popped h0 h1 (B.loc_buffer dst) h3 h4;
  (**) assert (HST.equal_domains h0 h4)
#pop-options
