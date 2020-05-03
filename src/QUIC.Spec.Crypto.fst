module QUIC.Spec.Crypto

module U8 = FStar.UInt8
module Seq = QUIC.Secret.Seq
module HKDF = Spec.Agile.HKDF

inline_for_extraction
noextract
let prefix_l: List.Tot.llist U8.t 11 =
  // JP: "tls13 quic "
  [@inline_let]
  let l = [0x74uy; 0x6cuy; 0x73uy; 0x31uy; 0x33uy;
           0x20uy; 0x71uy; 0x75uy; 0x69uy; 0x63uy; 0x20uy] in
  assert_norm (List.Tot.length l == 11);
  l

noextract
let prefix: lbytes 11 =
  Seq.seq_of_list prefix_l

#push-options "--z3rlimit 10"
let lemma_hash_lengths (a:ha)
  : Lemma (HD.hash_length a <= 64 /\ HD.word_length a <= 8 /\
    HD.block_length a <= 128 /\ HD.max_input_length a >= pow2 61 - 1)
  =
  assert_norm(pow2 61 < pow2 125)
#pop-options

inline_for_extraction
noextract
let label_key_l: List.Tot.llist U8.t 3 =
  [@inline_let]
  let l = [ 0x6buy; 0x65uy; 0x79uy ] in
  assert_norm (List.Tot.length l = 3);
  l

let label_key =
  Seq.seq_of_list label_key_l

inline_for_extraction
noextract
let label_iv_l: List.Tot.llist U8.t 2 =
  [@inline_let]
  let l = [ 0x69uy; 0x76uy ] in
  assert_norm (List.Tot.length l = 2);
  l

let label_iv =
  Seq.seq_of_list label_iv_l

inline_for_extraction
noextract
let label_hp_l: List.Tot.llist U8.t 2 =
  [@inline_let]
  let l = [ 0x68uy; 0x70uy ] in
  assert_norm (List.Tot.length l = 2);
  l

let label_hp =
  Seq.seq_of_list label_hp_l

let derive_secret a prk label len =
  let open Seq in
  let z = Seq.create 1 0uy in
  let lb = Seq.create 1 (U8.uint_to_t len) in // len <= 255
  let llen = Seq.create 1 (U8.uint_to_t (11 + Seq.length label)) in
  let info = z @| lb @| llen @| prefix @| label @| z in
  lemma_hash_lengths a;
  assert_norm(452 < pow2 61);
  HKDF.expand a prk (Seq.seq_hide info) len
