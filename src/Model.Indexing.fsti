module Model.Indexing

(*
This module provides the functions that the QUIC
record layer security model expect to be provided
by the TLS handshake security model. In particular,
it assumes that the indexes contain the history of
the derivation of each key, including the implicit
authentication of algorithms to use.
*)

open Mem
include Model.Flags

module C = Spec.Agile.Cipher
module AE = Spec.Agile.AEAD
module HD = Spec.Hash.Definitions
module G = FStar.Ghost

let is_supported_hash = function
  | HD.SHA1 | HD.SHA2_256 | HD.SHA2_384 | HD.SHA2_512 -> true
  | _ -> false

let is_supported_aead = function
  | AE.AES128_GCM | AE.AES256_GCM | AE.CHACHA20_POLY1305 -> true
  | _ -> false

let is_supported_cipher = function
  | C.AES128 | C.AES256 | C.CHACHA20 -> true
  | _ -> false

type ha = a:HD.hash_alg{is_supported_hash a}
type ea = a:AE.alg{is_supported_aead a}
type ca = a:C.cipher_alg{is_supported_cipher a}

let cipher_of_aead (a:ea) =
  match a with
  | AE.AES128_GCM -> C.AES128
  | AE.AES256_GCM -> C.AES256
  | AE.CHACHA20_POLY1305 -> C.CHACHA20

val id: eqtype
inline_for_extraction
val is_honest: id -> bool

val id_ginfo: i:id -> GTot (ha * ea * ca)
val id_info: i:id{model} -> a:(ha * ea * ca){a == id_ginfo i}

val ae_id: eqtype
inline_for_extraction
val is_ae_honest: ae_id -> bool

val ae_id_ginfo: i:ae_id  -> GTot ea
val ae_id_info: i:ae_id{model} -> a:ea{a == ae_id_ginfo i}
val ae_id_ghash: i:ae_id  -> GTot ha
val ae_id_hash: i:ae_id{model} -> a:ha{a == ae_id_ghash i}

val pne_id: eqtype
inline_for_extraction
val is_pne_honest: pne_id -> bool

val pne_id_ginfo: i:pne_id -> GTot ca
val pne_id_info: i:pne_id{model} -> a:ca{a == pne_id_ginfo i}
val pne_id_ghash: i:pne_id -> GTot ha
val pne_id_hash: i:pne_id{model} -> a:ha{a == pne_id_ghash i}

