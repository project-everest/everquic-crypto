module Model.QUIC.Spec

module AEAD = Spec.Agile.AEAD
module U32 = FStar.UInt32
module U64 = FStar.UInt64
module S = FStar.Seq

// This is an executable version of Spec.QUIC in Tot
include QUIC.Spec


val encrypt:
  a: ea ->
  k: lbytes (AEAD.key_length a) ->
  static_iv: lbytes 12 ->
  hpk: lbytes (ae_keysize a) ->
  h: header ->
  plain: pbytes' (is_retry h) { has_payload_length h ==> U64.v (payload_length h) == S.length plain + AEAD.tag_length a } ->
  Pure packet
  (requires True)
  (ensures fun p -> p == QUIC.Spec.encrypt a k static_iv hpk h plain)

val decrypt:
  a: ea ->
  k: lbytes (AEAD.key_length a) ->
  static_iv: lbytes 12 ->
  hpk: lbytes (ae_keysize a) ->
  last: nat{last+1 < pow2 62} ->
  cid_len: nat { cid_len <= 20 } ->
  packet: packet ->
  Pure (r: result {
    match r with
    | Failure -> True
    | Success h _ rem ->
      is_valid_header h cid_len last /\
      S.length rem <= Seq.length packet /\
      rem `S.equal` S.slice packet (S.length packet - S.length rem) (S.length packet)
  })
  (requires True)
  (ensures fun r -> r == QUIC.Spec.decrypt a k static_iv hpk last cid_len packet)
