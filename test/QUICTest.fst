module QUICTest
module Q = QUIC.Impl
module QS = QUIC.Spec
module B = LowStar.Buffer
module U32 = FStar.UInt32
module U8 = FStar.UInt8
module HST = FStar.HyperStack.ST
module HS = FStar.HyperStack
module L = FStar.List.Tot
module Secret = QUIC.Secret.Int
module PN = QUIC.Spec.PacketNumber.Base
module Seq = QUIC.Secret.Seq

(* declassification for post tests *)
module ADMITDeclassify = Lib.RawIntTypes

let idx = {
  Q.hash_alg = Spec.Hash.Definitions.SHA2_256;
  Q.aead_alg = Spec.Agile.AEAD.CHACHA20_POLY1305;
}

inline_for_extraction
noextract
let _traffic_secret: list Secret.uint8 = [
  Secret.hide #Secret.U8 0x48uy; Secret.hide #Secret.U8 0xc4uy; Secret.hide #Secret.U8 0x30uy; Secret.hide #Secret.U8 0x9buy; Secret.hide #Secret.U8 0x5fuy; Secret.hide #Secret.U8 0x27uy; Secret.hide #Secret.U8 0x52uy; Secret.hide #Secret.U8 0xe8uy;
  Secret.hide #Secret.U8 0x12uy; Secret.hide #Secret.U8 0x7buy; Secret.hide #Secret.U8 0x1uy;  Secret.hide #Secret.U8 0x66uy; Secret.hide #Secret.U8 0x5uy;  Secret.hide #Secret.U8 0x5auy; Secret.hide #Secret.U8 0x9auy; Secret.hide #Secret.U8 0x56uy;
  Secret.hide #Secret.U8 0xe5uy; Secret.hide #Secret.U8 0xf9uy; Secret.hide #Secret.U8 0x6uy;  Secret.hide #Secret.U8 0x31uy; Secret.hide #Secret.U8 0xe0uy; Secret.hide #Secret.U8 0x84uy; Secret.hide #Secret.U8 0x85uy; Secret.hide #Secret.U8 0xe0uy;
  Secret.hide #Secret.U8 0xf8uy; Secret.hide #Secret.U8 0x9euy; Secret.hide #Secret.U8 0x9cuy; Secret.hide #Secret.U8 0xecuy; Secret.hide #Secret.U8 0x4auy; Secret.hide #Secret.U8 0xdeuy; Secret.hide #Secret.U8 0xb6uy; Secret.hide #Secret.U8 0x50uy;
]

inline_for_extraction
noextract
let traffic_secret_length = norm [delta; zeta; iota; primops] (L.length _traffic_secret)

let traffic_secret_length_correct : squash (traffic_secret_length == L.length _traffic_secret) =
  assert_norm (traffic_secret_length == L.length _traffic_secret)

inline_for_extraction
noextract
let _plain: list Secret.uint8 = [
  Secret.hide #Secret.U8 0uy;Secret.hide #Secret.U8 1uy;Secret.hide #Secret.U8 2uy;Secret.hide #Secret.U8 3uy;Secret.hide #Secret.U8 4uy;Secret.hide #Secret.U8 5uy;Secret.hide #Secret.U8 6uy;Secret.hide #Secret.U8 7uy;Secret.hide #Secret.U8 8uy;Secret.hide #Secret.U8 9uy;
]

inline_for_extraction
noextract
let plain_length = norm [delta; zeta; iota; primops] (L.length _plain)

let plain_length_correct : squash (plain_length == L.length _plain) =
  assert_norm (plain_length == L.length _plain)

module E = EverCrypt.Error
module PF = LowStar.Printf

let is_success_body (e: E.error_code) : HST.Stack bool
  (requires (fun _ -> True))
  (ensures (fun h r h' -> h == h' /\ r == (E.Success? e)))
= match e with
  | E.UnsupportedAlgorithm ->
    PF.print_string "unsupported algorithm\n";
    false
  | E.InvalidKey ->
    PF.print_string "invalid key\n";
    false
  | E.AuthenticationFailure ->
    PF.print_string "auth failure\n";
    false
  | E.InvalidIVLength ->
    PF.print_string "invalid IV length\n";
    false
  | E.DecodeError ->
    PF.print_string "decode error\n";
    false
  | E.Success ->
    PF.print_string "success\n";
    true

inline_for_extraction
noextract
let is_success (s: string) (e: E.error_code) : HST.Stack bool
  (requires (fun _ -> True))
  (ensures (fun h r h' -> h == h' /\ r == (E.Success? e)))
= PF.print_string "Performing ";
  PF.print_string s;
  PF.print_string ": ";
  is_success_body e

let check_is_true_body
  (e: bool)
: HST.Stack bool
  (requires (fun _ -> True))
  (ensures (fun h r h' -> h == h' /\ r == e))
= if e then PF.print_string "OK\n" else PF.print_string "KO\n";
  e

inline_for_extraction
noextract
let check_is_true
  (s: string)
  (e: bool)
: HST.Stack bool
  (requires (fun _ -> True))
  (ensures (fun h r h' -> h == h' /\ r == e))
= PF.print_string "Checking ";
  PF.print_string s;
  PF.print_string ": ";
  check_is_true_body e

assume (* implemented in main.c *)
val is_equal
  (b1: B.buffer U8.t)
  (b2: B.buffer Secret.uint8)
  (len: U32.t)
: HST.Stack bool
  (requires (fun h ->
    B.live h b1 /\
    B.live h b2 /\
    U32.v len <= B.length b1 /\
    U32.v len <= B.length b2
  ))
  (ensures (fun h res h' ->
    h' == h /\
    (res == true <==> Seq.slice (Seq.seq_hide #Secret.U8 (B.as_seq h b1)) 0 (U32.v len) == Seq.slice (B.as_seq h b2) 0 (U32.v len))
  ))

inline_for_extraction
noextract
let used_in_not_unused_in_disjoint
  ()
: HST.Stack unit
  (requires (fun _ -> True))
  (ensures (fun h _ h' ->
    h' == h /\
    B.loc_disjoint (B.loc_unused_in h) (B.loc_not_unused_in h)
  ))
= let h = HST.get () in
  B.loc_unused_in_not_unused_in_disjoint h

#push-options "--z3rlimit 128 --query_stats --using_facts_from '*,-LowStar.Monotonic.Buffer.unused_in_not_unused_in_disjoint_2' --fuel 2 --ifuel 2"

module Cast = FStar.Int.Cast

let test () : HST.ST C.exit_code
  (requires (fun _ -> True))
  (ensures (fun _ _ _ -> True))
= 
HST.push_frame ();
let res =
  used_in_not_unused_in_disjoint ();
  let st_enc : B.pointer (B.pointer_or_null (Q.state_s idx)) =
    B.alloca B.null 1ul
  in
  used_in_not_unused_in_disjoint ();
  let st_dec : B.pointer (B.pointer_or_null (Q.state_s idx)) =
    B.alloca B.null 1ul
  in
  used_in_not_unused_in_disjoint ();
  let traffic_secret : traffic_secret: B.buffer Secret.uint8 {
    B.length traffic_secret == traffic_secret_length
  } =
    B.alloca_of_list _traffic_secret
  in
  let initial_pn : Q.u62 = 0uL in
  used_in_not_unused_in_disjoint ();
  let plain : plain: B.buffer Secret.uint8 {
    B.length plain == plain_length
  } =
    B.alloca_of_list _plain
  in
  let plain_len = U32.uint_to_t plain_length in
  let dcil8 = 20uy in
  let dcil = Cast.uint8_to_uint32 dcil8 in
  used_in_not_unused_in_disjoint ();
  let dcid = B.alloca 0uy dcil in
  let scil = 20ul in
  used_in_not_unused_in_disjoint ();
  let scid = B.alloca 0uy scil in
  let token_len = 16ul in
  used_in_not_unused_in_disjoint ();
  let token = B.alloca 0uy token_len in
  let cipher_len = plain_len `U32.add` 16ul in
  let pn_len = 3ul in
  let payload_and_pn_len = cipher_len `U32.add` pn_len in
  let version = 0xff000017ul in
  let hdr_spec = Q.BInitial (Secret.hide #Secret.U8 0uy) (Cast.uint32_to_uint64 payload_and_pn_len) (Secret.hide pn_len) token token_len in
  let hdr = Q.BLong version dcid dcil scid scil hdr_spec in
  let public_hdr_len = Q.public_header_len hdr in
  let hdr_len = public_hdr_len `U32.add` pn_len in
  assert (hdr_len == Secret.reveal (Q.header_len hdr));
  let enc_dst_len = hdr_len `U32.add` cipher_len in
  used_in_not_unused_in_disjoint ();
  let enc_dst : B.buffer U8.t =
    B.alloca 0uy enc_dst_len
  in
  used_in_not_unused_in_disjoint ();
  let enc_dst_pn : B.pointer PN.packet_number_t =
    B.alloca (Secret.hide initial_pn) 1ul
  in
  used_in_not_unused_in_disjoint ();
  let dec_dst = B.alloca
    ({
        Q.pn = Secret.hide 0uL;
        Q.header = hdr;
        Q.header_len = Secret.hide 0ul;
        Q.plain_len = Secret.hide 0ul;
        Q.total_len = Secret.hide 0ul;
    })
    1ul
  in
  let j = Ghost.hide idx in
  used_in_not_unused_in_disjoint ();
  let r = Q.create_in idx HS.root st_enc (Secret.hide initial_pn) traffic_secret in
  if not (is_success "create_in st_enc" r)
  then C.EXIT_FAILURE
  else begin
    let st_enc = B.index st_enc 0ul in
    let h = HST.get () in
    let h0 = h in
    let r = Q.encrypt #j st_enc enc_dst enc_dst_pn hdr plain plain_len in
    if not (is_success "encrypt" r)
    then C.EXIT_FAILURE
    else begin
      let pn = B.index enc_dst_pn 0ul in
      used_in_not_unused_in_disjoint ();
      let r = Q.create_in idx HS.root st_dec (Secret.hide initial_pn) traffic_secret in
      if not (is_success "create_in st_dec" r)
      then C.EXIT_FAILURE
      else begin
        let st_dec = B.index st_dec 0ul in
        let h1 = HST.get () in
        let r = Q.decrypt #j st_dec dec_dst enc_dst enc_dst_len dcil8 in
        assert (Q.derive_k j st_dec h1 == Q.derive_k j st_enc h0);
        assert (Q.derive_iv j st_dec h1 == Q.derive_iv j st_enc h0);
        assert (Q.derive_pne j st_dec h1 == Q.derive_pne j st_enc h0);
        QS.lemma_encrypt_correct j.Q.aead_alg (Q.derive_k j st_enc h0)  (Q.derive_iv j st_enc h0) (Q.derive_pne j st_enc h0) (Q.g_header hdr h0 pn) (U8.v dcil8) (Secret.v (Q.g_last_packet_number (B.deref h1 st_dec) h1)) (Seq.seq_reveal (B.as_seq h0 plain));
        assert (r == E.Success);
        if not (is_success "decrypt" r)
        then C.EXIT_FAILURE
        else begin
          let res = B.index dec_dst 0ul in
          if not (check_is_true "pn" (ADMITDeclassify.u64_to_UInt64 res.Q.pn = ADMITDeclassify.u64_to_UInt64 pn))
          then C.EXIT_FAILURE
          else if not (check_is_true "header_len" (ADMITDeclassify.u32_to_UInt32 res.Q.header_len = hdr_len))
          then C.EXIT_FAILURE
          else if not (check_is_true "plain_len" (ADMITDeclassify.u32_to_UInt32 res.Q.plain_len = plain_len))
          then C.EXIT_FAILURE
          else if not (check_is_true "total_len" (ADMITDeclassify.u32_to_UInt32 res.Q.total_len = enc_dst_len))
          then C.EXIT_FAILURE
          else
            let plain' = B.sub enc_dst hdr_len plain_len in
            let chk = is_equal plain' plain plain_len in
            if not (check_is_true "plain" chk)
            then C.EXIT_FAILURE
            else C.EXIT_SUCCESS
        end
      end
    end
  end
in  
HST.pop_frame ();
res
