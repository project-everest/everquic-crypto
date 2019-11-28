module QUICTest
module Q = QUIC.Impl
module QS = QUIC.Spec
module B = LowStar.Buffer
module U32 = FStar.UInt32
module U8 = FStar.UInt8
module HST = FStar.HyperStack.ST
module HS = FStar.HyperStack
module L = FStar.List.Tot

let idx = {
  Q.hash_alg = Spec.Hash.Definitions.SHA2_256;
  Q.aead_alg = Spec.Agile.AEAD.CHACHA20_POLY1305;
}

inline_for_extraction
noextract
let _traffic_secret = [
  0x48uy; 0xc4uy; 0x30uy; 0x9buy; 0x5fuy; 0x27uy; 0x52uy; 0xe8uy;
  0x12uy; 0x7buy; 0x1uy;  0x66uy; 0x5uy;  0x5auy; 0x9auy; 0x56uy;
  0xe5uy; 0xf9uy; 0x6uy;  0x31uy; 0xe0uy; 0x84uy; 0x85uy; 0xe0uy;
  0xf8uy; 0x9euy; 0x9cuy; 0xecuy; 0x4auy; 0xdeuy; 0xb6uy; 0x50uy;
]

inline_for_extraction
noextract
let traffic_secret_length = norm [delta; zeta; iota; primops] (L.length _traffic_secret)

inline_for_extraction
noextract
let _plain = [
  0uy; 1uy; 2uy; 3uy; 4uy; 5uy; 6uy; 7uy; 8uy; 9uy;
]

inline_for_extraction
noextract
let plain_length = norm [delta; zeta; iota; primops] (L.length _plain)

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

assume
val is_equal
  (b1 b2: B.buffer U8.t)
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
    (res == true <==> Seq.slice (B.as_seq h b1) 0 (U32.v len) == Seq.slice (B.as_seq h b2) 0 (U32.v len))
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

#push-options "--z3rlimit 128 --query_stats --using_facts_from '*,-LowStar.Monotonic.Buffer.unused_in_not_unused_in_disjoint_2'"

module Cast = FStar.Int.Cast

let test () : HST.ST unit
  (requires (fun _ -> True))
  (ensures (fun _ _ _ -> True))
= 
  HST.push_frame ();
  used_in_not_unused_in_disjoint ();
  let st_enc : B.pointer (B.pointer_or_null (Q.state_s idx)) =
    B.alloca B.null 1ul
  in
  used_in_not_unused_in_disjoint ();
  let st_dec : B.pointer (B.pointer_or_null (Q.state_s idx)) =
    B.alloca B.null 1ul
  in
  used_in_not_unused_in_disjoint ();
  let traffic_secret : traffic_secret: B.buffer U8.t {
    B.length traffic_secret == traffic_secret_length
  } =
    B.alloca_of_list _traffic_secret
  in
  let initial_pn : Q.u62 = 0uL in
  used_in_not_unused_in_disjoint ();
  let plain : plain: B.buffer U8.t {
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
  let hdr_spec = Q.BInitial (Cast.uint32_to_uint64 cipher_len) 3ul token token_len in
  let hdr = Q.BLong 0xff000017ul dcid dcil scid scil hdr_spec in
  let hdr_len = Q.header_len hdr in
  let cipher_len = plain_len `U32.add` 16ul in
  let enc_dst_len = hdr_len `U32.add` cipher_len in
  used_in_not_unused_in_disjoint ();
  let enc_dst : enc_dst: B.buffer U8.t =
    B.alloca 0uy enc_dst_len
  in
  used_in_not_unused_in_disjoint ();
  let enc_dst_pn : enc_dst_pn: B.pointer Q.u62 =
    B.alloca initial_pn 1ul
  in
  used_in_not_unused_in_disjoint ();
  let dec_dst = B.alloca
    ({
        Q.pn = 0uL;
        Q.header = hdr;
        Q.header_len = 0ul;
        Q.plain_len = 0ul;
        Q.total_len = 0ul;
    })
    1ul
  in
  let j = Ghost.hide idx in
  used_in_not_unused_in_disjoint ();
  let r = Q.create_in idx HS.root st_enc initial_pn traffic_secret in
  if not (is_success "create_in st_enc" r)
  then ()
  else begin
    let st_enc = B.index st_enc 0ul in
    let h = HST.get () in
    assume (Q.incrementable st_enc h);
    let r = Q.encrypt #j st_enc enc_dst enc_dst_pn hdr plain plain_len in
    if not (is_success "encrypt" r)
    then ()
    else begin
      let pn = B.index enc_dst_pn 0ul in
      used_in_not_unused_in_disjoint ();
      let r = Q.create_in idx HS.root st_dec initial_pn traffic_secret in
      if not (is_success "create_in st_dec" r)
      then ()
      else begin
        let st_dec = B.index st_dec 0ul in
        let h = HST.get () in
        assume (Q.incrementable st_dec h);
        let r = Q.decrypt #j st_dec dec_dst enc_dst enc_dst_len dcil8 in
        if not (is_success "decrypt" r)
        then ()
        else begin
          let res = B.index dec_dst 0ul in
          if not (check_is_true "pn" (res.Q.pn = pn))
          then ()
          else if not (check_is_true "header_len" (res.Q.header_len = hdr_len))
          then ()
          else if not (check_is_true "plain_len" (res.Q.plain_len = plain_len))
          then ()
          else if not (check_is_true "total_len" (res.Q.total_len = enc_dst_len))
          then ()
          else
            let plain' = B.sub enc_dst hdr_len plain_len in
            let chk = is_equal plain' plain plain_len in
            let _ = check_is_true "plain" chk in
            ()
        end
      end
    end
  end;
  HST.pop_frame ();
  ()
