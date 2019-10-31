module QUIC.Parse

module B = LowStar.Buffer
module U8 = FStar.UInt8
module U32 = FStar.UInt32
module HST = FStar.HyperStack.ST

val test : B.buffer U8.t -> HST.Stack U32.t (requires (fun _ -> False)) (ensures (fun _ _ _ -> True))
