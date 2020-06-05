module Model.Helpers

friend Lib.RawIntTypes

let correct #l (b:Seq.seq UInt8.t{Seq.length b = l})
  : Lemma (reveal #l (hide b) == b)
  [SMTPat (reveal #l (hide b))]
=
  assert (reveal #l (hide b) `Seq.equal` b)

let correct2 #l b =
  assert (hide (reveal #l b) `Seq.equal` b)
