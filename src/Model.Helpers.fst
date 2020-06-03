module Model.Helpers

friend Lib.RawIntTypes

let correct #l (b:Seq.seq UInt8.t{Seq.length b = l})
  : Lemma (reveal #l (hide #l b) == b)
  [SMTPat (reveal #l (hide #l b))]
=
  assert (reveal #l (hide #l b) `Seq.equal` b)
