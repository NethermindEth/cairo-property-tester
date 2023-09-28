import Mathlib.Testing.SlimCheck.Testable

structure MyType where
  low : ℕ
  high : ℕ
  h : low ≤ high
  deriving Repr

instance : SlimCheck.Shrinkable MyType where
  shrink := λ ⟨x,y,_⟩ =>
    let proxy := SlimCheck.Shrinkable.shrink (x, y - x)
    proxy.map (λ ⟨fst, snd⟩ => ⟨fst, fst + snd, (by {
      simp
    })⟩)

instance : SlimCheck.SampleableExt MyType :=
  SlimCheck.SampleableExt.mkSelfContained do
    let x ← SlimCheck.SampleableExt.interpSample Nat
    let xyDiff ← SlimCheck.SampleableExt.interpSample Nat
    pure $ ⟨x, x + xyDiff, (by {
      simp
    })⟩

-- example false prop
-- #eval SlimCheck.Testable.check (∀ a b : MyType, a.low ≤ b.low → a.high ≤ b.high) {
--   numInst := 100,
--   maxSize := 1000,
--   numRetries := 100,
--   traceDiscarded := false,
--   traceSuccesses := false,
--   traceShrink := false,
--   traceShrinkCandidates := false,
--   randomSeed := none,
--   quiet := false
-- }

#eval SlimCheck.Testable.check (∀ a b : MyType, a.high ≤ b.low → a.low ≤ b.high) {
  numInst := 100,
  maxSize := 1000,
  numRetries := 100,
  traceDiscarded := false,
  traceSuccesses := false,
  traceShrink := false,
  traceShrinkCandidates := false,
  randomSeed := none,
  quiet := false
}