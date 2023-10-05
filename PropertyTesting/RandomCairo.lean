import Mathlib.Testing.SlimCheck.Testable

import Verification.Semantics.Assembly

instance : SlimCheck.SampleableExt ℤ :=
  SlimCheck.SampleableExt.mkSelfContained do
    let n ← SlimCheck.SampleableExt.interpSample ℕ
    return (n % 2) * ((n: ℤ) / 2) + (1 - n % 2) * ((n: ℤ) / -2)

deriving instance Repr for Op0Spec

instance : SlimCheck.Shrinkable Op0Spec where
  shrink := λ _ => []

instance : SlimCheck.SampleableExt Op0Spec :=
  SlimCheck.SampleableExt.mkSelfContained do
    let idx ← SlimCheck.SampleableExt.interpSample ℕ
    let val ← SlimCheck.SampleableExt.interpSample ℤ
    return match idx % 2 with
      | 0 => Op0Spec.ap_plus val
      | _ => Op0Spec.fp_plus val

deriving instance Repr for Op1Spec

instance : SlimCheck.Shrinkable Op1Spec where
  shrink := λ _ => []

instance : SlimCheck.SampleableExt Op1Spec :=
  SlimCheck.SampleableExt.mkSelfContained do
    let idx ← SlimCheck.SampleableExt.interpSample ℕ
    let val ← SlimCheck.SampleableExt.interpSample ℤ
    return match idx % 4 with
      | 0 => Op1Spec.mem_op0_plus val
      | 1 => Op1Spec.mem_pc_plus val
      | 2 => Op1Spec.mem_fp_plus val
      | _ => Op1Spec.mem_ap_plus val

deriving instance Repr for ResSpec

instance : SlimCheck.Shrinkable ResSpec where
  shrink := λ _ => []

instance : SlimCheck.SampleableExt ResSpec :=
  SlimCheck.SampleableExt.mkSelfContained do
    let idx ← SlimCheck.SampleableExt.interpSample ℕ
    let val ← SlimCheck.SampleableExt.interpSample Op1Spec
    return match idx % 2 with
      | 0 => ResSpec.op1 val
      | 1 => ResSpec.op0_plus_op1 val
      | _ => ResSpec.op0_times_op1 val

deriving instance Repr for DstSpec

instance : SlimCheck.Shrinkable DstSpec where
  shrink := λ _ => []

instance : SlimCheck.SampleableExt DstSpec :=
  SlimCheck.SampleableExt.mkSelfContained do
    let idx ← SlimCheck.SampleableExt.interpSample ℕ
    let val ← SlimCheck.SampleableExt.interpSample ℤ
    return match idx % 2 with
      | 0 => DstSpec.mem_ap_plus val
      | _ => DstSpec.mem_fp_plus val

deriving instance Repr for Instr

instance : SlimCheck.Shrinkable Instr where
  shrink := λ _ => []

instance : SlimCheck.SampleableExt Instr :=
  SlimCheck.SampleableExt.mkSelfContained do
    let idx ← SlimCheck.SampleableExt.interpSample ℕ
    match idx % 6 with
      | 0 => do
        let op0 ← SlimCheck.SampleableExt.interpSample Op0Spec
        let res ← SlimCheck.SampleableExt.interpSample ResSpec
        let dst ← SlimCheck.SampleableExt.interpSample DstSpec
        let ap_update ← SlimCheck.SampleableExt.interpSample Bool
        return assertEqInstr op0 res dst ap_update
      | 1 => do
        let jump_abs ← SlimCheck.SampleableExt.interpSample Bool
        let op0 ← SlimCheck.SampleableExt.interpSample Op0Spec
        let res ← SlimCheck.SampleableExt.interpSample ResSpec
        let ap_update ← SlimCheck.SampleableExt.interpSample Bool
        return jumpInstr jump_abs op0 res ap_update
      | 2 => do
        let op0 ← SlimCheck.SampleableExt.interpSample Op0Spec
        let op1 ← SlimCheck.SampleableExt.interpSample Op1Spec
        let dst ← SlimCheck.SampleableExt.interpSample DstSpec
        let ap_update ← SlimCheck.SampleableExt.interpSample Bool
        return jnzInstr op0 op1 dst ap_update
      | 3 => do
        let call_abs ← SlimCheck.SampleableExt.interpSample Bool
        let res ← SlimCheck.SampleableExt.interpSample ResSpec
        return callInstr call_abs res
      | 4 => do
        return retInstr
      | _ => do
        let op0 ← SlimCheck.SampleableExt.interpSample Op0Spec
        let res ← SlimCheck.SampleableExt.interpSample ResSpec
        return advanceApInstr op0 res



-- #eval SlimCheck.Testable.check (∀ z : ℤ, z ≥ 0) {
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

-- def test: IO Unit := do
--   SlimCheck.Testable.checkIO (∀ i: Instr, do
--     IO.FS.writeFile (System.mkFilePath [".", "out"]) (reprStr i)
--     return True
--   )
--   IO.bindTask
--   -- SlimCheck.Testable.check (∀ i: Instr, Id.run do
--   --   IO.FS.writeFile (System.mkFilePath ["."]) (reprStr i)
--   --   return True
--   -- )

def toIO (i: Instr): IO Instr := do return i

def funcToIOFunc (f: Prop → IO PUnit) (p: IO Prop): IO PUnit :=
  p.bind f

def wrappedCheck (p: Prop) [SlimCheck.Testable p]: IO PUnit :=
  SlimCheck.Testable.check p {
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

-- funcToIOFunc (wrappedCheck) (do write return exec)

-- def test (i: Instr) : IO Prop :=
--   Monad.toBind.bind (toIO i) (SlimCheck.Testable.checkIO)


-- ∀ prog: Prog, do
  --write prog to file
  --(mem, trace) ← exec vm on file
  --trace is valid on mem for prog

-- open SlimCheck in
-- open Decorations in
-- /-- Run a test suite for `p` and throw an exception if `p` does not hold. -/
-- def Testable.check (p : Prop) (cfg : Configuration := {}) [Testable p] : IO PUnit := do
--   match ← Testable.checkIO p cfg with
--   | TestResult.success _ => if !cfg.quiet then IO.println "Success"
--   | TestResult.gaveUp n => if !cfg.quiet then IO.println s!"Gave up {n} times"
--   | TestResult.failure _ xs n => throw (IO.userError $ Testable.formatFailure "Found problems!" xs n)
  

-- #eval SlimCheck.Testable.check (∀ z : Instr, z.apUpdate.fst → z.apUpdate.snd) {
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