import Verification.Semantics.Cpu
import Mathlib.Data.ZMod.Basic

-- def toNat [Field F] (f: F) : ℕ := by exact?
  

-- def NextStateDecidable [Field F] [DecidableEq F] (mem: F → F) (s t : RegisterState F) : Decidable (NextState mem s t) :=
--   (mem s.pc).toNat

def PRIME := 3618502788666131213697322783095070105623107215331596699973092056135872020481
-- May need to store this as four UInt64s for efficiency
def UInt256.size : Nat := 115792089237316195423570985008687907853269984665640564039457584007913129639936
structure UInt256 where
  val : Fin UInt256.size

axiom P_PRIME : Nat.Prime PRIME
instance: Fact PRIME.Prime := fact_iff.mpr P_PRIME

abbrev Felt := ZMod PRIME

def uint64ToFelt (u: UInt64) : Felt := u.val
def uint256ToFelt (u: UInt256) : Felt := u.val
def uint64sToRegisterState (u: (UInt64 × UInt64 × UInt64)) : RegisterState Felt := { pc := u.1.val, ap := u.2.1.val, fp := u.2.2.val }
def uint256ToInstruction (u: UInt256) : Instruction := sorry
-- {
--   offDst := (Bitvec.ofFin u.val), --& 0b1111111111111111,
--   offOp0 := (Bitvec.ofFin u.val).ushr 16,--(u.val >> 16), --& 0b1111111111111111,
--   offOp1 := (Bitvec.ofFin u.val).ushr 32,--(u.val >> 32), --& 0b1111111111111111,
--   flags :=  (Bitvec.ofFin u.val).ushr 48,--(u.val >> 48)  --& 0b111111111111111
-- }

lemma uint64Size_lt_PRIME : UInt64.size < PRIME := by simp
lemma uint64Size_le_PRIME : UInt64.size ≤ PRIME := by simp
-- lemma uint256ToInstruction_inv : memGet fmem (uint64sToRegisterState s).pc = ↑(Instruction.toNat i)

def instructionAtPc (mem: List (UInt64 × UInt256)) (pc: UInt64) : Instruction :=
  match mem with
    | [] => {offDst := 0, offOp0 := 0, offOp1 := 0, flags:= 0}
    | (loc, val)::rest => if loc=pc then uint256ToInstruction val else instructionAtPc rest pc

def fieldMem (rawMem: List (UInt64 × UInt256)) : Option (List (Felt × Felt)) :=
  if rawMem.all (λ (_, x) => x.val < PRIME)
  then .some (rawMem.map (λ (loc, val) => (uint64ToFelt loc, uint256ToFelt val)))
  else .none

lemma fieldMem_nil: fieldMem [] = some [] := by aesop

lemma fieldMem_range (h: fieldMem mem = some fmem) : fmem.all (λ (loc, _) => loc.val < UInt64.size) := by
  rewrite [List.all_eq_true]
  intro ⟨loc, _⟩
  unfold fieldMem at h
  simp at h
  by_cases h_cond: (List.all mem λ x => decide (↑x.snd.val < PRIME))
  . simp [h_cond] at h
    rewrite [←h]
    intro h_map
    simp at h_map ⊢
    sorry
  . simp [h_cond] at h


def memGet (mem: List (Felt × Felt)) (input: Felt) : Felt :=
  match mem with
    | [] => 0
    | (loc, val)::rest => if loc=input then val else memGet rest input

lemma TEMP (head: UInt64 × UInt64 × UInt64): ∀ loc: UInt64, loc=head.fst ↔ (uint64ToFelt loc)=(uint64sToRegisterState head).pc := by
  intro loc
  apply Iff.intro
  . intro h
    unfold uint64ToFelt uint64sToRegisterState
    simp [h]
  . intro h
    unfold uint64ToFelt uint64sToRegisterState at h
    simp at h
    have val_val_eq: Fin.val (loc.val) = Fin.val (head.fst.val) := by
      injection h with h1
      have hLoc: ↑loc.val < PRIME := Nat.lt_of_lt_of_le loc.val.2 uint64Size_le_PRIME
      have hHead: ↑head.fst.val < PRIME := Nat.lt_of_lt_of_le head.fst.val.2 uint64Size_le_PRIME
      rewrite [Nat.mod_eq_of_lt, Nat.mod_eq_of_lt] at h1
      all_goals aesop
    have val_eq: loc.val = head.fst.val := Fin.eq_of_val_eq val_val_eq
    cases loc
    simp at *
    simp [val_eq]

def isParsedTraceValid [Field F] [DecidableEq F] (trace: List (RegisterState F)) (mem: F → F): Prop :=
  match trace with
    | a::b::rest => NextState mem a b ∧ isParsedTraceValid (b::rest) mem
    | _ => True

def isTraceValid (trace: List (UInt64 × UInt64 × UInt64)) (mem: List (UInt64 × UInt256)) : Prop :=
  match (fieldMem mem) with
    | .some fMem => isParsedTraceValid (trace.map uint64sToRegisterState) (memGet fMem)
    | .none => False

def instruction_nextPc_decidable [Field F] [DecidableEq F] (i: Instruction) (mem: F → F) (s t: RegisterState F): Decidable (Option.Agrees (i.nextPc mem s) t.pc) := by
  unfold Instruction.nextPc Option.Agrees
  match i.pcJumpAbs, i.pcJumpRel, i.pcJnz with
    | false, false, false => exact (decEq (s.pc + i.size) t.pc)
    | false, false, true =>
      by_cases h: i.dst mem s = 0
      . simp [h]; exact (decEq (s.pc + i.size) t.pc)
      . match i.op1 mem s with
        | some op1 => simp [h]; exact (decEq (s.pc + op1) t.pc)
        | none => exact .isTrue (by aesop)
    | false, true, false =>
      match i.res mem s with
        | some res => exact (decEq (s.pc + res) t.pc)
        | none => exact .isTrue (by aesop)
    | false, true, true => exact .isTrue (by aesop)
    | true, false, false =>
      match i.res mem s with
        | some res => exact (decEq res t.pc)
        | none => exact .isTrue (by aesop)
    | true, false, true => exact .isTrue (by aesop)
    | true, true, false => exact .isTrue (by aesop)
    | true, true, true => exact .isTrue (by aesop)

def instruction_nextAp_decidable [Field F] [DecidableEq F] (i: Instruction) (mem: F → F) (s t: RegisterState F): Decidable (Option.Agrees (i.nextAp mem s) t.ap) := by
  unfold Instruction.nextAp Option.Agrees
  match i.opcodeCall, i.opcodeRet, i.opcodeAssertEq with
    | false, false, false =>
      match i.nextApAux mem s with
        | some a =>
          by_cases a = t.ap
          . exact .isTrue (by aesop)
          . exact .isFalse (by aesop)
        | none => exact .isTrue (by aesop)
    | false, false, true =>
      match i.nextApAux mem s with
        | some a =>
          by_cases a = t.ap
          . exact .isTrue (by aesop)
          . exact .isFalse (by aesop)
        | none => exact .isTrue (by aesop)
    | false, true, false =>
      match i.nextApAux mem s with
        | some a =>
          by_cases a = t.ap
          . exact .isTrue (by aesop)
          . exact .isFalse (by aesop)
        | none => exact .isTrue (by aesop)
    | false, true, true => exact .isTrue (by aesop)
    | true, false, false =>
      match i.apAdd, i.apAdd1 with
        | false, false =>
          by_cases (s.ap + 2) = t.ap
          . exact .isTrue (by aesop)
          . exact .isFalse (by aesop)
        | false, true => exact .isTrue (by aesop)
        | true, false => exact .isTrue (by aesop)
        | true, true => exact .isTrue (by aesop)
    | true, false, true => exact .isTrue (by aesop)
    | true, true, false => exact .isTrue (by aesop)
    | true, true, true => exact .isTrue (by aesop)

def instruction_nextFp_decidable [Field F] [DecidableEq F] (i: Instruction) (mem: F → F) (s t: RegisterState F): Decidable (Option.Agrees (i.nextFp mem s) t.fp) := by
  unfold Instruction.nextFp Option.Agrees
  match i.opcodeCall, i.opcodeRet, i.opcodeAssertEq with
    | false, false, false =>
      by_cases s.fp = t.fp
      . exact .isTrue (by aesop)
      . exact .isFalse (by aesop)
    | false, false, true =>
      by_cases s.fp = t.fp
      . exact .isTrue (by aesop)
      . exact .isFalse (by aesop)
    | false, true, false =>
      by_cases i.dst mem s = t.fp
      . exact .isTrue (by aesop)
      . exact .isFalse (by aesop)
    | false, true, true => exact .isTrue (by aesop)
    | true, false, false =>
      by_cases (s.ap + 2) = t.fp
      . exact .isTrue (by aesop)
      . exact .isFalse (by aesop)
    | true, false, true => exact .isTrue (by aesop)
    | true, true, false => exact .isTrue (by aesop)
    | true, true, true => exact .isTrue (by aesop)

def instruction_asserts_decidable [Field F] [DecidableEq F] (i: Instruction) (mem: F → F) (s: RegisterState F): Decidable (i.Asserts mem s) := by
  unfold Instruction.Asserts
  match i.opcodeCall, i.opcodeRet, i.opcodeAssertEq with
    | false, false, false => exact .isTrue (by aesop)
    | false, true, false => exact .isTrue (by aesop)
    | false, false, true =>
      match (i.res mem s), (i.dst mem s) with
        | .some x, y =>
          by_cases x=y
          . exact .isTrue (by simp [Option.Agrees, h])
          . exact .isFalse (by {simp [Option.Agrees, h]})
        | .none, _ => exact .isTrue (by simp [Option.Agrees])
    | false, true, true => exact .isTrue (by aesop)
    | true, false, false =>
      if Instruction.op0 i mem s = s.pc + i.size ∧ i.dst mem s = s.fp
      then exact .isTrue (by aesop)
      else exact .isFalse (by aesop)
    | true, true, false => exact .isTrue (by aesop)
    | true, false, true => exact .isTrue (by aesop)
    | true, true, true => exact .isTrue (by aesop)

def instruction_nextState_decidable [Field F] [DecidableEq F] (i: Instruction) (mem: F → F) (s t: RegisterState F): Decidable (i.NextState mem s t) := by
  unfold Instruction.NextState
  have nextPc: _ := instruction_nextPc_decidable i mem s t
  have nextAp: _ := instruction_nextAp_decidable i mem s t
  have nextFp: _ := instruction_nextFp_decidable i mem s t
  have asserts: _ := instruction_asserts_decidable i mem s
  apply instDecidableAnd

set_option maxHeartbeats 0
def trace_head_decidable (s t: UInt64 × UInt64 × UInt64) (h_fmem: fieldMem mem = some fMem): Decidable (NextState (memGet fMem) (uint64sToRegisterState s) (uint64sToRegisterState t)) := by
  unfold NextState
  have h_dec: _ := instruction_nextState_decidable (instructionAtPc mem s.1) (memGet fMem) (uint64sToRegisterState s) (uint64sToRegisterState t)
  by_cases (instructionAtPc mem s.1).NextState (memGet fMem) (uint64sToRegisterState s) (uint64sToRegisterState t)
  case pos => exact .isTrue ⟨instructionAtPc mem s.fst, (by {
    simp [h]
    unfold memGet instructionAtPc
    induction mem with
      | nil =>
        have h_fmem_empty : fMem = [] := by
          rewrite [fieldMem_nil] at h_fmem
          injection h_fmem with h'
          exact h'.symm
        rewrite [h_fmem_empty]
        simp only
        -- sorry
      | cons memHead memTail memTail_ih => sorry
  })⟩
  case neg => exact .isFalse (by {
    simp only [not_exists, not_and]
    intro i h_i
    sorry
  })

def isTraceValid_decidable (trace: List (UInt64 × UInt64 × UInt64)) (mem: List (UInt64 × UInt256)) : Decidable (isTraceValid trace mem) := by
  unfold isTraceValid
  cases h_fmem: (fieldMem mem) with
    | some fMem =>
      unfold isParsedTraceValid
      induction trace with
        | nil =>
          simp
          exact isTrue trivial
        | cons s tail tail_ih =>
          simp
          cases tail with
            | nil =>
              simp
              exact isTrue trivial
            | cons t rest =>
              simp at tail_ih ⊢
              unfold isParsedTraceValid
              have head_dec: _ := trace_head_decidable s t h_fmem
              apply instDecidableAnd
    | none =>
      simp
      exact isFalse (by simp)


















  -- induction trace with
  --   | nil =>
  --     unfold isTraceValid
  --     exact isTrue trivial
  --   | cons head tail tail_ih =>
  --     unfold isTraceValid
  --     cases tail with
  --       | nil =>
  --         simp
  --         exact isTrue trivial
  --       | cons s t =>
  --         simp
  --         have head_dec: Decidable (NextState (fieldMem mem) (uint64sToRegisterState head) (uint64sToRegisterState s)) := by
  --           unfold NextState
  --           let i := instructionAtPc mem head.1
  --           have h_i : i = instructionAtPc mem head.1 := rfl
  --           have h_eq: fieldMem mem (uint64sToRegisterState head).pc = ↑(Instruction.toNat i) := by
  --             rewrite [h_i]
  --             have h_conv: ∀ u: UInt256, uint256ToFelt u = ↑(Instruction.toNat (uint256ToInstruction u)) := by
  --               intro u
  --               unfold uint256ToFelt Instruction.toNat
  --               simp only [Nat.cast_add, Nat.cast_mul, Nat.cast_pow, Nat.cast_ofNat]
  --               unfold Bitvec.toNatr

  --         apply instDecidableAnd
  -- unfold isTraceValid
  -- match trace with
  --   | a::b::rest => sorry
  --   | _ => 
  --length = 0 or 1 => isTraceValid by simp/manual match proof
  --length 2 or more (s::t::rest)
    --let fMem = fieldMem mem
    --NextState ↔ ∃ i : Instruction, fMem s.pc = ↑i.toNat ∧ i.NextState fMem s t
    -- rtp (∃ i : Instruction, fMem s.pc = ↑i.toNat ∧ i.NextState fMem s t) ↔ (uint256ToInstruction (mem s.pc)).NextState fMem s t
    --    rtp (∃ i : Instruction, fMem s.pc = ↑i.toNat ∧ i.NextState mem s t) → (uint256ToInstruction (mem s.pc)).NextState fMem s t
    --        assume ∃ i : Instruction, fMem s.pc = ↑i.toNat ∧ i.NextState mem s t
    --        rtp (uint256ToInstruction (mem s.pc)).NextState mem s t
    --        !!rtp ∀ i : Instruction, fMem s.pc = ↑i.toNat → i=uint256ToInstruction (mem s.pc)
    --    rtp (uint256ToInstruction (mem s.pc)).NextState mem s t → ∃ i : Instruction, mem s.pc = ↑i.toNat ∧ i.NextState mem s t)
    --        assume (uint256ToInstruction (mem s.pc)).NextState mem s t
    --        let i  = uint256ToInstruction (mem s.pc)
    --        have i.NextState mem s t
    --        rtp fMem s.pc = ↑(uint256ToInstruction (mem s.pc)).toNat


