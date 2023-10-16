import PropertyTesting.Correctness.Basic

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

def nextState_decidable
  (trace : List (UInt64 × UInt64 × UInt64))
  (mem : List (UInt64 × UInt256))
  (trace_with_instructions : List ((UInt64 × UInt64 × UInt64) × Instruction))
  (fMem : List (Felt × Felt))
  (trace_head trace_next : UInt64 × UInt64 × UInt64)
  (trace_tail : List (UInt64 × UInt64 × UInt64))
  (h_instructions: instructions_for_trace_checked trace mem = some trace_with_instructions)
  (h_fmem: fieldMem_checked mem = some fMem)
  (h_trace: trace = trace_head :: trace_next :: trace_tail)
  (h_instructions_valid: ∀ t ∈ trace, ∀ value: UInt256, (t.fst, value) ∈ mem → value.val < Instruction_range):
  Decidable (NextState (memGet_unchecked fMem) (uint64sToRegisterState trace_head) (uint64sToRegisterState trace_next)) := by
    unfold NextState
    rcases h_trace_with_instructions: trace_with_instructions with _ | ⟨⟨⟨pc,ap,fp⟩,instruction⟩, tail⟩
    case nil =>
      rewrite [h_trace_with_instructions] at h_instructions
      have h_contr: _ := (instructions_for_trace_checked_nil trace mem).mp h_instructions
      aesop
    case cons =>
      have h_instructions' : _ := h_instructions
      rewrite [h_trace_with_instructions] at h_instructions
      have h_mem_pc_valid : ∀ (value : UInt256), (pc, value) ∈ mem → ↑value.val < Instruction_range := by
        intro value h_mem
        rewrite [h_trace] at h_instructions
        have h_trace_head: (pc, ap, fp) ∈ trace := by
          rewrite [h_trace]
          apply List.mem_cons.mpr
          simp [pc_of_instructions_for_trace_checked h_instructions]
        exact h_instructions_valid (pc, ap, fp) h_trace_head value (by simp [h_mem])
      rcases instruction_nextState_decidable instruction (memGet_unchecked fMem) (uint64sToRegisterState trace_head) (uint64sToRegisterState trace_next) with ⟨h_instruction_nextState⟩ | ⟨h_instruction_not_nextState⟩
      case isTrue => exact .isTrue ⟨instruction, (by {
        simp only [h_instruction_not_nextState, and_true]
        rewrite [h_trace] at h_instructions
        rewrite [instructions_for_trace_checked_head h_instructions]
        exact memGet_pc_eq_instruction_toNat pc trace mem trace_with_instructions tail fMem trace_head trace_next trace_tail h_instructions' h_fmem h_trace h_trace_with_instructions h_mem_pc_valid
      })⟩
      case isFalse => exact .isFalse (by {
        simp only [not_exists, not_and]
        intro instruction'
        by_cases h_eq: instruction=instruction'
        case pos =>
          rewrite [h_eq] at h_instruction_nextState
          simp [h_instruction_nextState]
        case neg =>
          contrapose
          intro
          have h_get_pc: _ := memGet_pc_eq_instruction_toNat pc trace mem trace_with_instructions tail fMem trace_head trace_next trace_tail h_instructions' h_fmem h_trace h_trace_with_instructions h_mem_pc_valid
          rewrite [h_get_pc]
          rewrite [h_trace] at h_instructions
          rewrite [←instructions_for_trace_checked_head h_instructions]
          exact toNat_feltCast_neq_of_instruction_neq instruction instruction' h_eq
      })


def isParsedTraceValid_decidable
  (trace : List (UInt64 × UInt64 × UInt64))
  (mem : List (UInt64 × UInt256))
  (trace_with_instructions : List ((UInt64 × UInt64 × UInt64) × Instruction))
  (fMem : List (Felt × Felt))
  (h_instructions: instructions_for_trace_checked trace mem = some trace_with_instructions)
  (h_fmem: fieldMem_checked mem = some fMem)
  (h_instructions_valid: ∀ t ∈ trace, ∀ value: UInt256, (t.fst, value) ∈ mem → value.val < Instruction_range):
  Decidable (isParsedTraceValid (List.map uint64sToRegisterState trace) (memGet_unchecked fMem)) := by
    unfold isParsedTraceValid
    rcases h_trace: trace with _ | ⟨trace_head, _ | ⟨trace_next, trace_tail⟩⟩
    case nil =>
      simp only [List.map]
      exact .isTrue trivial
    case cons.nil =>
      simp only [List.map]
      exact .isTrue trivial
    case cons.cons =>
      simp only [List.map]
      have nextState_decidable : Decidable (NextState (memGet_unchecked fMem) (uint64sToRegisterState trace_head) (uint64sToRegisterState trace_next)) :=
        nextState_decidable trace mem trace_with_instructions fMem trace_head trace_next trace_tail h_instructions h_fmem h_trace h_instructions_valid
      have h_instructions_rec: instructions_for_trace_checked (trace_next::trace_tail) mem = some trace_with_instructions.tail :=
        instructions_for_trace_checked_tail h_instructions h_trace
      have h_instructions_valid_rec: ∀ t ∈ (trace_next::trace_tail), ∀ value: UInt256, (t.fst, value) ∈ mem → value.val < Instruction_range := by
        intro t h_t value h_value
        apply h_instructions_valid
        . rewrite [h_trace]
          rewrite [List.mem_cons]
          right
          exact h_t
        . exact h_value
      have raw_rec: Decidable (isParsedTraceValid (List.map uint64sToRegisterState (trace_next :: trace_tail)) (memGet_unchecked fMem)) :=
        isParsedTraceValid_decidable (trace_next::trace_tail) mem trace_with_instructions.tail fMem h_instructions_rec h_fmem h_instructions_valid_rec
      have decidable_rec : Decidable (isParsedTraceValid (uint64sToRegisterState trace_next :: List.map uint64sToRegisterState trace_tail) (memGet_unchecked fMem)) :=
        by aesop
      apply instDecidableAnd

def isTraceValid_unchecked_decidable
  (trace : List (UInt64 × UInt64 × UInt64))
  (mem : List (UInt64 × UInt256))
  (trace_with_instructions : List ((UInt64 × UInt64 × UInt64) × Instruction))
  (h_instructions: instructions_for_trace_checked trace mem = some trace_with_instructions)
  (h_instructions_valid: ∀ t ∈ trace, ∀ value: UInt256, (t.fst, value) ∈ mem → value.val < Instruction_range):
  Decidable (isTraceValid_unchecked trace mem) := by
    unfold isTraceValid_unchecked
    rcases h_fmem: fieldMem_checked mem
    case none =>
      simp only
      exact .isFalse (by simp)
    case some fMem =>
      simp only
      exact isParsedTraceValid_decidable trace mem trace_with_instructions fMem h_instructions h_fmem h_instructions_valid

def mem_pc_valid_decidable
  (trace : List (UInt64 × UInt64 × UInt64))
  (mem : List (UInt64 × UInt256)):
  Decidable (∀ mem_entry, mem_entry ∈ mem → ∀ trace_entry, trace_entry ∈ trace → mem_entry.fst = trace_entry.fst → ↑mem_entry.snd.val < Instruction_range) := by
    apply List.decidableBAll

def isTraceValid_checked_decidable
  (trace: List (UInt64 × UInt64 × UInt64))
  (mem: List (UInt64 × UInt256)):
  Decidable (isTraceValid_checked trace mem) := by
    unfold isTraceValid_checked
    rcases h_instructions: instructions_for_trace_checked trace mem
    case none =>
      simp only
      exact .isFalse (by simp)
    case some trace_with_instructions =>
      simp only
      have mem_valid_dec: _ := mem_pc_valid_decidable trace mem
      rcases h_mem_valid: mem_valid_dec
      case isTrue h_mem_valid_proof =>
        have h_instructions_valid: ∀ t ∈ trace, ∀ value: UInt256, (t.fst, value) ∈ mem → value.val < Instruction_range := by
          intro t h_t value h_value
          exact h_mem_valid_proof (t.fst, value) h_value t h_t (by simp)
        have unchecked_decidable: _ := isTraceValid_unchecked_decidable trace mem trace_with_instructions h_instructions h_instructions_valid
        rcases h_unchecked_decidable: unchecked_decidable
        case isTrue h_unchecked_proof =>
          simp only [h_unchecked_proof, and_true]
          exact .isTrue (by {
            unfold mem_pc_valid
            exact h_mem_valid_proof
          })
        case isFalse h_unchecked_invalid_proof =>
          simp only [h_unchecked_invalid_proof, and_false]
          exact .isFalse (by simp)
      case isFalse h_mem_invalid_proof =>
        exact .isFalse (by {
          simp only [not_and]
          intro h_contr
          simp at h_mem_invalid_proof
          rcases h_mem_invalid_proof with ⟨pc, ⟨⟨ap, fp, h_trace⟩, ⟨val, h_mem, _⟩⟩⟩
          unfold mem_pc_valid at h_contr
          have h_in_range : _ := h_contr (pc, val) h_mem (pc, ap, fp) h_trace (by simp)
          simp at h_in_range
          contradiction
        })
