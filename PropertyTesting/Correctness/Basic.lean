import PropertyTesting.Correctness.Defs

lemma fieldMem_nil: fieldMem_checked [] = some [] := by aesop

lemma fieldMem_cons (h_fmem: fieldMem_checked ((loc, val)::tail) = some fMem): fMem = (uint64ToFelt loc, uint256ToFelt_unchecked val) :: List.map (fun x => (uint64ToFelt x.fst, uint256ToFelt_unchecked x.snd)) tail := by
  unfold fieldMem_checked at h_fmem
  split at h_fmem
  . injection h_fmem with h_fmem
    unfold fieldMem_unchecked at h_fmem
    simp [←h_fmem, List.map_cons]
  . contradiction

lemma fieldMem_tail
  (h_fmem: fieldMem_checked ((loc, val)::tail) = some fMem):
  fieldMem_checked tail = .some (List.map (fun x => (uint64ToFelt x.fst, uint256ToFelt_unchecked x.snd)) tail) := by
    rewrite [fieldMem_cons h_fmem] at h_fmem
    unfold fieldMem_checked at h_fmem
    split at h_fmem
    case inl h_all =>
      unfold fieldMem_checked
      rewrite [List.all_cons, Bool.and_eq_true] at h_all
      simp only [h_all, ite_true, Option.some.injEq]
      injection h_fmem with h_fmem
      unfold fieldMem_unchecked at h_fmem ⊢
      simp [h_fmem]
    case inr => contradiction

lemma instructionAtPc_unchecked_rec
  (h_neq: loc ≠ pc) :
  instructionAtPc_unchecked ((loc, val) :: mem_tail) pc = instructionAtPc_unchecked mem_tail pc := by
    generalize h_instruction: instructionAtPc_unchecked mem_tail pc = instruction
    unfold instructionAtPc_unchecked
    simp [h_neq]
    exact h_instruction

lemma instructions_for_trace_checked_tail
  (h_instructions: instructions_for_trace_checked trace mem = some trace_with_instructions)
  (h_trace: trace = trace_head::trace_tail) :
  instructions_for_trace_checked trace_tail mem = some trace_with_instructions.tail := by
    rewrite [h_trace] at h_instructions
    unfold instructions_for_trace_checked at h_instructions
    by_cases h_all_valid: (List.all (trace_head :: trace_tail) fun x =>
          match x with
          | (pc, _, _) => Option.isSome (instructionAtPc_checked mem pc)) = true
    case pos =>
      simp only [h_all_valid, if_true] at h_instructions
      injection h_instructions with h_instructions
      simp only [← h_instructions, List.map, Prod.mk.eta, List.tail_cons]
      unfold instructions_for_trace_checked
      simp [List.all_cons] at h_all_valid
      simp [List.all_eq_true]
      intro x1 x2 x3 h_x h_contr
      have h_contr' : _ := h_all_valid.2 x1 x2 x3 h_x
      simp [Option.isNone_iff_eq_none] at h_contr
      simp [h_contr] at h_contr'
    case neg =>
      simp only [h_all_valid, if_false] at h_instructions

lemma instructions_for_trace_checked_nil
  (trace : List (UInt64 × UInt64 × UInt64))
  (mem : List (UInt64 × UInt256)):
  instructions_for_trace_checked trace mem = some [] ↔ trace = [] := by
    apply Iff.intro
    . intro h
      unfold instructions_for_trace_checked at h
      by_cases h_cond: (List.all trace fun x =>
          match x with
          | (pc, _, _) => Option.isSome (instructionAtPc_checked mem pc)) =
        true
      case pos => aesop
      case neg => aesop
    . aesop

lemma instructions_for_trace_checked_head
  (h_instructions: instructions_for_trace_checked (trace_head::trace_tail) mem = some (((pc, ap, fp), instruction) :: tail)):
  instruction = instructionAtPc_unchecked mem pc := by
    unfold instructions_for_trace_checked at h_instructions
    by_cases h_cond: (List.all (trace_head :: trace_tail) fun x =>
          match x with
          | (pc, _, _) => Option.isSome (instructionAtPc_checked mem pc)) =
        true
    case pos =>
      simp only [h_cond, if_true] at h_instructions
      injection h_instructions with h_instructions
      simp at h_instructions
      rcases h_instructions with ⟨⟨h_trace_head, h_instruction⟩, _⟩
      simp only [h_trace_head] at h_instruction
      exact h_instruction.symm
    case neg => simp only [h_cond, if_false] at h_instructions

lemma pc_of_instructions_for_trace_checked
  (h_instructions: instructions_for_trace_checked (trace_head::trace_tail) mem = some (((pc, ap, fp), instruction) :: tail)):
  trace_head = (pc, ap, fp) := by
    unfold instructions_for_trace_checked at h_instructions
    split at h_instructions
    . injection h_instructions with h_instructions
      rewrite [List.map_cons] at h_instructions
      injection h_instructions with h_instructions
      aesop
    . aesop

lemma range_of_instructions_for_trace_checked
  (h_instructions: instructions_for_trace_checked (trace_head::trace_tail) ((pc, val)::mem_tail) = some (((pc, ap, fp), instruction)::tail)) :
  ↑val.val < Instruction_range := by
    unfold instructions_for_trace_checked at h_instructions
    split at h_instructions
    case inl h_range =>
      injection h_instructions with h_instructions
      simp [List.map_cons] at h_instructions
      rcases h_instructions with ⟨⟨h_head, _⟩, _⟩
      simp only [h_head, List.all_cons, Bool.and_eq_true] at h_range
      rcases h_range with ⟨h_range, _⟩
      unfold instructionAtPc_checked at h_range
      simp only [if_true] at h_range
      exact (uint256ToInstruction_of_in_range val).mpr h_range
    case inr => contradiction

lemma memGet_pc_eq_instruction_toNat_aux
  (pc ap fp: UInt64)
  (mem : List (UInt64 × UInt256))
  (fMem : List (Felt × Felt))
  (h_fmem: fieldMem_checked mem = some fMem)
  (h_mem_pc_valid: ∀ value: UInt256, (pc, value) ∈ mem → ↑value.val < Instruction_range):
  memGet_unchecked fMem (uint64sToRegisterState (pc, ap, fp)).pc = ↑(Instruction.toNat (instructionAtPc_unchecked mem pc)) := by
    rcases h_mem: mem with _ | ⟨⟨loc, val⟩, mem_tail⟩
    case nil =>
      unfold memGet_unchecked memGet_checked
      rewrite [h_mem, fieldMem_nil] at h_fmem
      injection h_fmem with h_fmem
      rewrite [←h_fmem]
      dsimp only
      unfold instructionAtPc_unchecked
      rewrite [←zero_instruction]
      simp
    case cons =>
      rewrite [h_mem] at h_fmem
      have h_fmem_tail: _ := fieldMem_tail h_fmem
      have h_mem_pc_valid_rec: ∀ value: UInt256, (pc, value) ∈ mem_tail → ↑value.val < Instruction_range := by
        intro value h_value_in_mem_tail
        have h_value_in_mem: (pc, value) ∈ mem := by simp [h_mem, h_value_in_mem_tail]
        exact h_mem_pc_valid value h_value_in_mem
      have h_rec: _ := memGet_pc_eq_instruction_toNat_aux pc ap fp mem_tail (List.map (fun x => (uint64ToFelt x.fst, uint256ToFelt_unchecked x.snd)) mem_tail) h_fmem_tail h_mem_pc_valid_rec
      unfold memGet_unchecked at h_rec ⊢
      have h_fmem_cons: _ := fieldMem_cons h_fmem
      subst h_fmem_cons
      unfold memGet_checked
      unfold uint64sToRegisterState
      simp only
      by_cases h: loc=pc
      . subst h
        simp only [uint64ToFelt_eq_cast]
        unfold instructionAtPc_unchecked
        simp only [if_true]
        apply uint256ToFelt_eq_uint256ToInstruction_toNat_cast
        show ↑val.val < Instruction_range
        apply h_mem_pc_valid
        simp [h_mem]
      . rewrite [←uint64ToFelt_eq_cast]
        by_cases h_eq: uint64ToFelt loc = uint64ToFelt pc
        . have h_contr: loc = pc := uint64ToFelt_inj h_eq
          contradiction
        . simp only [h_eq, if_false]
          unfold uint64sToRegisterState at h_rec
          simp only [←uint64ToFelt_eq_cast] at h_rec
          rw [h_rec, instructionAtPc_unchecked_rec]
          simp [h]

lemma memGet_pc_eq_instruction_toNat
  (pc: UInt64)
  (trace : List (UInt64 × UInt64 × UInt64))
  (mem : List (UInt64 × UInt256))
  (trace_with_instructions : List ((UInt64 × UInt64 × UInt64) × Instruction))
  (tail: List ((UInt64 × UInt64 × UInt64) × Instruction))
  (fMem : List (Felt × Felt))
  (trace_head trace_next : UInt64 × UInt64 × UInt64)
  (trace_tail : List (UInt64 × UInt64 × UInt64))
  (h_instructions: instructions_for_trace_checked trace mem = some trace_with_instructions)
  (h_fmem: fieldMem_checked mem = some fMem)
  (h_trace: trace = trace_head :: trace_next :: trace_tail)
  (h_trace_with_instructions: trace_with_instructions = ((pc, ap, fp), instruction) :: tail)
  (h_mem_pc_valid: ∀ value: UInt256, (pc, value) ∈ mem → ↑value.val < Instruction_range):
  memGet_unchecked fMem (uint64sToRegisterState trace_head).pc = ↑(Instruction.toNat (instructionAtPc_unchecked mem pc)) := by
    have h_trace_head: trace_head = (pc, ap, fp) := by
      rewrite [h_trace, h_trace_with_instructions] at h_instructions
      exact pc_of_instructions_for_trace_checked h_instructions
    rewrite [h_trace_head]
    unfold uint64sToRegisterState
    simp only [←uint64ToFelt_eq_cast]
    exact memGet_pc_eq_instruction_toNat_aux pc ap fp mem fMem h_fmem h_mem_pc_valid
