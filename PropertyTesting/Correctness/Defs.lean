import PropertyTesting.Instruction


def instructionAtPc_unchecked (mem: List (UInt64 × UInt256)) (pc: UInt64) : Instruction :=
  match mem with
    | [] => {
      offDst := 0,
      offOp0 := 0,
      offOp1 := 0,
      flags := 0
    }
    | (loc, val)::rest => if loc=pc then uint256ToInstruction_unchecked val else instructionAtPc_unchecked rest pc

-- Parses the data at pc iff there is such an entry and if the value is within 2^63
def instructionAtPc_checked (mem: List (UInt64 × UInt256)) (pc: UInt64): Option Instruction :=
  match mem with
    | [] => none
    | (loc, val)::rest => if loc=pc then uint256ToInstruction_checked val else instructionAtPc_checked rest pc

def fieldMem_unchecked (rawMem: List (UInt64 × UInt256)): (List (Felt × Felt)) :=
  (rawMem.map (λ(loc, val) => (uint64ToFelt loc, uint256ToFelt_unchecked val)))

def fieldMem_checked (rawMem: List (UInt64 × UInt256)): Option (List (Felt × Felt)) :=
  if rawMem.all (λ(_, x) => x.val < PRIME)
  then .some (fieldMem_unchecked rawMem)
  else .none

def memGet_checked (mem: List (Felt × Felt)) (input: Felt) : Option Felt :=
  match mem with
    | [] => .none
    | (loc, val)::rest => if loc=input then .some val else memGet_checked rest input

def memGet_unchecked (mem: List (Felt × Felt)) (input: Felt): Felt :=
  match memGet_checked mem input with
    | .none => 0
    | .some val => val

def isParsedTraceValid [Field F] [DecidableEq F] (trace: List (RegisterState F)) (mem: F → F): Prop :=
  match trace with
    | a::b::rest => NextState mem a b ∧ isParsedTraceValid (b::rest) mem
    | _ => True

def isTraceValid_unchecked (trace: List (UInt64 × UInt64 × UInt64)) (mem: List (UInt64 × UInt256)): Prop :=
  match (fieldMem_checked mem) with
    | .some fMem => isParsedTraceValid (trace.map uint64sToRegisterState) (memGet_unchecked fMem)
    | .none => False

def instructions_for_trace_checked (trace: List (UInt64 × UInt64 × UInt64)) (mem: List (UInt64 × UInt256)): Option (List ((UInt64 × UInt64 × UInt64) × Instruction)) :=
  if trace.all (λ(pc, _, _) => (instructionAtPc_checked mem pc).isSome)
  then .some (trace.map (λ (pc, ap, fp) => ((pc, ap, fp), instructionAtPc_unchecked mem pc)))
  else .none

def mem_pc_valid (trace: List (UInt64 × UInt64 × UInt64)) (mem: List (UInt64 × UInt256)): Prop :=
  ∀ mem_entry, mem_entry ∈ mem → ∀ trace_entry, trace_entry ∈ trace → mem_entry.fst = trace_entry.fst → ↑mem_entry.snd.val < Instruction_range

def isTraceValid_checked (trace: List (UInt64 × UInt64 × UInt64)) (mem: List (UInt64 × UInt256)): Prop :=
  mem_pc_valid trace mem ∧
  match instructions_for_trace_checked trace mem with
    | .none => False
    | .some _ => isTraceValid_unchecked trace mem