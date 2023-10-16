import PropertyTesting.UInt
import Verification.Semantics.Cpu

def Instruction_range: Nat := 9223372036854775808 -- 2^63
lemma Instruction_range_bin: Instruction_range = 2^63 := by norm_num
lemma Instruction_le_PRIME: Instruction_range ≤ PRIME := by norm_num

set_option maxHeartbeats 0
lemma zero_instruction: 0 = ↑(Instruction.toNat { offDst := 0, offOp0 := 0, offOp1 := 0, flags := 0 }) := by simp

lemma instruction_toNat_range (i: Instruction): i.toNat < Instruction_range := by
  unfold Instruction.toNat
  have h_offDst: i.offDst.toNatr < 2^16 := Bitvec.toNatr_lt i.offDst
  have h_offOp0: i.offOp0.toNatr < 2^16 := Bitvec.toNatr_lt i.offOp0
  have h_offOp1: i.offOp1.toNatr < 2^16 := Bitvec.toNatr_lt i.offOp1
  have h_flags: i.flags.toNatr < 2^15 := Bitvec.toNatr_lt i.flags
  unfold Instruction_range
  norm_num
  linarith

lemma ne_of_add_ne (a b c: ℕ) (h: b ≠ c): a+b ≠ a+c := by
  simp_arith [*]

lemma instruction_toNat_neq_step1 (a b c d: ℕ) (h_a: a < 2^16) (h_c: c < 2^16) (h_neq: a ≠ c): a+(2^16)*b≠c+(2^16)*d := by
  have h_lt_or_ge : _ := Nat.lt_or_ge b d
  rcases h_lt_or_ge with h_lt | h_ge
  . apply Nat.ne_of_lt
    linarith
  . have h_le: d ≤ b := by aesop
    by_cases h_eq: b=d
    . aesop
    . have h_neq': d ≠ b := by aesop
      have h_lt: _ := Nat.lt_of_le_and_ne h_le h_neq'
      linarith

lemma instruction_toNat_neq_step2 (a b c d e f: ℕ) (h_a: a < 2^16) (h_b: b < 2^16) (h_d: d < 2^16) (h_e: e < 2^16) (h_neq: a≠d ∨ b≠e): a+(2^16)*b+(2^32)*c ≠ d+(2^16)*e+(2^32)*f := by
  by_cases h: a=d
  . rewrite [h]
    rewrite [Nat.add_assoc, Nat.add_assoc]
    simp [h] at h_neq
    have h': _ := instruction_toNat_neq_step1 b c e f h_b h_e h_neq
    apply ne_of_add_ne
    have h_factor: 2^32 = 2^16 * 2^16 := by norm_num
    rewrite [h_factor]
    rewrite [Nat.mul_assoc, ←Nat.distrib.left_distrib]
    rewrite [Nat.mul_assoc, ←Nat.distrib.left_distrib]
    simp [*]
  . have h: _ := instruction_toNat_neq_step1 a (b+(2^16)*c) d (e+(2^16)*f) h_a h_d h
    simp [Nat.distrib.left_distrib, ←Nat.add_assoc, ←Nat.mul_assoc] at h
    norm_num at h
    norm_num
    exact h

lemma instruction_toNat_neq_step3 (x₁ x₂ x₃ x₄ y₁ y₂ y₃ y₄: ℕ) (h_x₁: x₁ < 2^16) (h_x₂: x₂ < 2^16) (h_x₃: x₃ < 2^16) (h_y₁: y₁ < 2^16) (h_y₂: y₂ < 2^16) (h_y₃: y₃ < 2^16) (h_neq: x₁≠y₁ ∨ x₂≠y₂ ∨ x₃≠y₃ ∨ x₄≠y₄): x₁+(2^16)*x₂+(2^32)*x₃+(2^48)*x₄ ≠ y₁+(2^16)*y₂+(2^32)*y₃+(2^48)*y₄ := by
  by_cases h: x₁=y₁
  . rewrite [h]
    simp only [Nat.add_assoc, ne_eq, add_right_inj]
    rcases h_neq with h_contr | h_neq₂ | h_neq₃ | h_neq₄
    . aesop
    . have h_neq_2_or_3 : x₂ ≠ y₂ ∨ x₃ ≠ y₃ := by
        left
        exact h_neq₂
      have h: _ := instruction_toNat_neq_step2 x₂ x₃ x₄ y₂ y₃ y₄ h_x₂ h_x₃ h_y₂ h_y₃ h_neq_2_or_3
      have h_factor₁: 2^48 = 2^16 * 2^32 := by norm_num
      have h_factor₂: 2^32 = 2^16 * 2^16 := by norm_num
      simp only [h_factor₁, h_factor₂, Nat.mul_assoc, ←Nat.distrib.left_distrib, mul_eq_mul_left_iff, or_false, ne_eq]
      simp only [Nat.distrib.left_distrib, ←Nat.add_assoc, ←Nat.mul_assoc, ←h_factor₂, h]
    . have h_neq_2_or_3 : x₂ ≠ y₂ ∨ x₃ ≠ y₃ := by
        right
        exact h_neq₃
      have h: _ := instruction_toNat_neq_step2 x₂ x₃ x₄ y₂ y₃ y₄ h_x₂ h_x₃ h_y₂ h_y₃ h_neq_2_or_3
      have h_factor₁: 2^48 = 2^16 * 2^32 := by norm_num
      have h_factor₂: 2^32 = 2^16 * 2^16 := by norm_num
      simp only [h_factor₁, h_factor₂, Nat.mul_assoc, ←Nat.distrib.left_distrib, mul_eq_mul_left_iff, or_false, ne_eq]
      simp only [Nat.distrib.left_distrib, ←Nat.add_assoc, ←Nat.mul_assoc, ←h_factor₂, h]
    . have h_factor₁: 2^48 = 2^16 * 2^32 := by norm_num
      have h_factor₂: 2^32 = 2^16 * 2^16 := by norm_num
      simp only [h_factor₁, h_factor₂, Nat.mul_assoc, ←Nat.distrib.left_distrib, mul_eq_mul_left_iff, or_false, ne_eq]
      by_cases h: x₂=y₂
      . simp [h]
        by_cases h: x₃=y₃
        . simp [h, h_neq₄]
        . exact instruction_toNat_neq_step1 x₃ x₄ y₃ y₄ h_x₃ h_y₃ h
      . exact instruction_toNat_neq_step1 x₂ _ y₂ _ h_x₂ h_y₂ h
  . have h: _ := instruction_toNat_neq_step1 x₁ (x₂+(2^16)*x₃+(2^32)*x₄) y₁ (y₂+(2^16)*y₃+(2^32)*y₄) h_x₁ h_y₁ h
    simp [Nat.distrib.left_distrib, ←Nat.add_assoc, ←Nat.mul_assoc] at h
    norm_num at h
    norm_num
    exact h

lemma Bitvec_toNatr_bij (b1 b2: Bitvec n) : b1.toNatr = b2.toNatr ↔ b1 = b2 := by
  apply Iff.intro
  . exact Bitvec.toNatr_inj
  . intro h
    simp [h]

lemma toNat_neq_of_instruction_eq (i i': Instruction) (h_neq: i ≠ i'): i.toNat ≠ i'.toNat := by
  unfold Instruction.toNat
  apply instruction_toNat_neq_step3
  . exact Bitvec.toNatr_lt i.offDst
  . exact Bitvec.toNatr_lt i.offOp0
  . exact Bitvec.toNatr_lt i.offOp1
  . exact Bitvec.toNatr_lt i'.offDst
  . exact Bitvec.toNatr_lt i'.offOp0
  . exact Bitvec.toNatr_lt i'.offOp1
  . by_cases h_offDst: i.offDst = i'.offDst
    . by_cases h_offOp0: i.offOp0 = i'.offOp0
      . by_cases h_offOp1: i.offOp1 = i'.offOp1
        . by_cases h_flags: i.flags = i'.flags
          . have h_eq: _ := (Instruction.mk.injEq i.offDst i.offOp0 i.offOp1 i.flags i'.offDst i'.offOp0 i'.offOp1 i'.flags).mpr ⟨h_offDst, h_offOp0, h_offOp1, h_flags⟩
            have h_i: i = { offDst := i.offDst, offOp0 := i.offOp0, offOp1 := i.offOp1, flags := i.flags } := by simp
            have h_i': i' = { offDst := i'.offDst, offOp0 := i'.offOp0, offOp1 := i'.offOp1, flags := i'.flags } := by simp
            rewrite [←h_i, ←h_i'] at h_eq
            contradiction
          . right
            right
            right
            exact (Bitvec_toNatr_bij i.flags i'.flags).not.mpr h_flags
        . right
          right
          left
          exact (Bitvec_toNatr_bij i.offOp1 i'.offOp1).not.mpr h_offOp1
      . right
        left
        exact (Bitvec_toNatr_bij i.offOp0 i'.offOp0).not.mpr h_offOp0
    . left
      exact (Bitvec_toNatr_bij i.offDst i'.offDst).not.mpr h_offDst

lemma toNat_feltCast_neq_of_instruction_neq (i i': Instruction) (h_neq: i ≠ i'): ((i.toNat): Felt) ≠ ↑(i'.toNat) := by
  have h_i_range: i.toNat < PRIME := Nat.lt_of_lt_of_le (instruction_toNat_range i) Instruction_le_PRIME
  have h_i'_range: i'.toNat < PRIME := Nat.lt_of_lt_of_le (instruction_toNat_range i') Instruction_le_PRIME
  have h_toNat_neq: i.toNat ≠ i'.toNat := toNat_neq_of_instruction_eq i i' h_neq
  simp [(ZMod.nat_cast_eq_nat_cast_iff' i.toNat i'.toNat _).not, Nat.mod_eq_of_lt h_i_range, Nat.mod_eq_of_lt h_i'_range, h_toNat_neq]

section UInt64
  def uint64sToRegisterState (u: UInt64 × UInt64 × UInt64) : RegisterState Felt := {
    pc := u.1.val,
    ap := u.2.1.val,
    fp := u.2.2.val
  }

  private lemma uint64sToRegisterState_pc_aux (h: uint64ToFelt u = (uint64sToRegisterState s).pc) : u=s.fst := by
    unfold uint64sToRegisterState uint64ToFelt at h
    simp only at h
    injection h with h'
    have h_u: ↑u.val < PRIME := uint64_val_lt_PRIME u
    have h_s: ↑s.fst.val < PRIME := uint64_val_lt_PRIME s.fst
    unfold PRIME at h_u h_s
    simp [Nat.mod_eq_of_lt h_u, Nat.mod_eq_of_lt h_s] at h'
    rcases u with ⟨u_val⟩
    rcases s with ⟨⟨s_val⟩, _⟩
    simp only at *
    have h: u_val = s_val := Fin.eq_of_veq h'
    rw [h]

  lemma uint64sToRegisterState_pc : uint64ToFelt u = (uint64sToRegisterState s).pc ↔ u = s.fst := by
    apply Iff.intro
    . exact uint64sToRegisterState_pc_aux
    . aesop
end UInt64



section UInt256
  def uint256ToInstruction_unchecked (u: UInt256) : Instruction := {
    offDst := Bitvec.ofNatr 16 (u.val % 2 ^ 16)
    offOp0 := Bitvec.ofNatr 16 (u.val / 2^16 % 2^16)
    offOp1 := Bitvec.ofNatr 16 (u.val / 2^32 % 2^16)
    flags := Bitvec.ofNatr 15 (u.val / 2^48 % 2^15)
  }
  def uint256ToInstruction_checked (u: UInt256) : Option Instruction :=
    if u.val < Instruction_range
    then .some (uint256ToInstruction_unchecked u)
    else .none

  lemma uint256ToInstruction_of_in_range (u: UInt256): u.val < Instruction_range ↔ (uint256ToInstruction_checked u).isSome := by
    unfold uint256ToInstruction_checked
    apply Iff.intro
    . aesop
    . split
      case inl h =>
        intro
        exact h
      case inr => simp

  lemma uint256ToFelt_eq_uint256ToInstruction_toNat_cast (x: UInt256) (h_x: x.val < Instruction_range) :
    uint256ToFelt_unchecked x = ↑(Instruction.toNat (uint256ToInstruction_unchecked x)) := by
      unfold uint256ToFelt_unchecked uint256ToInstruction_unchecked Instruction.toNat
      generalize h: (x.val: ℕ) = y
      have h_y: y < Instruction_range := by
        aesop
      unfold Instruction_range at h_y
      simp only [Bitvec.toNatr_ofNatr]
      norm_num
      have h_eq: y = (y % 65536) + 65536 * (y / 65536 % 65536) + 4294967296 * (y / 4294967296 % 65536) + 281474976710656 * (y / 281474976710656 % 32768) := by
        simp [Nat.div_mod_eq_mod_mul_div]
        norm_num
        simp [Nat.mod_eq_of_lt h_y]
        have h': 281474976710656 * (y / 281474976710656) = y - (y % 281474976710656) := by
          have h'': 281474976710656 ∣ (y - y % 281474976710656) := Nat.dvd_sub_mod _
          have h''': y / 281474976710656 = (y - y % 281474976710656) / 281474976710656 := Nat.div_eq_sub_mod_div
          rw [h''', Nat.mul_div_cancel_left' h'']
        rewrite [h', add_comm]
        rewrite [Nat.mod_mul_left_div_self y 65536 65536]
        have h_sub: (y % 65536 + 65536 * (y / 65536 % 65536) + 4294967296 * (y % 281474976710656 / 4294967296)) = y % 281474976710656 := by
          rewrite [Nat.mod_mul_left_div_self y 4294967296 65536]
          have h_factor: 65536 * 65536 = 4294967296 := by norm_num
          rewrite [←h_factor, mul_assoc, add_assoc, ←Nat.distrib.left_distrib]
          have h_factor: 65536 * 65536 * 65536 = 281474976710656 := by norm_num
          rewrite [←h_factor]
          have h'' : y / 65536 % 65536 + 65536 * (y / (65536 * 65536) % 65536) = y / 65536 % (65536 * 65536) := by
            rewrite [←Nat.div_div_eq_div_mul]
            generalize y / 65536 = z
            rewrite [←Nat.mod_add_div (z % (65536 * 65536)) 65536]
            have h_z: z % (65536 * 65536) % 65536 = z % 65536 := Nat.mod_mul_left_mod z 65536 65536
            rewrite [h_z]
            have h_z' : z % (65536 * 65536) / 65536 = z / 65536 % 65536 := Nat.mod_mul_left_div_self z 65536 65536
            rw [h_z']
          rewrite [h'']
          rewrite [Nat.div_mod_eq_mod_mul_div, ←mul_assoc, ←@Nat.mod_mod_of_dvd y 65536 (65536*65536*65536) (by simp)]
          generalize y % (65536*65536*65536) = z
          exact Nat.mod_add_div z 65536
        simp [h_sub]
        symm
        apply Nat.sub_add_cancel
        exact Nat.mod_le y 281474976710656
      rewrite [ZMod.nat_coe_zmod_eq_iff]
      exact ⟨0, by {
        simp [mul_zero, add_zero, ZMod.val_add, ZMod.val_mul, ZMod.val_nat_cast]
        have h_const: (@OfNat.ofNat Felt 65536).val = 65536 := by simp
        rewrite [h_const]
        have h_const: (@OfNat.ofNat Felt 4294967296 ).val = 4294967296  := by simp
        rewrite [h_const]
        have h_const: (@OfNat.ofNat Felt 281474976710656 ).val = 281474976710656  := by simp
        rewrite [h_const]
        have h_mod: ∀ a b : ℕ, (b < PRIME) → (b > 0) → a % b % PRIME = a % b := by
          intro a b h1 h2
          apply Nat.mod_eq_of_lt
          apply Nat.lt_of_lt_of_le
          . exact Nat.mod_lt a h2
          . exact le_of_lt h1
        rewrite [h_mod, h_mod, h_mod]
        . rewrite [←h_eq]
          symm
          apply Nat.mod_eq_of_lt
          apply Nat.lt_of_lt_of_le
          . exact h_y
          . simp
        all_goals simp
      }⟩

end UInt256
