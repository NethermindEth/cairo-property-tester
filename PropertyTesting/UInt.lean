import PropertyTesting.Felt
import Verification.Semantics.Cpu

section UInt64
  def uint64ToFelt (u: UInt64) : Felt := u.val

  lemma uint64Size_lt_PRIME : UInt64.size < PRIME := by simp
  lemma uint64Size_le_PRIME : UInt64.size ≤ PRIME := by simp

  lemma uint64_val_lt_PRIME (u: UInt64) : ↑u.val < PRIME :=
    Nat.lt_of_lt_of_le u.val.isLt uint64Size_le_PRIME

  lemma uint64ToFelt_eq_cast (u: UInt64) : uint64ToFelt u = ↑↑u.val := rfl
  lemma uint64ToFelt_inj (h: uint64ToFelt u = uint64ToFelt v): u = v := by
    unfold uint64ToFelt at h
    injection h with h
    have h_u: _ := Nat.lt_of_lt_of_le u.val.2 uint64Size_le_PRIME
    have h_v: _ := Nat.lt_of_lt_of_le v.val.2 uint64Size_le_PRIME
    unfold PRIME at h_u h_v
    simp [Nat.mod_eq_of_lt h_u, Nat.mod_eq_of_lt h_v] at h
    have h: u.val = v.val := (Fin.val_eq_val u.val v.val).mp h
    have h: {val:= u.val: UInt64} = {val:= v.val: UInt64} := by aesop
    have h_u : {val:=u.val:UInt64} = u := by simp
    have h_v : {val:=v.val:UInt64} = v := by simp
    rewrite [←h_u]
    rewrite [←h_v]
    exact h
end UInt64



section UInt256
  -- May need to store this as four UInt64s for efficiency
  def UInt256.size : Nat := 115792089237316195423570985008687907853269984665640564039457584007913129639936
  structure UInt256 where
    val : Fin UInt256.size

  def uint256ToFelt_unchecked (u: UInt256): Felt := u.val
  def uint256ToFelt_checked (u: UInt256): Option Felt :=
    if u.val < PRIME
    then .some u.val
    else .none

  lemma uint256ToFelt_checked_range: uint256ToFelt_checked u = some x ↔ u.val < PRIME ∧ u.val=x := by
    unfold uint256ToFelt_checked
    aesop
end UInt256



