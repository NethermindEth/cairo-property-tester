import Mathlib.Data.ZMod.Basic

def PRIME := 3618502788666131213697322783095070105623107215331596699973092056135872020481
abbrev Felt := ZMod PRIME
axiom P_PRIME : Nat.Prime PRIME
instance: Fact PRIME.Prime := fact_iff.mpr P_PRIME
