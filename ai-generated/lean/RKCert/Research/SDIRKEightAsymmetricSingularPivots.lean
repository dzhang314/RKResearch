module

public import Mathlib.Algebra.Field.Basic
public import Mathlib.Data.Nat.GCD.Basic
import Mathlib.Tactic.LinearCombination
import Mathlib.Tactic.Ring

@[expose] public section

/-! # Actual singular second-gap equations in the asymmetric graph -/

namespace RKResearch.Certified.SDIRKEightAsymmetricSingularPivots

theorem gap_singular {K : Type*} [Field K] {γ k q : K}
    (h₂ : (2 : K) ≠ 0) (hg : γ ≠ 0)
    (hD : (2*γ-1)^2+k*(2*γ-1)+q+4*γ^2=0)
    (hU : 2*((2*γ-1)^2+k*(2*γ-1)+q)-2*γ*(4*γ-2+k)=0) :
    k=2-8*γ ∧ q=8*γ^2-8*γ+1 := by
  have hh : (2*γ)*(8*γ-2+k)=0 := by linear_combination 2*hD-hU
  have hz := (mul_eq_zero.mp hh).resolve_left (mul_ne_zero h₂ hg)
  have hk : k=2-8*γ := by linear_combination hz
  rw [hk] at hD
  exact ⟨hk,by linear_combination hD⟩

theorem opposite_gaps_nonsingular {K : Type*} [Field K] {γ k : K}
    (h₂ : (2 : K) ≠ 0) (hg : γ ≠ 0) (hk : k ≠ 0)
    (a : 2*γ*(8*γ-2+k)=0) (b : 2*γ*(8*γ-2-k)=0) : False := by
  have s := (mul_eq_zero.mp a).resolve_left (mul_ne_zero h₂ hg)
  have t := (mul_eq_zero.mp b).resolve_left (mul_ne_zero h₂ hg)
  have c : (2 : K)*k=0 := by linear_combination s-t
  exact (mul_ne_zero h₂ hk) c

theorem gap_anchor_support : (13^3*131^3 : ℕ)=4939055927 := by decide +kernel

end RKResearch.Certified.SDIRKEightAsymmetricSingularPivots
