module

public import Mathlib.Algebra.Field.Basic
public import Mathlib.Data.Nat.GCD.Basic
public import Mathlib.Data.ZMod.Basic
import Mathlib.Tactic.LinearCombination
import Mathlib.Tactic.Ring

@[expose] public section

/-! # Small native receipts for the asymmetric supported midpoint exclusion -/

namespace RKResearch.Certified.SDIRKEightAsymmetricMidpoint

theorem noncentral_opposite_reject {K : Type*} [Field K] {k x z : K}
    (h₄ : (4 : K) ≠ 0) (h₅ : (5 : K) ≠ 0)
    (hk : k^2=1) (hx : x^2-k*x-1=0) (hz : z=k-x)
    (hg : 1+2*(k-2)*(x-k) = -1-2*(k+2)*(z-k)) : False := by
  rw [hz] at hg
  have hn : (4 : K)*(k-2*x)=0 := by linear_combination hg+2*hk
  have he : k=2*x := sub_eq_zero.mp ((mul_eq_zero.mp hn).resolve_left h₄)
  rw [he] at hk hx
  apply h₅
  linear_combination -4*hx-hk

theorem nonsquare_f13 : ∀ y : ZMod 13, y^2 ≠ 5 := by decide +kernel

theorem singular_gap_prime_support :
    Nat.gcd 219735220141 3139321086281830924014713=1 := by decide +kernel

end RKResearch.Certified.SDIRKEightAsymmetricMidpoint
