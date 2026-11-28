module

public import Mathlib.Algebra.Field.Basic
import Mathlib.Tactic.LinearCombination
import Mathlib.Tactic.Ring

@[expose] public section

namespace RKCert.ReviewedNative.SDIRK8CenteredStarRead

/-- Sum and difference of the two physical star-tail comparisons pin
the centered affine slope and its polynomial gap condition. -/
theorem centeredStarFromActualTail {K : Type*} [Field K]
    (T p γ v q A B : K) (hp : p ≠ 0)
    (hc : T*(p-γ*(1+v)*q)=p*A)
    (hd : T*(p-γ*(1-v)*q)=p*B) :
    2*γ*T*q=(2*T-A-B)*p ∧ v*(2*T-A-B)=B-A := by
  have hsum : 2*γ*T*q=(2*T-A-B)*p := by linear_combination -hc-hd
  have hdiff : 2*γ*v*T*q=p*(B-A) := by linear_combination hd-hc
  have h : (v*(2*T-A-B)-(B-A))*p=0 := by
    linear_combination hdiff-v*hsum
  exact ⟨hsum,sub_eq_zero.mp ((mul_eq_zero.mp h).resolve_right hp)⟩

#print axioms centeredStarFromActualTail

end RKCert.ReviewedNative.SDIRK8CenteredStarRead
