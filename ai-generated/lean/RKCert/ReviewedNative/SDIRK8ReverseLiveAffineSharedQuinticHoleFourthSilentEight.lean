module

public import Mathlib.LinearAlgebra.Matrix.Adjugate
import Mathlib.Algebra.BigOperators.Fin
import Mathlib.Tactic.LinearCombination
import Mathlib.Tactic.Ring

@[expose] public section

namespace RKCert.ReviewedNative.SDIRK8ReverseLiveAffineSharedQuinticHoleFourthSilentEight

open scoped Matrix BigOperators

/-- Combining the paid terminal weight row and the actual silent-eighth
gap clears the profile values from the known-peg coefficient row. It
divides neither by u-2 nor by the actual silent eighth amplitude. -/
theorem reducedSilentEightWeightRow {R : Type*} [CommRing R] [NoZeroDivisors R]
    (γ u k x c a b Hc Hx Rc Rx : R)
    (hγ : γ≠0) (hu : u≠0) (hHx : Hx≠0)
    (hclock : c=x-γ*u)
    (hgap : (u-2)*Hc=(2*u+k*(u-2))*Hx)
    (hweight : Hc*(c-a)*(c-b)*(c-x)*Rc=Hx*(x-a)*(x-b)*(x-c)*Rx) :
    (2*u+k*(u-2))*(c-a)*(c-b)*Rc+(u-2)*(x-a)*(x-b)*Rx=0 := by
  have hzero : (γ*u*Hx)*
      ((2*u+k*(u-2))*(c-a)*(c-b)*Rc+(u-2)*(x-a)*(x-b)*Rx)=0 := by
    rw [hclock] at hweight ⊢
    linear_combination -(u-2)*hweight-(γ*u)*(x-γ*u-a)*(x-γ*u-b)*Rc*hgap
  exact (mul_eq_zero.mp hzero).resolve_left (mul_ne_zero (mul_ne_zero hγ hu) hHx)

/-- Four known ordinary nonhole pegs leave a monic cubic. The three
signed coefficient rows and the paid terminal row must have zero
determinant, without an early or signed Cramer pivot. -/
theorem monicCubicFourRows {R : Type*} [CommRing R]
    (M : Matrix (Fin 4) (Fin 4) R) (r₀ r₁ r₂ : R)
    (h : ∀ i, M i 0*r₀+M i 1*r₁+M i 2*r₂+M i 3=0) :
    M.det=0 := by
  let v : Fin 4 → R := ![r₀,r₁,r₂,1]
  apply Matrix.det_eq_zero_of_mulVec_eq_zero_of_mem_nonZeroDivisors
    (v := v) (i := 3)
  · funext i
    change (∑ j, M i j*v j)=0
    simpa [Fin.sum_univ_succ,v,add_assoc] using h i
  · simp [v]

/-- Only the two true literal fifth pads are canceled here. No pad at
the fourth-hole clock is assumed. -/
theorem cancelFifthTwoPads {R : Type*} [CommRing R] [NoZeroDivisors R]
    (Y A B G : R) (hA : Y≠A) (hB : Y≠B)
    (h : (Y-A)*(Y-B)*G=0) : G=0 := by
  exact (mul_eq_zero.mp h).resolve_left
    (mul_ne_zero (sub_ne_zero.mpr hA) (sub_ne_zero.mpr hB))

#print axioms reducedSilentEightWeightRow
#print axioms monicCubicFourRows
#print axioms cancelFifthTwoPads

end RKCert.ReviewedNative.SDIRK8ReverseLiveAffineSharedQuinticHoleFourthSilentEight
