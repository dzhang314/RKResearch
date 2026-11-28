module

public import Mathlib.Algebra.Field.Basic
import Mathlib.Tactic.LinearCombination
import Mathlib.Tactic.Ring

@[expose] public section

namespace RKCert.ReviewedNative.SDIRK8GaussSilentSlope

/-- One live active Gauss hole and one physically silent contributor share
a clock. Only the silent pure slope, not its virtual defect, is recovered. -/
theorem actualSilentSlopeAtGaussHole {K : Type*} [Field K]
    (w₀ w₁ h₀ h₁ v₀ v₁ q : K)
    (hw : w₁ ≠ 0) (hh : h₀ = 0) (hv : v₀ = 0)
    (h : w₀*v₀+w₁*v₁=q*(w₀*h₀+w₁*h₁)) :
    v₁ = q*h₁ := by
  have h' : (v₁-q*h₁)*w₁=0 := by
    linear_combination h - w₀*hv + q*w₀*hh
  exact sub_eq_zero.mp ((mul_eq_zero.mp h').resolve_right hw)

/-- A literal fifth sharing the Gauss-hole clock carries an unknown actual
silent defect. Eliminate it without division by either fifth-read slope. -/
theorem literalSilentFifthEliminate {K : Type*} [Field K]
    (H h T A U V : K) (Hne : H ≠ 0)
    (hT : H*T+U*h=0) (hA : H*A+V*h=0) :
    T*V-A*U=0 := by
  have h' : (T*V-A*U)*H=0 := by
    linear_combination V*hT - U*hA
  exact (mul_eq_zero.mp h').resolve_right Hne

#print axioms actualSilentSlopeAtGaussHole
#print axioms literalSilentFifthEliminate

end RKCert.ReviewedNative.SDIRK8GaussSilentSlope
