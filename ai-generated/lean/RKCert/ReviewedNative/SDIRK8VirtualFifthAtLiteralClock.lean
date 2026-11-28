module

public import Mathlib.Algebra.Field.Basic
import Mathlib.Tactic.LinearCombination
import Mathlib.Tactic.Ring

@[expose] public section

namespace RKCert.ReviewedNative.SDIRK8VirtualFifthAtLiteralClock

/-- Literal fifth's two pure reads are affine in the actual defect at a
fixed clock. An earlier literal at that clock has the padded read, so
their weighted virtual profile satisfies the same literal scalar read. -/
theorem weightedActualAffineRead {K : Type*} [Field K]
    (w₀ w₁ h₀ h₁ v₀ v₁ hv vv T D : K)
    (hw : w₀+w₁ ≠ 0)
    (hh : w₀*h₀+w₁*h₁=(w₀+w₁)*hv)
    (hv' : w₀*v₀+w₁*v₁=(w₀+w₁)*vv)
    (h₀' : v₀=T+D*h₀) (h₁' : v₁=T+D*h₁) :
    vv=T+D*hv := by
  have h : (vv-(T+D*hv))*(w₀+w₁)=0 := by
    linear_combination w₀*h₀' + w₁*h₁' + D*hh - hv'
  exact sub_eq_zero.mp ((mul_eq_zero.mp h).resolve_right hw)

#print axioms weightedActualAffineRead

end RKCert.ReviewedNative.SDIRK8VirtualFifthAtLiteralClock
