module

public import Mathlib.Algebra.Field.Basic
import Mathlib.Tactic.LinearCombination
import Mathlib.Tactic.Ring

@[expose] public section

namespace RKCert.ReviewedNative.SDIRK8CoprimeReversePole

/-- A zero ordinary reverse aggregate at a shared physical pole
does not force equality of the defects. The individual pure reads
satisfy a slope condition on their difference. -/
theorem oppositeSilentDifference {K : Type*} [Field K]
    (w₀ w₁ v₀ v₁ h₀ h₁ q : K)
    (hneq : w₀ ≠ 0)
    (hw : w₀+w₁=0) (hv : w₀*v₀+w₁*v₁=q*(w₀*h₀+w₁*h₁)) :
    v₀-v₁=q*(h₀-h₁) := by
  have h : ((v₀-v₁)-q*(h₀-h₁))*w₀=0 := by
    linear_combination hv-(v₁-q*h₁)*hw
  exact sub_eq_zero.mp ((mul_eq_zero.mp h).resolve_right hneq)

/-- Substitute the linear fourth-clock equation into a marked sixth
read of degree at most two, without an inverse of its actual slope.
A vanishing slope is not silently deemed invertible. -/
theorem clearedFourthClockSubstitution {R : Type*} [CommRing R]
    (J T s a b c : R)
    (hs : T+J*s=0) (h : a+b*s+c*s^2=0) :
    J^2*a-J*T*b+T^2*c=0 := by
  linear_combination J^2*h+((T-J*s)*c-J*b)*hs

/-- Cross-eliminate an unknown affine reverse root from a literal star
tail, without requiring any individual silent stage defect. -/
theorem starProfileRootCross {K : Type*} [Field K]
    (x z g u k h₀ h₁ h₂ : K)
    (hx : x-z ≠ 0)
    (hc : (x-z)*h₁=k*(x-g*u-z)*h₀)
    (hd : (x-z)*h₂=k*(x-g*(2-u)-z)*h₀) :
    (2-u)*h₁-u*h₂+k*(2*u-2)*h₀=0 := by
  have h : ((2-u)*h₁-u*h₂+k*(2*u-2)*h₀)*(x-z)=0 := by
    linear_combination (2-u)*hc-u*hd
  exact (mul_eq_zero.mp h).resolve_right hx

#print axioms oppositeSilentDifference
#print axioms clearedFourthClockSubstitution
#print axioms starProfileRootCross

end RKCert.ReviewedNative.SDIRK8CoprimeReversePole
