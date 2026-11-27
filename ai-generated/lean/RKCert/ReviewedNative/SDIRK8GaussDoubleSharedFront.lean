module

public import Mathlib.Algebra.Field.Basic
import Mathlib.Tactic.LinearCombination
import Mathlib.Tactic.Ring

@[expose] public section

namespace RKCert.ReviewedNative.SDIRK8GaussDoubleSharedFront

/-- A physically doubled silent clock may transport an affine fifth-row
read by weighted averaging, without forcing either of its cubic
defects to equal the virtual one. -/
theorem affineVirtualRead {K : Type*} [Field K]
    (w₀ w₁ h₀ h₁ h v₀ v₁ a b q : K)
    (hw : w₀+w₁ ≠ 0)
    (hh : w₀*h₀+w₁*h₁=(w₀+w₁)*h)
    (hv₀ : v₀=a+b*h₀) (hv₁ : v₁=a+b*h₁)
    (hv : w₀*v₀+w₁*v₁=(w₀+w₁)*q*h) :
    a+b*h=q*h := by
  have h' : (a+b*h-q*h)*(w₀+w₁)=0 := by
    linear_combination hv-w₀*hv₀-w₁*hv₁-b*hh
  exact sub_eq_zero.mp ((mul_eq_zero.mp h').resolve_right hw)

/-- Known normalized reverse-root clock, without normalized weights at
the physical silent eighth. This is the cleared diagonal gauge. -/
theorem silentEighthDiagonalGauge {K : Type*} [CommRing K]
    (g Z u k : K)
    (h : 2*(g*Z-(1-g))=g*k*(u-2)) :
    2*g*(1+Z)-g*k*(u-2)=2 := by
  linear_combination h

/-- Comparing paid first and second cubic-defect moments with a
singleton profile gives a mass condition at the actual double.
The two physical amplitudes, not their ordinary aggregate, appear. -/
theorem repeatedClockMass {K : Type*} [CommRing K]
    (w b₀ b₁ h₀ h₁ p ν : K)
    (hw : w=b₀+b₁)
    (h₁read : b₀*h₀+b₁*h₁=(w-ν)*p)
    (h₂read : b₀*h₀^2+b₁*h₁^2=(w-ν)*p^2) :
    w*(p-h₀)*(p-h₁)=ν*p*(p-h₀-h₁) := by
  linear_combination (h₀+h₁)*h₁read - h₂read + h₀*h₁*hw

#print axioms affineVirtualRead
#print axioms silentEighthDiagonalGauge
#print axioms repeatedClockMass

end RKCert.ReviewedNative.SDIRK8GaussDoubleSharedFront
