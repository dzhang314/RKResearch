module

public import Mathlib.Algebra.Ring.Basic
import Mathlib.Tactic.LinearCombination
import Mathlib.Tactic.Ring

@[expose] public section

namespace RKCert.ReviewedNative.SDIRK8ReverseLiveAffineQuarticLiteral

/-- The two actual literal scalar reads identify the cleared affine
reverse numerator, regardless of whether one row has zero ordinary weight. -/
theorem identifyAffineNumerator {R : Type*} [CommRing R]
    (A B a b Lₐ Lᵦ q₀ q₁ Y : R)
    (hA : a*(q₀+q₁*A)=Lₐ) (hB : b*(q₀+q₁*B)=Lᵦ) :
    B*b*Lₐ-A*a*Lᵦ+(a*Lᵦ-b*Lₐ)*Y =
      (B-A)*a*b*(q₀+q₁*Y) := by
  rw [← hA, ← hB]
  ring

/-- At an interpolated actual site, coprimeness prevents any pole,
so the actual profile is never lost when clearing a local denominator. -/
theorem noActualSitePole {R : Type*} [CommRing R]
    (T S h : R) (hS : S=T*h) (hcoprime : T≠0 ∨ S≠0) : T≠0 := by
  rcases hcoprime with hT | hS₀
  · exact hT
  · intro hT
    apply hS₀
    rw [hS, hT, zero_mul]

/-- Deflation at an ordinary node uses the actual silent reverse clock.
No factor from a derivative or weight is divided out here. -/
theorem ordinaryDeflation {R : Type*} [CommRing R] [NoZeroDivisors R]
    (c z d b h μ T : R) (hcz : c≠z)
    (hread : b*h*((c-z)*d)=μ*(c-z)*T) : d*b*h=μ*T := by
  have hzero : (c-z)*(d*b*h-μ*T)=0 := by linear_combination hread
  exact sub_eq_zero.mp ((mul_eq_zero.mp hzero).resolve_left (sub_ne_zero.mpr hcz))

/-- Remove only the two actual literal padded roots of the fourth-row
quartic. The formula includes a vanishing or degree-dropping quadratic. -/
theorem literalQuarticQuotient {R : Type*} [CommRing R] [NoZeroDivisors R]
    (A B c₀ c₁ c₂ c₃ c₄ : R) (hAB : A≠B)
    (F : R → R) (hF : ∀ y, F y=c₀+c₁*y+c₂*y^2+c₃*y^3+c₄*y^4)
    (hA : F A=0) (hB : F B=0) (Y : R) :
    F Y=(Y-A)*(Y-B)*(c₂+c₃*(Y+A+B)+c₄*(Y^2+(A+B)*Y+A^2+A*B+B^2)) := by
  let Q := c₂+c₃*(Y+A+B)+c₄*(Y^2+(A+B)*Y+A^2+A*B+B^2)
  have h₀ : (B-A)*(F Y-(Y-A)*(Y-B)*Q)=(B-Y)*F A+(Y-A)*F B := by
    rw [hF Y, hF A, hF B]
    dsimp [Q]
    ring
  rw [hA, hB, mul_zero, mul_zero, add_zero] at h₀
  exact sub_eq_zero.mp ((mul_eq_zero.mp h₀).resolve_left (sub_ne_zero.mpr hAB.symm))

/-- Homogeneous rear comparison at the actual ordinarily silent clock. -/
theorem clearLiteralRear {R : Type*} [CommRing R]
    (x c z k qₓ qC pₓ pC hₓ hC : R)
    (hx : qₓ*hₓ=pₓ) (hc : qC*hC=pC)
    (h : (x-z)*hC=k*(c-z)*hₓ) :
    (x-z)*pC*qₓ=k*(c-z)*pₓ*qC := by
  rw [← hx, ← hc]
  linear_combination (qₓ*qC)*h

/-- Both rear phase equations fit this one formally checked
denominator clearing, which imposes no generic leading assumptions. -/
theorem clearThreeReadTail {R : Type*} [CommRing R]
    (a b c q₁ q₂ q₃ p₁ p₂ p₃ h₁ h₂ h₃ : R)
    (h₁read : q₁*h₁=p₁) (h₂read : q₂*h₂=p₂) (h₃read : q₃*h₃=p₃)
    (h : a*h₁+b*h₂+c*h₃=0) :
    a*p₁*q₂*q₃+b*p₂*q₁*q₃+c*p₃*q₁*q₂=0 := by
  rw [← h₁read, ← h₂read, ← h₃read]
  linear_combination (q₁*q₂*q₃)*h

/-- The actual fifth determinant is linear in its own amplitude:
homogeneous evaluation at a rational profile uses the actual numerator. -/
theorem clearLinearFifth {R : Type*} [CommRing R]
    (F₀ F₁ q N h : R) (hread : q*h=N) (hzero : F₀+F₁*h=0) :
    q*F₀+F₁*N=0 := by
  rw [← hread]
  linear_combination q*hzero

#print axioms identifyAffineNumerator
#print axioms noActualSitePole
#print axioms ordinaryDeflation
#print axioms literalQuarticQuotient
#print axioms clearLiteralRear
#print axioms clearThreeReadTail
#print axioms clearLinearFifth

end RKCert.ReviewedNative.SDIRK8ReverseLiveAffineQuarticLiteral
