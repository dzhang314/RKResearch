module

public import Mathlib.Algebra.Ring.Basic
import RKCert.ReviewedNative.SDIRK8ArithmeticLiteralFourthProfilePivot
import Mathlib.Tactic.Ring

@[expose] public section

namespace RKCert.ReviewedNative.SDIRK8ArithmeticLiteralSilentFifth

open SDIRK8ArithmeticLiteralFourthProfilePivot

/-- The actual silent fifth, not a missing ordinary root, obeys the
homogeneous literal cubic forced by its paid affine reverse read. -/
theorem actualSilentFifthGate {R : Type*} [CommRing R] [NoZeroDivisors R]
    (g u k x c z Y Hc Hx L f₀ f₁ f₂ f₃ : R)
    (hg : g≠0) (hu : u≠0) (hk : k≠0) (hHx : Hx≠0)
    (hc : c=x-g*u) (hz : z=g*Y) (hL : Hc-k*Hx=u*L)
    (ha : (x-z)*Hc=k*(c-z)*Hx)
    (hf : f₀+f₁*Y+f₂*Y^2+f₃*Y^3=0) :
    L≠0 ∧
      f₀*(g*L)^3 + f₁*(x*L+g*k*Hx)*(g*L)^2
      + f₂*(x*L+g*k*Hx)^2*(g*L) + f₃*(x*L+g*k*Hx)^3=0 := by
  obtain ⟨hL0, hY⟩ :=
    silentClockHomogeneous g u k x c z Y Hc Hx L hg hu hk hHx hc hz hL ha
  exact ⟨hL0, homogeneousCubic _ _ _ _ _ _ _ hY hf⟩

/-- An actual ordinary fourth and an independently reverse-live silent
fifth are distinct even after the latter's clock is homogenized. -/
theorem ordinaryFourthDistinctFromSilentFifth {R : Type*} [CommRing R]
    [NoZeroDivisors R] (g s Y d n q z : R)
    (hd : d≠0) (hq : q=g*s) (hz : z=g*Y) (hqz : q≠z)
    (hY : d*Y=n) : d*s-n≠0 := by
  have hs : s≠Y := by
    intro h
    apply hqz
    rw [hq, hz, h]
  rw [← hY, ← mul_sub]
  exact mul_ne_zero hd (sub_ne_zero.mpr hs)

/-- The two saturated inputs may remove the primitive tail pivot
only on the genuine nonzero-pivot branch. -/
theorem cancelPrimitivePivotPowers {R : Type*} [CommRing R]
    [NoZeroDivisors R] (g F₁ r N Q A B : R)
    (hf : F₁=g*r) (hf₀ : F₁≠0)
    (hN : N=r*A) (hQ : Q=r^3*B) (hzN : N=0) (hzQ : Q=0) :
    A=0 ∧ B=0 := by
  have hr : r≠0 := by
    intro h
    apply hf₀
    rw [hf, h, mul_zero]
  exact ⟨(mul_eq_zero.mp (hN.symm.trans hzN)).resolve_left hr,
         (mul_eq_zero.mp (hQ.symm.trans hzQ)).resolve_left (pow_ne_zero _ hr)⟩

#print axioms actualSilentFifthGate
#print axioms ordinaryFourthDistinctFromSilentFifth
#print axioms cancelPrimitivePivotPowers

end RKCert.ReviewedNative.SDIRK8ArithmeticLiteralSilentFifth
