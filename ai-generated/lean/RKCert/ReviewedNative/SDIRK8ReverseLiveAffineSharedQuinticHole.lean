module

public import Mathlib.Algebra.Field.Defs
public import Mathlib.Algebra.CharZero.Defs
import Mathlib.Tactic.LinearCombination
import Mathlib.Tactic.Ring

@[expose] public section

namespace RKCert.ReviewedNative.SDIRK8ReverseLiveAffineSharedQuinticHole

/-- If the continued polynomial agrees at an actual ordinary root of the
affine numerator, the same pointwise profile holds even at the hole. -/
theorem rootAgreementReads {R : Type*} [CommRing R] [NoZeroDivisors R]
    (T S h P : R) (hh : S=T*h) (hP : S=T*P)
    (ho : T=0 → h=0) (hp : T=0 → P=0) : h=P := by
  by_cases ht : T=0
  · rw [ho ht,hp ht]
  · have hzero : T*(h-P)=0 := by linear_combination hP-hh
    exact sub_eq_zero.mp ((mul_eq_zero.mp hzero).resolve_left ht)

/-- Four corrected moments, with one true ordinary missing amplitude,
force the coefficients of the reproducing-kernel correction. -/
theorem quarticMomentKernel {K : Type*} [Field K] [CharZero K]
    (a b c d e beta r : K)
    (h₀ : a+b/2+c/3+d/4+e/5=beta)
    (h₁ : a/2+b/3+c/4+d/5+e/6=beta*r)
    (h₂ : a/3+b/4+c/5+d/6+e/7=beta*r^2)
    (h₃ : a/4+b/5+c/6+d/7+e/8=beta*r^3) :
    a=e/70+beta*(16-120*r+240*r^2-140*r^3) ∧
    b=-(2*e/7)+beta*(-120+1200*r-2700*r^2+1680*r^3) ∧
    c=9*e/7+beta*(240-2700*r+6480*r^2-4200*r^3) ∧
    d=-(2*e)+beta*(-140+1680*r-4200*r^2+2800*r^3) := by
  refine ⟨?_,?_,?_,?_⟩
  · linear_combination 16*h₀-120*h₁+240*h₂-140*h₃
  · linear_combination -120*h₀+1200*h₁-2700*h₂+1680*h₃
  · linear_combination 240*h₀-2700*h₁+6480*h₂-4200*h₃
  · linear_combination -140*h₀+1680*h₁-4200*h₂+2800*h₃

/-- Both homogeneous front numerators vanish when the actual early
two-column evaluation has zero determinant. -/
theorem rankLossTwoNumerators {R : Type*} [CommRing R]
    (La Lb Ka Kb Ha Hb α β : R)
    (hA : La*α+Ka*β=Ha) (hB : Lb*α+Kb*β=Hb)
    (hzero : La*Kb-Lb*Ka=0) :
    Ha*Kb-Hb*Ka=0 ∧ La*Hb-Lb*Ha=0 := by
  constructor
  · linear_combination α*hzero-Kb*hA+Ka*hB
  · linear_combination β*hzero-La*hB+Lb*hA

/-- A true ordinarily weighted but reverse-zero eighth in the arithmetic
rear forces the cubic rear coefficient to vanish. -/
theorem arithmeticRearHoleGap {R : Type*} [CommRing R] [NoZeroDivisors R]
    (x c d z k J hc hx : R) (hd : d=2*c-x)
    (hk : k≠0) (hx₀ : hx≠0) (hdz : d≠z)
    (hpen : (x-z)*hc=k*(c-z)*hx)
    (hrear : 2*J*hc-k*J*hx=0) : J=0 := by
  have hz : k*J*(d-z)*hx=0 := by
    rw [hd]
    linear_combination (x-z)*hrear-2*J*hpen
  exact (mul_eq_zero.mp ((mul_eq_zero.mp
    ((mul_eq_zero.mp hz).resolve_right hx₀)).resolve_right (sub_ne_zero.mpr hdz))).resolve_left hk

#print axioms rootAgreementReads
#print axioms quarticMomentKernel
#print axioms rankLossTwoNumerators
#print axioms arithmeticRearHoleGap

end RKCert.ReviewedNative.SDIRK8ReverseLiveAffineSharedQuinticHole
