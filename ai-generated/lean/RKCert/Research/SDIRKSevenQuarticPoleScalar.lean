module

public import RKCert.Research.SDIRKSevenChristoffelScalar
import Mathlib.Tactic.LinearCombination
import Mathlib.Tactic.Ring

@[expose] public section

/-! # Scalar payments for a quartic cubic-defect profile divided by an affine pole -/

namespace RKResearch.Certified.SDIRKSevenQuarticPoleScalar
open scoped BigOperators

def q4 {R : Type*} [CommRing R] (g₀ g₁ g₂ g₃ g₄ x : R) : R :=
  g₀+g₁*x+g₂*x^2+g₃*x^3+g₄*x^4

section moments
variable {R I : Type*} [CommRing R] [Fintype I]

def rawMoment (y p : I→R) (k : ℕ) : R := ∑ i, p i*y i^k

private theorem two_affine {y p : I→R} (paid : ∀ k≤5,rawMoment y p k=0)
    (a b c d : R) (k : ℕ) (hk : k≤3) :
    (∑ i, p i*y i^k*(a+b*y i)*(c+d*y i))=0 := by
  have h : (∑ i,p i*y i^k*(a+b*y i)*(c+d*y i)) =
      a*c*rawMoment y p k+(a*d+b*c)*rawMoment y p (k+1)+b*d*rawMoment y p (k+2) := by
    simp only [rawMoment,Finset.mul_sum,←Finset.sum_add_distrib,pow_add,pow_one]
    apply Finset.sum_congr rfl
    intro i _
    ring
  rw [h,paid k (by omega),paid (k+1) (by omega),paid (k+2) (by omega)]
  ring

private theorem quartic_moment {y p : I→R} (paid : ∀ k≤5,rawMoment y p k=0)
    (a b c d e : R) (k : ℕ) (hk : k≤1) :
    (∑ i, p i*y i^k*q4 a b c d e (y i))=0 := by
  have h : (∑ i,p i*y i^k*q4 a b c d e (y i)) =
      a*rawMoment y p k+b*rawMoment y p (k+1)+c*rawMoment y p (k+2)+
      d*rawMoment y p (k+3)+e*rawMoment y p (k+4) := by
    simp only [rawMoment,q4,Finset.mul_sum,←Finset.sum_add_distrib,pow_add,pow_one]
    apply Finset.sum_congr rfl
    intro i _
    ring
  rw [h,paid k (by omega),paid (k+1) (by omega),paid (k+2) (by omega),
    paid (k+3) (by omega),paid (k+4) (by omega)]
  ring

/-- After the exact nodal relations are supplied, all required Gram and
adjoint payments for this profile are consequences of degree-five
barycentric moments. This calculation does not divide by a mass. -/
theorem quartic_pole_payments {y p b D V : I→R}
    (paid : ∀ k≤5,rawMoment y p k=0)
    (w₀ w₁ l₀ l₁ a b' c d e τ : R)
    (hD : ∀ i,D i=τ*p i*(w₀+w₁*y i))
    (hV : ∀ i,(w₀+w₁*y i)*V i=q4 a b' c d e (y i))
    (hb : ∀ i,b i*V i=τ*p i*(w₀+w₁*y i)*(l₀+l₁*y i)) :
    (∀ k≤3,(∑ i,b i*y i^k*V i)=0) ∧
    (∑ i,b i*(V i)^2)=0 ∧ (∑ i,D i*V i)=0 ∧
      (∑ i,D i*y i*V i)=0 := by
  have mm₀ := quartic_moment paid a b' c d e 0 (by decide)
  have mm₁ := quartic_moment paid a b' c d e 1 (by decide)
  simp only [pow_zero,mul_one,pow_one] at mm₀ mm₁
  have ld :
      (∑ i,τ*p i*q4 a b' c d e (y i)*(l₀+l₁*y i))=0 := by
    calc
      (∑ i,τ*p i*q4 a b' c d e (y i)*(l₀+l₁*y i)) =
          τ*(l₀*(∑ i,p i*q4 a b' c d e (y i))+
            l₁*(∑ i,p i*y i*q4 a b' c d e (y i))) := by
        simp only [Finset.mul_sum,←Finset.sum_add_distrib]
        apply Finset.sum_congr rfl
        intro i _
        ring
      _=0 := by rw [mm₀,mm₁]; ring
  refine ⟨?_,?_,?_,?_⟩
  · intro k hk
    calc
      (∑ i,b i*y i^k*V i)=τ*(∑ i,p i*y i^k*(w₀+w₁*y i)*(l₀+l₁*y i)) := by
        rw [Finset.mul_sum]
        apply Finset.sum_congr rfl
        intro i _
        rw [show b i*y i^k*V i=(b i*V i)*y i^k by ring,hb]
        ring
      _=0 := by rw [two_affine paid _ _ _ _ _ hk,mul_zero]
  · convert ld using 1
    apply Finset.sum_congr rfl
    intro i _
    rw [show b i*(V i)^2=(b i*V i)*V i by ring,hb]
    rw [show τ*p i*(w₀+w₁*y i)*(l₀+l₁*y i)*V i =
      τ*p i*((w₀+w₁*y i)*V i)*(l₀+l₁*y i) by ring,hV]
  · calc
      (∑ i,D i*V i)=τ*(∑ i,p i*q4 a b' c d e (y i)) := by
        rw [Finset.mul_sum]
        apply Finset.sum_congr rfl
        intro i _
        rw [hD,mul_assoc,hV]
        ring
      _=0 := by rw [mm₀,mul_zero]
  · calc
      (∑ i,D i*y i*V i)=τ*(∑ i,p i*y i*q4 a b' c d e (y i)) := by
        rw [Finset.mul_sum]
        apply Finset.sum_congr rfl
        intro i _
        rw [hD,show τ*p i*(w₀+w₁*y i)*y i*V i =
          τ*p i*y i*((w₀+w₁*y i)*V i) by ring,hV]
        ring
      _=0 := by rw [mm₁,mul_zero]

end moments

/-- Reflected terminal interpolation produces an M-independent fourth
quadratic after the known cubic chronological factor is removed. -/
theorem reflection_quartic_fourth {R : Type*} [CommRing R]
    (a b c d M Y : R) :
    let g := q4 a b c d 1 Y
    let T := (M+a+b+2*c+6*d+20)*Y^2+
       (M*d+4*M-4*a-3*b-4*c-10*d-32)*Y+
       (-M*a-M*b-M*c-2*M*d-6*M+3*a+2*b+2*c+4*d+12)
    (Y^3-9*Y^2+18*Y-6)*T+(5*M-4+(4-M)*Y)*g =
      (Y-1)*(Y^2-4*Y+2-M)*(
        (a+b+2*c+6*d+24)*Y^2+(-8*a-7*b-12*c-30*d-96)*Y+
          11*a+6*b+6*c+12*d+36) := by
  simp only [q4]
  ring

/-- The centered multiplier zero cannot occupy the last reflected site
of the rational reflection suffix: its fourth candidate never splits. -/
theorem centered_last_reflection_gate {c : ℚ} (h : 5*c^2-19*c+10=0) : False := by
  have sq : (10*c-19)^2=161 := by linear_combination 20*h
  have ns : ¬ IsSquare (161:ℕ) := by
    rintro ⟨n,hn⟩
    by_cases big : 13≤n
    · have h0 : 169≤n*n := Nat.mul_le_mul big big
      omega
    · have lo : n≤12 := by omega
      have h0 : n*n≤144 := Nat.mul_le_mul lo lo
      omega
  exact ((Rat.isSquare_natCast_iff (n:=161)).not.mpr ns)
    ⟨10*c-19,by linear_combination -sq⟩

end RKResearch.Certified.SDIRKSevenQuarticPoleScalar
