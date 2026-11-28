import Mathlib.Tactic.Ring.Basic

/-! Scalar symmetry and two-point Vieta receipts for the all-dirty clock census. -/
namespace RKResearch.Certified.SDIRKEightAllDirtyClockCensus

variable {R : Type*} [CommRing R]

theorem symmetric_intercept [IsDomain R] {p q a b h : R}
    (hq : q ≠ 0) (h₂ : (2 : R) ≠ 0)
    (h₀ : p=(a*h+b)*q) (h₁ : -p=(-(a*h)+b)*q) : b=0 := by
  have z : (2:R)*b*q=0 := by
    calc
      _ = (a*h+b)*q+(-(a*h)+b)*q := by ring1
      _ = 0 := by rw [← h₀, ← h₁]; ring1
  exact (mul_eq_zero.mp ((mul_eq_zero.mp z).resolve_right hq)).resolve_left h₂

theorem same_clock_product [IsDomain R] {ell A B g h : R}
    (hd : g ≠ h)
    (h₀ : ell=g*(A+B*g)) (h₁ : ell=h*(A+B*h)) :
    ell = -(B*g*h) := by
  have z : (g-h)*(A+B*(g+h))=0 := by
    calc
      _ = g*(A+B*g)-h*(A+B*h) := by ring1
      _ = 0 := by rw [← h₀, ← h₁, sub_self]
  have ha : A+B*(g+h)=0 :=
    (mul_eq_zero.mp z).resolve_left (sub_ne_zero.mpr hd)
  have hh : A=-(B*(g+h)) := by
    calc
      _ = (A+B*(g+h))-(B*(g+h)) := by ring1
      _ = _ := by rw [ha, zero_sub]
  rw [h₀,hh]
  ring1

theorem reflected_scale_fit (a p b lam : R) :
    lam*(lam*(a-b*p))=lam^2*a-(lam^2*b)*p := by
  ring1

end RKResearch.Certified.SDIRKEightAllDirtyClockCensus
