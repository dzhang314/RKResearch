import Mathlib.Tactic.Ring

namespace RKResearch.Certified.ERK10FifteenPureDonorLeakageScalars

variable {K : Type*} [Field K]

theorem forced_sums_and_square (a d e : K)
    (ha : a ≠ 0) (h3 : (3:K) ≠ 0) (h19 : (19:K) ≠ 0)
    (hP : 110*a^2-87*a*(d+e)+60*d*e = 0)
    (hN : 17*a^2-15*a*(d+e)+11*d*e = 0) :
    3*(d+e)=10*a ∧ d*e=3*a^2 ∧ (3*d-5*a)^2= -(2:K)*a^2 := by
  have h1 : (19:K)*a*(10*a-3*(d+e)) = 0 := by
    calc
      _ = 11*(110*a^2-87*a*(d+e)+60*d*e) -
          60*(17*a^2-15*a*(d+e)+11*d*e) := by ring
      _ = 0 := by simp [hP,hN]
  have h2 : (3:K)*19*(3*a^2-d*e) = 0 := by
    calc
      _ = 15*(110*a^2-87*a*(d+e)+60*d*e) -
          87*(17*a^2-15*a*(d+e)+11*d*e) := by ring
      _ = 0 := by simp [hP,hN]
  have hS := (sub_eq_zero.mp ((mul_eq_zero.mp h1).resolve_left (mul_ne_zero h19 ha))).symm
  have hD := (sub_eq_zero.mp ((mul_eq_zero.mp h2).resolve_left (mul_ne_zero h3 h19))).symm
  refine ⟨hS,hD,?_⟩
  apply sub_eq_zero.mp
  calc
    _ = 3*d*(3*(d+e)-10*a) - 9*(d*e-3*a^2) := by ring
    _ = 0 := by simp [hS,hD]

theorem requires_sqrt_neg_two (a d e : K)
    (ha : a ≠ 0) (h3 : (3:K) ≠ 0) (h19 : (19:K) ≠ 0)
    (hP : 110*a^2-87*a*(d+e)+60*d*e = 0)
    (hN : 17*a^2-15*a*(d+e)+11*d*e = 0) :
    ∃ z : K, z^2 = -2 := by
  obtain ⟨_,_,hs⟩ := forced_sums_and_square a d e ha h3 h19 hP hN
  refine ⟨(3*d-5*a)/a,?_⟩
  rw [div_pow]
  exact (div_eq_iff (pow_ne_zero 2 ha)).2 hs

end RKResearch.Certified.ERK10FifteenPureDonorLeakageScalars

#print axioms RKResearch.Certified.ERK10FifteenPureDonorLeakageScalars.forced_sums_and_square
#print axioms RKResearch.Certified.ERK10FifteenPureDonorLeakageScalars.requires_sqrt_neg_two
