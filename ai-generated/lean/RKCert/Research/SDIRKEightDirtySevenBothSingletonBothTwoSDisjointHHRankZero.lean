import Mathlib.Tactic.Ring.Basic

/-! Scalar characteristic-zero scale-mirror gates (the field census is separate). -/
namespace RKCert.Research.SDIRKEightDirtySevenBothSingletonBothTwoSDisjointHHRankZero

theorem quadratic_even_of_equal_end_values {K : Type*} [Field K]
    (r₀ r₁ r₂ h : K) (hh : 2 * h ≠ 0)
    (he : r₀ + r₁ * h + r₂ * h ^ 2 = r₀ + r₁ * (-h) + r₂ * (-h) ^ 2) :
    r₁ = 0 := by
  have hmul : (2 * h) * r₁ = 0 := by
    calc
      (2 * h) * r₁ =
        (r₀ + r₁ * h + r₂ * h ^ 2) - (r₀ + r₁ * (-h) + r₂ * (-h) ^ 2) := by ring1
      _ = 0 := sub_eq_zero.mpr he
  exact (mul_eq_zero.mp hmul).resolve_left hh

theorem same_offset_of_even_singleton_quartic {K : Type*} [Field K]
    (theta a b : K) (hth : theta ≠ 0) (hcu : theta * (b - a) = 0) : a = b :=
  (sub_eq_zero.mp ((mul_eq_zero.mp hcu).resolve_left hth)).symm

end RKCert.Research.SDIRKEightDirtySevenBothSingletonBothTwoSDisjointHHRankZero
