module

public import Mathlib.RingTheory.Polynomial.RationalRoot

@[expose] public section

/-! # An integral and prime-divisible representative of a fraction-field root

The leading coefficient is a unit (here normalized to one), so the rational-root
denominator theorem makes the root integral. If the remaining coefficients
all lie in a principal prime ideal, then so does the integral representative.
The constant coefficient need not have prime multiplicity exactly one. -/

namespace RKResearch.Certified

open Polynomial
open scoped Polynomial

/-- A fraction-field root of a monic polynomial with all nonleading
coefficients divisible by a prime is represented by a multiple of that
prime in the base UFD. -/
theorem exists_integer_dvd_of_monic_aeval_eq_zero
    {R K : Type*} [CommRing R] [IsDomain R] [UniqueFactorizationMonoid R]
    [Field K] [Algebra R K] [IsFractionRing R K] {P : R[X]} {x : K} {q : R}
    (hq : Prime q) (hP : P.Monic)
    (hcoeff : ∀ j < P.natDegree, q ∣ P.coeff j) (hx : aeval x P = 0) :
    ∃ z : R, x = algebraMap R K z ∧ q ∣ z := by
  obtain ⟨z, hz, _⟩ := exists_integer_of_is_root_of_monic hP hx
  have hEval : P.eval₂ (algebraMap R K) (algebraMap R K z) = 0 := by
    rw [← aeval_def, ← hz, hx]
  have hroot : P.IsRoot z :=
    isRoot_of_eval₂_map_eq_zero (IsFractionRing.injective R K) hEval
  have hd : q ∣ P.coeff P.natDegree * z ^ P.natDegree := by
    apply dvd_term_of_isRoot_of_dvd_terms P.natDegree hroot
    intro j hj
    rcases lt_or_gt_of_ne hj with hlt | hgt
    · exact dvd_mul_of_dvd_left (hcoeff j hlt) _
    · rw [coeff_eq_zero_of_natDegree_lt hgt, zero_mul]
      exact dvd_zero _
  rw [hP.coeff_natDegree, one_mul] at hd
  exact ⟨z, hz, hq.dvd_of_dvd_pow hd⟩

end RKResearch.Certified
