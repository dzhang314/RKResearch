module

public import Mathlib.RingTheory.Polynomial.RationalRoot

@[expose] public section

/-! # Reduction of a fraction-field root at a good leading coefficient

There is no map from the fraction field to a residue field. Reduce its
numerator and denominator instead, and use the existing rational-root
denominator theorem and scaleRoots to justify the division. -/

namespace RKResearch.Certified

open Polynomial IsFractionRing
open scoped Polynomial

noncomputable section

variable {R K F : Type*} [CommRing R] [IsDomain R] [UniqueFactorizationMonoid R]
variable [Field K] [Algebra R K] [IsFractionRing R K] [Field F]

/-- A fraction-field root has denominator a unit in every field image
in which the polynomial's leading coefficient remains nonzero. -/
theorem fractionRoot_den_map_ne_zero (f : R →+* F) {P : R[X]} {x : K}
    (hx : aeval x P = 0) (hlead : f P.leadingCoeff ≠ 0) :
    f (den R x : R) ≠ 0 := by
  obtain ⟨a,ha⟩ := den_dvd_of_is_root hx
  intro hd
  apply hlead
  rw [ha,map_mul,hd,zero_mul]

/-- Good reduction of the leading coefficient preserves a root
represented by the fraction-field numerator and denominator. -/
theorem fractionRoot_reduces_of_leadingCoeff_ne_zero (f : R →+* F) {P : R[X]} {x : K}
    (hx : aeval x P = 0) (hLead : f P.leadingCoeff ≠ 0) :
    (P.map f).IsRoot (f (num R x) / f (den R x : R)) := by
  let n := num R x
  let d : R := den R x
  have hd : f d ≠ 0 := fractionRoot_den_map_ne_zero f hx hLead
  have hn : (P.scaleRoots d).eval n = 0 := num_isRoot_scaleRoots_of_aeval_eq_zero hx
  have he : (P.scaleRoots d).eval₂ f (f n) = 0 := by
    rw [Polynomial.eval₂_at_apply,hn,map_zero]
  have hm : f d * (f n / f d) = f n := by
    rw [mul_comm,div_mul_cancel₀ _ hd]
  have h := scaleRoots_eval₂_mul (p := P) f (f n / f d) d
  rw [hm,he] at h
  change (P.map f).eval (f n / f d) = 0
  rw [← Polynomial.eval₂_eq_eval_map]
  exact (mul_eq_zero.mp h.symm).resolve_left (pow_ne_zero _ hd)

/-- Rootlessness of one good reduction obstructs every fraction-field
root, without any map on fractions with a bad denominator. -/
theorem no_fractionRoot_of_good_reduction (f : R →+* F) (P : R[X])
    (hLead : f P.leadingCoeff ≠ 0) (hzero : ∀ y : F, ¬ (P.map f).IsRoot y)
    (x : K) : aeval x P ≠ 0 := by
  intro hx
  exact hzero _ (fractionRoot_reduces_of_leadingCoeff_ne_zero f hx hLead)

end
end RKResearch.Certified
