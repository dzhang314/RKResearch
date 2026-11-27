module

public import RKCert.ReviewedNative.ERK9RationalFifteenChecks
public import Mathlib.Algebra.Field.Rat

@[expose] public section

/-! The strict literal fifteen-stage explicit witness has exact order
nine over any nontrivial commutative ring paying its common denominator.
In particular it works over every characteristic-zero field. -/

namespace RKResearch.Certified.ERK9RationalFifteen
open RKResearch FiniteRootedTree
open scoped Matrix

variable {R : Type*} [CommRing R]

theorem order_nine (d : R) (hd : (D:R)*d=1) : HasOrder 9 (A d) (b d) :=
  order_from_receipts receipts d hd

theorem not_order_ten [Nontrivial R] (d : R) (hd : (D:R)*d=1) :
    ¬ HasOrder 10 (A d) (b d) := by
  intro h
  have hb : ((bush10.order:ℕ)≤10) := by decide
  have hf := bush_defect d hd
  rw [h bush10 hb,sub_self,mul_zero] at hf
  obtain ⟨z,hz⟩ := (show (5:ℤ)∣D by decide +kernel)
  have hunit : IsUnit (5:R) := isUnit_of_dvd_unit
    (show (5:R) ∣ (D:R) from ⟨(z:R), by rw [hz,Int.cast_mul,Int.cast_ofNat]⟩)
    (IsUnit.of_mul_eq_one _ hd)
  exact hunit.ne_zero hf.symm

theorem exists_exact_of_unit [Nontrivial R] (hD : IsUnit (D:R)) :
    ∃ (U : Matrix (Fin 15) (Fin 15) R) (w : Fin 15 → R),
      ERK U ∧ HasOrder 9 U w ∧ ¬ HasOrder 10 U w := by
  obtain ⟨u,hu⟩ := hD
  let d : R := ↑(u⁻¹)
  have hd : (D:R)*d=1 := by rw [←hu]; exact u.mul_inv
  exact ⟨A d,b d,explicit d,order_nine d hd,not_order_ten d hd⟩

theorem exists_exact_charZero (K : Type*) [Field K] [CharZero K] :
    ∃ (U : Matrix (Fin 15) (Fin 15) K) (w : Fin 15 → K),
      ERK U ∧ HasOrder 9 U w ∧ ¬ HasOrder 10 U w :=
  exists_exact_of_unit ((Int.cast_ne_zero.mpr (show D ≠ 0 by decide +kernel)).isUnit)

theorem exists_exact_rational :
    ∃ (U : Matrix (Fin 15) (Fin 15) ℚ) (w : Fin 15 → ℚ),
      ERK U ∧ HasOrder 9 U w ∧ ¬ HasOrder 10 U w :=
  exists_exact_charZero ℚ

end RKResearch.Certified.ERK9RationalFifteen

#print axioms RKResearch.Certified.ERK9RationalFifteen.order_nine
#print axioms RKResearch.Certified.ERK9RationalFifteen.exists_exact_of_unit
#print axioms RKResearch.Certified.ERK9RationalFifteen.exists_exact_rational
