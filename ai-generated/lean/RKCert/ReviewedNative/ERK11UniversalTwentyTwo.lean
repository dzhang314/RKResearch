module

public import RKCert.ReviewedNative.ERK11UniversalTwentyTwoChecks

@[expose] public section

/-! A single twenty-two-stage strictly explicit tableau of exact order eleven
over every nontrivial commutative coefficient ring in which eleven factorial is a unit. -/

namespace RKResearch.Certified.ERK11UniversalTwentyTwo
open RKResearch FiniteRootedTree
open scoped Matrix

variable {R : Type*} [CommRing R]

theorem order_eleven (d : R) (hd : (D:R)*d=1) : HasOrder 11 (A d) (b d) :=
  order_from_receipts receipts d hd

theorem not_order_twelve [Nontrivial R] (d : R) (hd : (D:R)*d=1) :
    ¬ HasOrder 12 (A d) (b d) := by
  intro h
  have ht : ((nextTree.order:ℕ)≤12) := by decide
  have hf := next_defect d hd
  rw [h nextTree ht,sub_self,mul_zero] at hf
  obtain ⟨z,hz⟩ := (show (16:ℤ)∣D by decide +kernel)
  have hunit : IsUnit (16:R) := isUnit_of_dvd_unit
    (show (16:R) ∣ (D:R) from ⟨(z:R), by rw [hz,Int.cast_mul,Int.cast_ofNat]⟩)
    (IsUnit.of_mul_eq_one _ hd)
  exact hunit.ne_zero (neg_eq_zero.mp hf.symm)

theorem exists_exact_of_unit [Nontrivial R] (hD : IsUnit (D:R)) :
    ∃ (U : Matrix (Fin 22) (Fin 22) R) (w : Fin 22 → R),
      ERK U ∧ HasOrder 11 U w ∧ ¬ HasOrder 12 U w := by
  obtain ⟨u,hu⟩ := hD
  let d : R := ↑(u⁻¹)
  have hd : (D:R)*d=1 := by rw [←hu]; exact u.mul_inv
  exact ⟨A d,b d,explicit d,order_eleven d hd,not_order_twelve d hd⟩

theorem exists_exact [Nontrivial R] (h : IsUnit (Nat.factorial 11:R)) :
    ∃ (U : Matrix (Fin 22) (Fin 22) R) (w : Fin 22 → R),
      ERK U ∧ HasOrder 11 U w ∧ ¬ HasOrder 12 U w := by
  have hp : IsUnit (((Nat.factorial 11)^3:ℕ):R) := by
    simpa only [Nat.cast_pow] using h.pow 3
  have hD : IsUnit ((941072888448000:ℕ):R) := isUnit_of_dvd_unit (Nat.cast_dvd_cast (α:=R)
    (show (941072888448000:ℕ)∣(Nat.factorial 11)^3 by decide +kernel)) hp
  apply exists_exact_of_unit
  simpa only [D,Int.cast_ofNat,Nat.cast_ofNat] using hD

theorem exists_exact_iff_factorial_unit [Nontrivial R] :
    (∃ (U : Matrix (Fin 22) (Fin 22) R) (w : Fin 22 → R),
      ERK U ∧ HasOrder 11 U w ∧ ¬ HasOrder 12 U w) ↔
      IsUnit (Nat.factorial 11:R) := by
  refine ⟨?_,exists_exact⟩
  rintro ⟨A,b,_,ho,_⟩
  apply IsUnit.of_mul_eq_one (b ⬝ᵥ Φ (tallTree 11) A)
  have h := ho (tallTree 11) (by decide +kernel)
  have hfact : ((tallTree 11).factorial : ℕ) = Nat.factorial 11 := by decide +kernel
  simpa only [hfact] using h

end RKResearch.Certified.ERK11UniversalTwentyTwo

#print axioms RKResearch.Certified.ERK11UniversalTwentyTwo.order_eleven
#print axioms RKResearch.Certified.ERK11UniversalTwentyTwo.exists_exact
#print axioms RKResearch.Certified.ERK11UniversalTwentyTwo.exists_exact_iff_factorial_unit
