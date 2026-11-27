module

public import RKCert.ReviewedNative.ERK10UniversalEighteenChecks

@[expose] public section

/-! A single eighteen-stage strictly explicit tableau of exact order ten
over every nontrivial commutative coefficient ring paying ten factorial. -/

namespace RKResearch.Certified.ERK10UniversalEighteen
open RKResearch FiniteRootedTree
open scoped Matrix

variable {R : Type*} [CommRing R]

theorem order_ten (d : R) (hd : (D:R)*d=1) : HasOrder 10 (A d) (b d) :=
  order_from_receipts receipts d hd

theorem not_order_eleven [Nontrivial R] (d : R) (hd : (D:R)*d=1) :
    ¬ HasOrder 11 (A d) (b d) := by
  intro h
  have ht : ((nextTree.order:ℕ)≤11) := by decide
  have hf := next_defect d hd
  rw [h nextTree ht,sub_self,mul_zero] at hf
  exact one_ne_zero (neg_eq_zero.mp hf.symm)

theorem exists_exact_of_unit [Nontrivial R] (hD : IsUnit (D:R)) :
    ∃ (U : Matrix (Fin 18) (Fin 18) R) (w : Fin 18 → R),
      ERK U ∧ HasOrder 10 U w ∧ ¬ HasOrder 11 U w := by
  obtain ⟨u,hu⟩ := hD
  let d : R := ↑(u⁻¹)
  have hd : (D:R)*d=1 := by rw [←hu]; exact u.mul_inv
  exact ⟨A d,b d,explicit d,order_ten d hd,not_order_eleven d hd⟩

theorem exists_exact [Nontrivial R] (h : IsUnit (Nat.factorial 10:R)) :
    ∃ (U : Matrix (Fin 18) (Fin 18) R) (w : Fin 18 → R),
      ERK U ∧ HasOrder 10 U w ∧ ¬ HasOrder 11 U w := by
  have hp : IsUnit (((Nat.factorial 10)^3:ℕ):R) := by
    simpa only [Nat.cast_pow] using h.pow 3
  have hD : IsUnit ((800150400:ℕ):R) := isUnit_of_dvd_unit (Nat.cast_dvd_cast (α:=R)
    (show (800150400:ℕ)∣(Nat.factorial 10)^3 by decide +kernel)) hp
  apply exists_exact_of_unit
  simpa only [D,Int.cast_ofNat,Nat.cast_ofNat] using hD

theorem exists_exact_iff_factorial_unit [Nontrivial R] :
    (∃ (U : Matrix (Fin 18) (Fin 18) R) (w : Fin 18 → R),
      ERK U ∧ HasOrder 10 U w ∧ ¬ HasOrder 11 U w) ↔
      IsUnit (Nat.factorial 10:R) := by
  refine ⟨?_,exists_exact⟩
  rintro ⟨A,b,_,ho,_⟩
  apply IsUnit.of_mul_eq_one (b ⬝ᵥ Φ (tallTree 10) A)
  have h := ho (tallTree 10) (by decide +kernel)
  have hfact : ((tallTree 10).factorial : ℕ) = Nat.factorial 10 := by decide +kernel
  simpa only [hfact] using h

end RKResearch.Certified.ERK10UniversalEighteen

#print axioms RKResearch.Certified.ERK10UniversalEighteen.order_ten
#print axioms RKResearch.Certified.ERK10UniversalEighteen.exists_exact
#print axioms RKResearch.Certified.ERK10UniversalEighteen.exists_exact_iff_factorial_unit
