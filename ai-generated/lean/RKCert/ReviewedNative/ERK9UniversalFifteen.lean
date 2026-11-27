module

public import RKCert.ReviewedNative.ERK9UniversalFifteenChecks

@[expose] public section

/-! A single strict fifteen-stage explicit tableau of exact order nine
over every nontrivial commutative coefficient ring paying nine factorial. -/

namespace RKResearch.Certified.ERK9UniversalFifteen
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
  have hzero : (7:R)=0 := neg_eq_zero.mp hf.symm
  obtain ⟨z,hz⟩ := (show (7:ℤ)∣D by decide +kernel)
  have hunit : IsUnit (7:R) := isUnit_of_dvd_unit
    (show (7:R) ∣ (D:R) from ⟨(z:R), by rw [hz,Int.cast_mul,Int.cast_ofNat]⟩)
    (IsUnit.of_mul_eq_one _ hd)
  exact hunit.ne_zero hzero

theorem exists_exact_of_unit [Nontrivial R] (hD : IsUnit (D:R)) :
    ∃ (U : Matrix (Fin 15) (Fin 15) R) (w : Fin 15 → R),
      ERK U ∧ HasOrder 9 U w ∧ ¬ HasOrder 10 U w := by
  obtain ⟨u,hu⟩ := hD
  let d : R := ↑(u⁻¹)
  have hd : (D:R)*d=1 := by rw [←hu]; exact u.mul_inv
  exact ⟨A d,b d,explicit d,order_nine d hd,not_order_ten d hd⟩

/-- Only factorial admissibility is required, with no field, local or
characteristic assumptions. -/
theorem exists_exact [Nontrivial R] (h : IsUnit (Nat.factorial 9:R)) :
    ∃ (U : Matrix (Fin 15) (Fin 15) R) (w : Fin 15 → R),
      ERK U ∧ HasOrder 9 U w ∧ ¬ HasOrder 10 U w := by
  have hp : IsUnit (((Nat.factorial 9)^2:ℕ):R) := by
    simpa only [Nat.cast_pow] using h.pow 2
  have hD : IsUnit ((2116800:ℕ):R) := isUnit_of_dvd_unit (Nat.cast_dvd_cast (α:=R)
    (show (2116800:ℕ)∣(Nat.factorial 9)^2 by decide +kernel)) hp
  apply exists_exact_of_unit
  simpa only [D,Int.cast_ofNat,Nat.cast_ofNat] using hD

theorem exists_exact_iff_factorial_unit [Nontrivial R] :
    (∃ (U : Matrix (Fin 15) (Fin 15) R) (w : Fin 15 → R),
      ERK U ∧ HasOrder 9 U w ∧ ¬ HasOrder 10 U w) ↔
      IsUnit (Nat.factorial 9:R) := by
  refine ⟨?_,exists_exact⟩
  rintro ⟨A,b,_,ho,_⟩
  apply IsUnit.of_mul_eq_one (b ⬝ᵥ Φ (tallTree 9) A)
  have h := ho (tallTree 9) (by decide +kernel)
  have hfact : ((tallTree 9).factorial : ℕ) = Nat.factorial 9 := by decide +kernel
  simpa only [hfact] using h

end RKResearch.Certified.ERK9UniversalFifteen

#print axioms RKResearch.Certified.ERK9UniversalFifteen.order_nine
#print axioms RKResearch.Certified.ERK9UniversalFifteen.exists_exact

#print axioms RKResearch.Certified.ERK9UniversalFifteen.exists_exact_iff_factorial_unit
