module

public import RKCert.ReviewedNative.ERK12UniversalTwentyFourChecks

@[expose] public section

/-! One twenty-four-stage explicit order-twelve tableau over every
nontrivial ring with unit \(12!\). -/

namespace RKResearch.Certified.ERK12UniversalTwentyFour
open RKResearch FiniteRootedTree
open scoped Matrix

variable {R : Type*} [CommRing R]

theorem order_twelve (d : R) (hd : (D:R)*d=1) : HasOrder 12 (A d) (b d) :=
  order_from_trace trace (fun n hn => all_energy ⟨n,hn⟩) d hd

theorem exists_exact_of_unit [Nontrivial R] (hD : IsUnit (D:R)) :
    ∃ (U : Matrix (Fin 24) (Fin 24) R) (w : Fin 24 → R),
      ERK U ∧ HasOrder 12 U w ∧ ¬ HasOrder 13 U w := by
  obtain ⟨u,hu⟩ := hD
  let d : R := ↑(u⁻¹)
  have hd : (D:R)*d=1 := by rw [←hu]; exact u.mul_inv
  exact ⟨A d,b d,explicit d,order_twelve d hd,not_order_thirteen d hd⟩

theorem exists_exact [Nontrivial R] (h : IsUnit (Nat.factorial 12:R)) :
    ∃ (U : Matrix (Fin 24) (Fin 24) R) (w : Fin 24 → R),
      ERK U ∧ HasOrder 12 U w ∧ ¬ HasOrder 13 U w := by
  have hp : IsUnit (((Nat.factorial 12)^7:ℕ):R) := by
    simpa only [Nat.cast_pow] using h.pow 7
  have hD : IsUnit ((28868710429988352000000000000:ℕ):R) :=
    isUnit_of_dvd_unit (Nat.cast_dvd_cast (α:=R)
      (show (28868710429988352000000000000:ℕ)∣(Nat.factorial 12)^7 by decide +kernel)) hp
  apply exists_exact_of_unit
  simpa only [D,Int.cast_ofNat,Nat.cast_ofNat] using hD

theorem exists_exact_iff_factorial_unit [Nontrivial R] :
    (∃ (U : Matrix (Fin 24) (Fin 24) R) (w : Fin 24 → R),
      ERK U ∧ HasOrder 12 U w ∧ ¬ HasOrder 13 U w) ↔
      IsUnit (Nat.factorial 12:R) := by
  refine ⟨?_,exists_exact⟩
  rintro ⟨A,b,_,ho,_⟩
  apply IsUnit.of_mul_eq_one (b ⬝ᵥ Φ (tallTree 12) A)
  have h := ho (tallTree 12) (by decide +kernel)
  have hfact : ((tallTree 12).factorial : ℕ) = Nat.factorial 12 := by decide +kernel
  simpa only [hfact] using h

end RKResearch.Certified.ERK12UniversalTwentyFour

#print axioms RKResearch.Certified.ERK12UniversalTwentyFour.order_twelve
#print axioms RKResearch.Certified.ERK12UniversalTwentyFour.exists_exact
#print axioms RKResearch.Certified.ERK12UniversalTwentyFour.exists_exact_iff_factorial_unit
