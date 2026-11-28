module

public import RKCert.ReviewedNative.ERK10MirrorUnit13Checks
public import RKCert.ReviewedNative.ERK10MirrorUnit13Next

@[expose] public section

/-! Exact rational order-ten method; it also works inverting its literal
common denominator, with a two-tree Bézout receipt for exactness. -/
namespace RKResearch.Certified.ERK10MirrorUnit13
open RKResearch FiniteRootedTree
open scoped Matrix

abbrev e₁ : ℤ := 138963625074234951755337364362734
abbrev e₂ : ℤ := 13966576541690306994495

theorem bezout : e₁*n₁+e₂*n₂=1 := by decide +kernel

variable {R : Type*} [CommRing R]

theorem order_ten (d : R) (hd : (D:R)*d=1) : HasOrder 10 (A d) (b d) :=
  order_from_receipts receipts d hd

theorem not_order_eleven [Nontrivial R] (d : R) (hd : (D:R)*d=1) :
    ¬ HasOrder 11 (A d) (b d) := by
  intro ho
  have h₁ := from_integer_defect tree₁ (by decide) d₁ n₁ integer_next₁ d hd
  have h₂ := from_integer_defect tree₂ (by decide) d₂ n₂ integer_next₂ d hd
  rw [ho tree₁ (by decide),sub_self,mul_zero] at h₁
  rw [ho tree₂ (by decide),sub_self,mul_zero] at h₂
  have hb := congrArg (Int.castRingHom R) bezout
  simp only [map_add,map_mul,map_one] at hb
  change (e₁:R)*(n₁:R)+(e₂:R)*(n₂:R)=1 at hb
  rw [←h₁,←h₂,mul_zero,mul_zero,zero_add] at hb
  exact zero_ne_one hb

theorem exists_exact_of_unit [Nontrivial R] (hD : IsUnit (D:R)) :
    ∃ (U : Matrix (Fin 16) (Fin 16) R) (w : Fin 16 → R),
      ERK U ∧ HasOrder 10 U w ∧ ¬ HasOrder 11 U w := by
  obtain ⟨u,hu⟩ := hD
  let d : R := ↑(u⁻¹)
  have hd : (D:R)*d=1 := by rw [←hu]; exact u.mul_inv
  exact ⟨A d,b d,explicit d,order_ten d hd,not_order_eleven d hd⟩

theorem exists_exact_rat :
    ∃ (U : Matrix (Fin 16) (Fin 16) ℚ) (w : Fin 16 → ℚ),
      ERK U ∧ HasOrder 10 U w ∧ ¬ HasOrder 11 U w :=
  exists_exact_of_unit (isUnit_iff_ne_zero.mpr (by decide +kernel))

end RKResearch.Certified.ERK10MirrorUnit13

#print axioms RKResearch.Certified.ERK10MirrorUnit13.order_ten
#print axioms RKResearch.Certified.ERK10MirrorUnit13.exists_exact_of_unit
#print axioms RKResearch.Certified.ERK10MirrorUnit13.exists_exact_rat
