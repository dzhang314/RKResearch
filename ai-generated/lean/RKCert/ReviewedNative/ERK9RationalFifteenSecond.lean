module

public import RKCert.ReviewedNative.ERK9RationalFifteenSecondChecks

@[expose] public section

namespace RKResearch.Certified.ERK9RationalFifteenSecond
open RKResearch FiniteRootedTree
open scoped Matrix

variable {R : Type*} [CommRing R]

theorem order_nine (d : R) (hd : (D:R)*d=1) : HasOrder 9 (A d) (b d) :=
  order_from_receipts receipts d hd

theorem not_order_ten [Nontrivial R] (d : R) (hd : (D:R)*d=1) :
    ¬ HasOrder 10 (A d) (b d) := by
  intro h
  have hb := tenth_defect d hd bush10 (by decide) 1282889664 71019553 bush_integer
  have hm := tenth_defect d hd mixed10 (by decide)
    5885687017987200 (-24755745567906941) mixed_integer
  rw [h bush10 (by decide), sub_self, mul_zero] at hb
  rw [h mixed10 (by decide), sub_self, mul_zero] at hm
  have h1 : (71019553:R)=0 := by
    simpa only [Int.cast_ofNat] using hb.symm
  have h2 : ((-24755745567906941:ℤ):R)=0 := hm.symm
  have bez : (22589206:ℤ)*(-24755745567906941)+7874065840952799*71019553=1 := by
    decide +kernel
  have hh := congrArg (Int.castRingHom R) bez
  rw [map_one] at hh
  change (((22589206:ℤ)*(-24755745567906941)+7874065840952799*71019553:ℤ):R)=1 at hh
  simp only [Int.cast_add,Int.cast_mul,Int.cast_ofNat,h1,h2,mul_zero,add_zero] at hh
  exact zero_ne_one hh

theorem exists_exact_of_unit [Nontrivial R] (hD : IsUnit (D:R)) :
    ∃ (U : Matrix (Fin 15) (Fin 15) R) (w : Fin 15 → R),
      ERK U ∧ HasOrder 9 U w ∧ ¬ HasOrder 10 U w := by
  obtain ⟨u,hu⟩ := hD
  let d : R := ↑(u⁻¹)
  have hd : (D:R)*d=1 := by rw [←hu]; exact u.mul_inv
  exact ⟨A d,b d,explicit d,order_nine d hd,not_order_ten d hd⟩

end RKResearch.Certified.ERK9RationalFifteenSecond

#print axioms RKResearch.Certified.ERK9RationalFifteenSecond.exists_exact_of_unit
