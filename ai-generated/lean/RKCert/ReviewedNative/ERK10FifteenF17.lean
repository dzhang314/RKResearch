module

public import RKCert.ReviewedNative.ERK10FifteenF17Checks

@[expose] public section

/-! Fifteen strictly explicit stages of exact order ten in characteristic 17,
independently checked using ordinary rooted trees. -/
namespace RKResearch.Certified.ERK10FifteenF17
open RKResearch FiniteRootedTree
open scoped Matrix FiniteRootedTree

theorem order_ten : HasOrder 10 A b := order_from_receipts receipts

theorem exact_f17 : ERK A ∧ HasOrder 10 A b ∧ ¬ HasOrder 11 A b := by
  refine ⟨explicit,order_ten,?_⟩
  intro h
  exact (by decide +kernel : (9:K)≠1) (next_value.symm.trans (h nextTree next_size))

theorem exact_of_char17 (R : Type*) [CommRing R] [Nontrivial R] [CharP R 17] :
    ∃ (A : Matrix (Fin 15) (Fin 15) R) (b : Fin 15 → R),
      ERK A ∧ HasOrder 10 A b ∧ ¬ HasOrder 11 A b := by
  let f : ZMod 17 →+* R := ZMod.castHom (dvd_refl 17) R
  have hf : Function.Injective f := ZMod.castHom_injective R
  refine ⟨A.map f,f ∘ b,?_,order_ten.map f,?_⟩
  · intro i j hij
    change f (A i j) = 0
    rw [explicit hij,map_zero]
  · intro h
    exact exact_f17.2.2 ((hasOrder_map_iff (f:=f) hf).mp h)

end RKResearch.Certified.ERK10FifteenF17

#print axioms RKResearch.Certified.ERK10FifteenF17.order_ten
#print axioms RKResearch.Certified.ERK10FifteenF17.exact_f17
#print axioms RKResearch.Certified.ERK10FifteenF17.exact_of_char17
