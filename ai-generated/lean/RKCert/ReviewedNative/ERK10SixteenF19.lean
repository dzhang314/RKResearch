module

public import RKCert.ReviewedNative.ERK10SixteenF19Checks

@[expose] public section

/-! Sixteen strictly explicit stages of exact order ten in
characteristic 19, independently checked by ordinary rooted trees. -/
namespace RKResearch.Certified.ERK10SixteenF19
open RKResearch FiniteRootedTree
open scoped Matrix FiniteRootedTree

theorem order_ten : HasOrder 10 A b := order_from_receipts receipts

theorem exact_f19 : ERK A ∧ HasOrder 10 A b ∧ ¬ HasOrder 11 A b := by
  refine ⟨explicit,order_ten,?_⟩
  intro h
  exact (by decide +kernel : (12:K)≠1) (next_value.symm.trans (h nextTree next_size))

end RKResearch.Certified.ERK10SixteenF19

#print axioms RKResearch.Certified.ERK10SixteenF19.order_ten
#print axioms RKResearch.Certified.ERK10SixteenF19.exact_f19
