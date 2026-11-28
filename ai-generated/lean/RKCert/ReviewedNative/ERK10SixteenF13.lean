module

public import RKCert.ReviewedNative.ERK10SixteenF13Checks

@[expose] public section

/-! Sixteen strictly explicit stages of exact order ten in
characteristic 13, independently checked by ordinary rooted trees. -/
namespace RKResearch.Certified.ERK10SixteenF13
open RKResearch FiniteRootedTree
open scoped Matrix FiniteRootedTree

theorem order_ten : HasOrder 10 A b := order_from_receipts receipts

theorem exact_f13 : ERK A ∧ HasOrder 10 A b ∧ ¬ HasOrder 11 A b := by
  refine ⟨explicit,order_ten,?_⟩
  intro h
  exact (by decide +kernel : (6:K)≠1) (next_value.symm.trans (h nextTree next_size))

end RKResearch.Certified.ERK10SixteenF13

#print axioms RKResearch.Certified.ERK10SixteenF13.order_ten
#print axioms RKResearch.Certified.ERK10SixteenF13.exact_f13
