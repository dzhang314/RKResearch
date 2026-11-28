module

public import RKCert.ReviewedNative.ERK10SixteenF17Checks

@[expose] public section

/-! Sixteen strictly explicit stages of exact order ten in
characteristic seventeen, independently checked by ordinary rooted trees. -/
namespace RKResearch.Certified.ERK10SixteenF17
open RKResearch FiniteRootedTree
open scoped Matrix FiniteRootedTree

theorem order_ten : HasOrder 10 A b := order_from_receipts receipts

theorem exact_f17 : ERK A ∧ HasOrder 10 A b ∧ ¬ HasOrder 11 A b := by
  refine ⟨explicit,order_ten,?_⟩
  intro h
  exact (by decide +kernel : (3:K)≠1) (next_value.symm.trans (h nextTree next_size))

end RKResearch.Certified.ERK10SixteenF17

#print axioms RKResearch.Certified.ERK10SixteenF17.order_ten
#print axioms RKResearch.Certified.ERK10SixteenF17.exact_f17
