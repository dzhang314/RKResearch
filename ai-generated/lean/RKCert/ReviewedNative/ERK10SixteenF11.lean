module

public import RKCert.ReviewedNative.ERK10SixteenF11Checks

@[expose] public section

/-! Sixteen strictly explicit stages of exact order ten in
characteristic 11, independently checked by ordinary rooted trees. -/
namespace RKResearch.Certified.ERK10SixteenF11
open RKResearch FiniteRootedTree
open scoped Matrix FiniteRootedTree

theorem order_ten : HasOrder 10 A b := order_from_receipts receipts

theorem exact_f11 : ERK A ∧ HasOrder 10 A b ∧ ¬ HasOrder 11 A b := by
  refine ⟨explicit,order_ten,?_⟩
  intro h
  exact (by decide +kernel : (0:K)≠1) (next_value.symm.trans (h nextTree next_size))

end RKResearch.Certified.ERK10SixteenF11

#print axioms RKResearch.Certified.ERK10SixteenF11.order_ten
#print axioms RKResearch.Certified.ERK10SixteenF11.exact_f11
