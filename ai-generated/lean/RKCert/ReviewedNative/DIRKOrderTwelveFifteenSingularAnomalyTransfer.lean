module

public import Mathlib.Tactic.LinearCombination
public import Mathlib.Tactic.Ring

@[expose] public section

/-! The local affine transfer at the actual anomalous row. -/
namespace RKResearch.Certified.Graded.OrderTwelveFifteen.SingularAnomalyTransfer

/-- The affine quotient known at all normal roots extends to the singleton
reverse anomaly by its actual input and primitive zeros. The scalar
difference h-model is the only canceled factor. -/
theorem transfer {K : Type*} [Field K] {h model s q j r L : K}
    (distinct : h ≠ model) (input : s = h*q) (primitive : j+h*r=0)
    (ratio : j+model*r=(s-model*q)*L) : j=s*L := by
  have z : (h-model)*(j-s*L)=0 := by
    linear_combination h*ratio - model*primitive + (model*L)*input
  exact sub_eq_zero.mp ((mul_eq_zero.mp z).resolve_left (sub_ne_zero.mpr distinct))

#print axioms transfer

end RKResearch.Certified.Graded.OrderTwelveFifteen.SingularAnomalyTransfer
