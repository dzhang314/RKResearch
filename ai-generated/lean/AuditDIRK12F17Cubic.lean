import RKCert.ReviewedNative.DIRK12F17Cubic

open RKResearch
open RKResearch.Certified.Graded
open RKResearch.Certified.DIRK12F17Cubic
open scoped Matrix FiniteRootedTree

set_option autoImplicit false

example : Module.finrank (ZMod 17) K = 3 := extension_degree

example :
    Matrix.IsLowerTriangular (A alpha) ∧ A alpha 0 0 ≠ A alpha 1 1 ∧
      HasOrder 12 (A alpha) (b alpha) ∧ ¬ HasOrder 13 (A alpha) (b alpha) :=
  exact_f17_cubic

example :
    IsUnit ((((nextTree.factorial : Nat) : K)) * (b alpha ⬝ᵥ Φ nextTree (A alpha)) - 1) :=
  unit_next_star cubic_alpha

example :
    (13 : K)*row (b alpha) ((nodes (A alpha))^12) - 1 = 11+7*alpha+12*alpha^2 :=
  next_value cubic_alpha

#print axioms RKResearch.Certified.DIRK12F17Cubic.exact_f17_cubic
#print axioms RKResearch.Certified.DIRK12F17Cubic.unit_next_star
#print axioms RKResearch.Certified.DIRK12F17Cubic.extension_degree
