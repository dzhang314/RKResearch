import RKCert.ReviewedNative.DIRK12MidpointRealPhysicalWeights

open RKResearch FiniteRootedTree
open RKResearch.Certified.DirectedRatBox
open RKResearch.Certified.DIRK12MidpointRealInterval
open scoped Polynomial Matrix FiniteRootedTree

set_option autoImplicit false

example : ∃ x f : ℝ, Encloses xBox x ∧ Encloses fBox f ∧ realX x=0 ∧ realF x f=0 ∧
    Function.Injective (site x f) ∧
    (∀ q : ℝ[X], q.natDegree<12 → scalarQuadrature x f q=integral q) :=
  exists_scalar_quadrature

example (x f : ℝ) (j : Fin 10) :
    (∑ i : Fin 15, if stageTag i=j then physicalWeight x f i else 0) =
    cardinalWeight x f j :=
  weight_aggregate x f j

#print axioms RKResearch.Certified.DIRK12MidpointRealInterval.exists_scalar_quadrature
#print axioms RKResearch.Certified.DIRK12MidpointRealInterval.scalar_and_star_with_physical_weights
