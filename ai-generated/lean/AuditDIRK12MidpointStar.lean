import RKCert.ReviewedNative.DIRKOrderTwelveMidpointStar

open RKResearch FiniteRootedTree
open RKResearch.Certified.DIRK12MidpointStar
open scoped Polynomial Matrix FiniteRootedTree

set_option autoImplicit false

example {ι K : Type} [Fintype ι] [Field K] (A : Matrix ι ι K) (b : ι → K)
    (S : K[X]) (hS : S.Monic) (degreeS : S.natDegree=10)
    (I : K[X] →ₗ[K] K) (paid : ∀ P : K[X], P.natDegree<12 → quadr A b P = I P)
    (roots : ∀ i, b i * S.eval (1-RKResearch.Certified.Graded.nodes A i) = 0)
    (star : 13 * I starPoly=1) :
    (((bushyTree 13).factorial:Nat):K) * (b ⬝ᵥ Φ (bushyTree 13) A) - 1
      = -(13:K) * I (Polynomial.X^2*S) :=
  actual_star_defect A b S hS degreeS I paid roots star

#print axioms RKResearch.Certified.DIRK12MidpointStar.actual_star_defect
