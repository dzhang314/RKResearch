module

import RKCert.ReviewedNative.ProjectedMomentContext

/-! Standalone typed clients of the projected moment model. No quotient,
split tableau, or characteristic-zero premise is added. -/
open RKResearch RKResearch.ContextCompletion Polynomial
open RKResearch.CanonicalUniqueness (TreeWord)
open RKResearch.Certified.Graded (primitive)
open scoped Polynomial

section

variable {K V ι : Type*} [Field K] [CommRing V] [Algebra K V] [Fintype ι]
variable {p : ℕ}

example {A : Matrix ι ι K} {b : ι → K} (h : RKResearch.HasOrder p A b)
    (j : ℕ) (pos : 0 < j) (paid : j ≤ p) : (j : K) ≠ 0 :=
  PaidUnits.of_tableau h j pos paid

example (j : ℕ) (a : K) :
    unitMoment (monomial j a) = a / ((j + 1 : ℕ) : K) :=
  unitMoment_monomial j a

example (units : PaidUnits K p) (f g : K[X]) (paid : f.natDegree + g.natDegree + 1 < p) :
    unitMoment (f * primitive g) =
      unitMoment ((C (unitMoment f) - primitive f) * g) :=
  unitMoment_byParts units f g paid

example (P : MomentProjection K V p) (units : PaidUnits K p) : P.model.HasOrder p :=
  P.hasOrder units

example (P : MomentProjection K V p) {A : Matrix ι ι K} {b : ι → K}
    (h : RKResearch.HasOrder p A b) (C : TreeWord) (t : FiniteRootedTree)
    (paid : ((C.insert t).order : ℕ) ≤ p) :
    P.model.readout (P.model.column (C.insert t)) = ((C.insert t).factorial : K)⁻¹ :=
  Model.HasOrder.paid_cell (P.hasOrder (PaidUnits.of_tableau h)) C t paid

end

#check @RKResearch.ContextCompletion.PaidUnits
#check @RKResearch.ContextCompletion.PaidUnits.of_tableau
#check @RKResearch.ContextCompletion.unitMoment_monomial
#check @RKResearch.ContextCompletion.unitMoment_byParts
#check @RKResearch.ContextCompletion.MomentProjection
#check @RKResearch.ContextCompletion.MomentProjection.model
#check @RKResearch.ContextCompletion.MomentProjection.hasOrder
#check @RKResearch.ContextCompletion.Model.HasOrder.paid_cell

#print axioms RKResearch.ContextCompletion.PaidUnits.of_tableau
#print axioms RKResearch.ContextCompletion.unitMoment_monomial
#print axioms RKResearch.ContextCompletion.unitMoment_byParts
#print axioms RKResearch.ContextCompletion.MomentProjection.hasOrder
#print axioms RKResearch.ContextCompletion.Model.HasOrder.paid_cell
