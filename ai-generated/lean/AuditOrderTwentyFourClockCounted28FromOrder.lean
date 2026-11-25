module

import RKCert.ReviewedNative.OrderTwentyFourClockCounted28FromOrder

open RKResearch RKResearch.Certified.Graded
open HankelPaidMonicBasis HankelQuarticLegendre HankelCenteredAtom HankelOrderTwentyCounted28
open Polynomial Matrix Module
open scoped Polynomial Matrix

section
variable {K : Type*} [Field K] {s k : ℕ}
variable {A : Matrix (Fin s) (Fin s) K} {b : Fin s → K} {U : Finset K}

example (ho : HasOrder 20 A b) :
    ∀ j<20, (HankelLegendreIntData.paidNat : K)*centeredStageMoment A b (X^j) =
      (HankelLegendreIntData.atom j : K) :=
  (centeredStageMoment_powers_of_hasOrder ho).powers

example (two : (2:K) ≠ 0) (q : ℕ) :
    (hankel (maskedMoment (centeredStageMoment A b) (centeredClockMask U)) (q+1)).rank =
      finrank K (nodalPaidHankel A b (cutNodalPolynomial U) q).range :=
  centered_rank_eq_nodal two U q

example (ho : HasOrder 20 A b) :
    PaidLegendre28 (centeredStageMoment A b) :=
  paidLegendre28_of_centeredPower20 (centeredStageMoment_powers_of_hasOrder ho)

example (ho : HasOrder 20 A b) (tri : A.IsLowerTriangular) (le : k≤s)
    (u4 : U.card=4)
    (cover : ∀ i∈chronologicalHead le, nodes A i∈U)
    (ker0 : finrank K (cutZeroSpace K (chronologicalHead le) ⊓ (volterra A).ker :
      Submodule K (Fin s → K))=0) : 28≤s-k :=
  (chronological_cuts_ge_28 ho tri le U u4).1 cover ker0

example (ho : HasOrder 20 A b) (tri : A.IsLowerTriangular) (le : k≤s)
    (u4 : U.card=4)
    (cover : ∀ i∉chronologicalHead le, b i≠0 → nodes A i∈U)
    (ker0 : finrank K ((cutZeroSpace K (chronologicalHead le)).dualAnnihilator ⊓
      (volterra A).dualMap.ker : Submodule K (ClockCovector K s))=0) : 28≤k :=
  (chronological_cuts_ge_28 ho tri le U u4).2 cover ker0
end

#print axioms HankelCenteredAtom.centeredAtoms
#print axioms HankelCenteredAtom.centered_HasOrder_powers
#print axioms HankelQuarticLegendre.centered_mode_silent
#print axioms HankelQuarticLegendre.centered_mode_norm
#print axioms HankelQuarticLegendre.scaled_evalExpr_coeff
#print axioms HankelQuarticLegendre.paidLegendre28_of_centeredPower20
#print axioms HankelPaidAffineBasis.eval_affineClockMask
#print axioms HankelPaidAffineBasis.rank_hankel_eq_nodal
#print axioms HankelPaidAffineBasis.rank_affine_hankel_eq_nodal
#print axioms HankelOrderTwentyCounted28.centeredReadout28_of_hasOrder
#print axioms HankelOrderTwentyCounted28.actual_eight_width_credit_ge_28_of_hasOrder
#print axioms HankelOrderTwentyCounted28.chronological_cuts_ge_28
