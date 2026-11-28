module

public import RKCert.ReviewedNative.DIRK12MidpointRealSupportEndpoint
import Mathlib.Tactic.FinCases

@[expose] public section

/-! Actual width-fifteen physical output weights of the midpoint chart:
four ghosts have zero weight and the repeated reflected label is split
in half. The checked sums supply all scalar quadrature and the true
unpaid size-thirteen bush for any matching physical row sums. -/
namespace RKResearch.Certified.DIRK12MidpointRealInterval

open RKResearch Graded FiniteRootedTree Polynomial DirectedRatBox
open scoped Matrix Polynomial FiniteRootedTree BigOperators

def stageTag (i : Fin 15) : Fin 10 :=
  match i.val with
  | 0 => 1
  | 5 => 2
  | 6 => 3
  | 7 => 4
  | 8 => 5
  | 9 => 6
  | 10 => 9
  | 11 => 7
  | 12 => 8
  | 13 => 7
  | _ => 0

abbrev ghostRow (i : Fin 15) : Prop := 1 ≤ i.val ∧ i.val ≤ 4

noncomputable def cardinalWeight (x f : ℝ) (j : Fin 10) : ℝ :=
  integral (Lagrange.basis Finset.univ (site x f) j)

noncomputable def physicalWeight (x f : ℝ) (i : Fin 15) : ℝ :=
  if ghostRow i then 0 else
  if i.val=11 ∨ i.val=13 then cardinalWeight x f (stageTag i)/2 else cardinalWeight x f (stageTag i)

theorem weight_aggregate (x f : ℝ) (j : Fin 10) :
    (∑ i : Fin 15, if stageTag i=j then physicalWeight x f i else 0) =
    cardinalWeight x f j := by
  fin_cases j <;> simp [Fin.sum_univ_succ,stageTag,physicalWeight,ghostRow] <;> ring

theorem scalar_and_star_with_physical_weights {x f : ℝ}
    (hx : Encloses xBox x) (hf : Encloses fBox f) (hx0 : realX x=0) (hf0 : realF x f=0)
    (A : Matrix (Fin 15) (Fin 15) ℝ)
    (clocks : ∀ i, ¬ ghostRow i → 1-nodes A i=site x f (stageTag i)) :
    (∀ q : ℝ[X], q.natDegree<12 → DIRK12MidpointStar.quadr A (physicalWeight x f) q=integral q) ∧
      (starLo:ℝ) < (((bushyTree 13).factorial:Nat):ℝ)*(physicalWeight x f ⬝ᵥ Φ (bushyTree 13) A)-1 ∧
      (((bushyTree 13).factorial:Nat):ℝ)*(physicalWeight x f ⬝ᵥ Φ (bushyTree 13) A)-1 < (starHi:ℝ) := by
  apply actual_scalar_and_star hx hf hx0 hf0 A (physicalWeight x f) stageTag
  · intro i hw
    apply clocks
    intro hi
    exact hw (by simp [physicalWeight,hi])
  · exact weight_aggregate x f

end RKResearch.Certified.DIRK12MidpointRealInterval

#print axioms RKResearch.Certified.DIRK12MidpointRealInterval.weight_aggregate
#print axioms RKResearch.Certified.DIRK12MidpointRealInterval.scalar_and_star_with_physical_weights
