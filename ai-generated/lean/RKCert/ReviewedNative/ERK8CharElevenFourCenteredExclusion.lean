module

public import RKCert.ReviewedNative.ERK8CharElevenFourEarlyFiveExclusion
public import RKCert.ReviewedNative.ERK8CharElevenFourEarlySentinel
public import RKCert.ReviewedNative.ERK8CharElevenFourCenteredTail

import Lean.Elab.Tactic.Omega

@[expose] public section

/-! # Literal width-ten characteristic-eleven centered four-off exclusion -/
namespace RKResearch.Certified.Graded.ERK8CharEleven.FourOff

open RKResearch Polynomial OneOff ERKTaggedHorizon FourOffPhysical RKCert.Endpoint
open RKResearch.Certified.Graded.MultiOff.FourOff8CleanShape (CleanPrimitivePlacement)
open scoped Classical Matrix

variable {K : Type*} [Field K]
variable {A : Matrix (Fin 10) (Fin 10) K} {b : Fin 10 → K}

theorem no_actual_centered_four_off
    (ha : ∀ i j, i≤j → A i j=0) (ho : HasOrder 8 A b) (p : (11:K)=0)
    {P : K[X]} {dup k : Fin 10} (M : Placement A b P dup k)
    (L : CleanPrimitivePlacement A b k 6 (nodes A 7))
    (center : nodes A k=6) {theta : K} (tn : theta≠0) (fit : P=C theta*exceptionalQuadratic)
    (s : nodes A 6+nodes A 7=1) (m : nodes A 6*nodes A 7=8) : False := by
  have H := exceptional_head_of_centered_four p M L center tn fit
  have S := actual_clean_center_prefix ha ho M center
  have distinct := early_off_distinct_of_placement M
  rcases M.firstAtFourOrFive with eq|eq
  · subst k
    have g5 : g A 5≠0 := fun g=>(by decide : (5:Fin 10)≠4)
      (M.onlyCleanInMiddle 5 (by decide) (by decide) g)
    obtain ⟨_,_,beta,bn,U,rem⟩ := four_off_early_chart_of_center_four ha ho p distinct H S g5
    have d : (FiveOff.earlyFourHull A).natDegree≤4 := by
      rw [FiveOff.earlyFourHull,natDegree_nodalHull,(early_n4_from_off_row_five distinct S g5).2]
    have vanish (t : K) (ht : t∈offKnots A) : (FiveOff.earlyFourHull A).eval t=0 := by
      apply nodalHull_eval_of_mem
      obtain ⟨j,j0,j6,jg,h⟩ := M.offSenders t ht
      have j4 : j≠4 := fun eq=>jg (eq.symm ▸ M.firstClean)
      have cases : j=1∨j=2∨j=3∨j=5 := by omega
      rcases cases with rfl|rfl|rfl|rfl <;>
        simp [FiveOff.earlyFourClocks,earlyThreeClocks,←h]
    exact centered_tail_contradiction ha ho p M center L H s m _ d vanish bn rem
  · subst k
    exact four_off_contradiction_of_center_five ha ho p distinct M.rankData.bandThree H S

end RKResearch.Certified.Graded.ERK8CharEleven.FourOff

#print axioms RKResearch.Certified.Graded.ERK8CharEleven.FourOff.no_actual_centered_four_off
