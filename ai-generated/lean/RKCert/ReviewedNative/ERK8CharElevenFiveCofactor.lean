module

public import RKCert.ReviewedNative.ERK8CharElevenFiveProfile

import Mathlib.Tactic.LinearCombination
import Mathlib.Tactic.Ring

@[expose] public section

/-! The literal one-dimensional E5 annihilator for the five-off chart.
It is the seven-bulk-clock cofactor vector; it is not the identically
zero output-weighted quadratic defect. -/
namespace RKResearch.Certified.Graded.ERK8CharEleven.FiveOff

open RKResearch Polynomial Module OneOff ERKTaggedHorizon ERK8PaidField LobattoEight RKCert.Endpoint
open RKResearch.Certified.Graded.ERK8CharEleven Reverse
open scoped Classical Matrix BigOperators

variable {K : Type*} [Field K]
variable {A : Matrix (Fin 10) (Fin 10) K} {b : Fin 10 → K}

noncomputable def bulkCofactor (A : Matrix (Fin 10) (Fin 10) K) (x : K) : K :=
  (nodalHull ((bulkClocks A).erase x)).eval x

theorem bulkCofactor_ne (A : Matrix (Fin 10) (Fin 10) K) (x : K) : bulkCofactor A x≠0 :=
  nodalHull_eval_ne_zero_of_notMem (Finset.notMem_erase _ _)

noncomputable def bulkReverse (A : Matrix (Fin 10) (Fin 10) K) : Fin 10→K :=
  fun i=>if i∈bulkRows then (bulkCofactor A (nodes A i))⁻¹ else 0

theorem bulkReverse_apply (A : Matrix (Fin 10) (Fin 10) K) {i : Fin 10}
    (hi : i∈bulkRows) : bulkReverse A i=(bulkCofactor A (nodes A i))⁻¹ := by
  simp [bulkReverse,hi]

theorem bulkReverse_ne_at (A : Matrix (Fin 10) (Fin 10) K) {i : Fin 10}
    (hi : i∈bulkRows) : bulkReverse A i≠0 := by
  rw [bulkReverse_apply A hi]
  exact inv_ne_zero (bulkCofactor_ne A _)

/-- The seventh-node top-coefficient measure kills every actual E5
column, even though every off weight is zero in this branch. -/
theorem bulkReverse_mem_annih_five
    (ha : ∀ i j, i≤j → A i j=0) (ho : HasOrder 8 A b) (p : (11:K)=0)
    (five : (offKnots A).card=5) (cleanFive : (cleanKnots A).card=5)
    {theta : K} (H : ExceptionalHead A theta) (S : CenterPrefix A 4)
    {x z : Fin 10} (T : FiveCleanTail A x z) :
    bulkReverse A∈annih (treeSpace A 5) := by
  have ⟨range,dim⟩ := bulkProfile_range_five ha ho p five cleanFive H S T
  rw [←range]
  apply mem_annih.mpr
  rintro v ⟨w,rfl⟩
  let P := ofFn 6 w.1
  have pd : P.natDegree≤5 := Nat.le_of_lt_succ (ofFn_natDegree_lt (by decide) _)
  have d := bulkClocks_card five cleanFive H T
  have noTop : (∑ x∈bulkClocks A,P.eval x/bulkCofactor A x)=0 := by
    have e := coeff_last_barycentric (bulkClocks A) P (by omega)
    rw [d,show 7-1=6 by decide,coeff_eq_zero_of_natDegree_lt (pd.trans_lt (by decide))] at e
    exact e.symm
  have cut : (∑ i∈bulkRows,bulkReverse A i*bulkProfile A 5 w i)=
      ∑ i : Fin 10,bulkReverse A i*bulkProfile A 5 w i := by
    apply Finset.sum_subset (Finset.subset_univ _)
    intro j _ hj
    simp [bulkReverse,hj]
  rw [row_apply,dotProduct,←cut]
  calc
    _ = ∑ i∈bulkRows,P.eval (nodes A i)/bulkCofactor A (nodes A i) := by
      apply Finset.sum_congr rfl
      intro i hi
      rw [bulkReverse_apply A hi,bulkProfile_bulk A 5 w hi]
      simp only [P,div_eq_mul_inv,mul_comm]
    _ = _ := by
      have pp : (∑ x∈bulkClocks A,P.eval x/bulkCofactor A x)=
            ∑ i∈bulkRows,P.eval (nodes A i)/bulkCofactor A (nodes A i) := by
        unfold bulkClocks
        rw [Finset.sum_image (bulk_clock_inj five cleanFive H T)]
      exact pp.symm.trans noTop

theorem bulkReverse_spans_annih_five
    (ha : ∀ i j, i≤j → A i j=0) (ho : HasOrder 8 A b) (p : (11:K)=0)
    (five : (offKnots A).card=5) (cleanFive : (cleanKnots A).card=5)
    {theta : K} (H : ExceptionalHead A theta) (S : CenterPrefix A 4)
    {x z : Fin 10} (T : FiveCleanTail A x z) :
    annih (treeSpace A 5) = K ∙ bulkReverse A := by
  have a := bulkReverse_mem_annih_five ha ho p five cleanFive H S T
  have b := (bulkProfile_range_five ha ho p five cleanFive H S T).2
  have dim := finrank_annih (treeSpace A 5)
  rw [b,Fintype.card_fin] at dim
  have zn : bulkReverse A≠0 := fun e =>
    bulkReverse_ne_at A (i:=6) (by decide) (congrFun e 6)
  have rc := finrank_span_singleton (K:=K) zn
  refine (Submodule.eq_of_le_of_finrank_le ((Submodule.span_singleton_le_iff_mem ..).mpr a) ?_).symm
  omega

theorem first_reflected_bulk_multiple
    (ha : ∀ i j, i≤j → A i j=0) (ho : HasOrder 8 A b) (p : (11:K)=0)
    (five : (offKnots A).card=5) (cleanFive : (cleanKnots A).card=5)
    {theta : K} (H : ExceptionalHead A theta) (S : CenterPrefix A 4)
    {x z : Fin 10} (T : FiveCleanTail A x z) :
    ∃ rho : K, reflectedStageRow A b 1=rho • bulkReverse A := by
  have z := reflectedStageRow_annih ho 5 1 (by decide)
  rw [bulkReverse_spans_annih_five ha ho p five cleanFive H S T] at z
  obtain ⟨rho,eq⟩ := Submodule.mem_span_singleton.mp z
  exact ⟨rho,eq.symm⟩

end RKResearch.Certified.Graded.ERK8CharEleven.FiveOff

#print axioms RKResearch.Certified.Graded.ERK8CharEleven.FiveOff.bulkReverse_mem_annih_five
#print axioms RKResearch.Certified.Graded.ERK8CharEleven.FiveOff.first_reflected_bulk_multiple
