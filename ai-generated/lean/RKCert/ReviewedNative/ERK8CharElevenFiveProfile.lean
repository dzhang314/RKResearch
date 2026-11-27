module

public import RKCert.ReviewedNative.ERK8CharElevenFiveGeometry

import Mathlib.Tactic.FinCases
import Mathlib.Tactic.LinearCombination
import Mathlib.Tactic.Ring

@[expose] public section

/-! The three anchor coordinates and polynomial evaluations on the
seven bulk rows are actual E4/E5 vectors. The grade-five rank cap is
saturated, which earns the genuine cofactor annihilator. -/
namespace RKResearch.Certified.Graded.ERK8CharEleven.FiveOff

open RKResearch Polynomial Module OneOff ERKTaggedHorizon ERK8PaidField LobattoEight RKCert.Endpoint
open RKResearch.Certified.Graded.ERK8CharEleven Reverse
open scoped Classical Matrix BigOperators

variable {K : Type*} [Field K]
variable {A : Matrix (Fin 10) (Fin 10) K} {b : Fin 10 → K}

noncomputable def bulkProfile (A : Matrix (Fin 10) (Fin 10) K) (k : ℕ) :
    ((Fin (k+1)→K) × (Fin 3→K)) →ₗ[K] (Fin 10→K) where
  toFun w i := if i=0 then w.2 0 else if i=4 then w.2 1 else if i=9 then w.2 2
    else coeffEval A k w.1 i
  map_add' u v := by
    ext i
    by_cases h0 : i=0 <;> by_cases h4 : i=4 <;> by_cases h9 : i=9 <;>
      simp [h0,h4,h9,map_add]
  map_smul' a w := by
    ext i
    by_cases h0 : i=0 <;> by_cases h4 : i=4 <;> by_cases h9 : i=9 <;>
      simp [h0,h4,h9,map_smul]

theorem bulkProfile_bulk (A : Matrix (Fin 10) (Fin 10) K) (k : ℕ)
    (w : (Fin (k+1)→K) × (Fin 3→K)) {i : Fin 10} (hi : i∈bulkRows) :
    bulkProfile A k w i=(ofFn (k+1) w.1).eval (nodes A i) := by
  obtain ⟨h0,h4,h9⟩ := mem_bulkRows.mp hi
  have eq := congrFun (ofFn_eval A k w.1) i
  change (ofFn (k+1) w.1).eval (nodes A i)=coeffEval A k w.1 i at eq
  simpa [bulkProfile,h0,h4,h9] using eq.symm

theorem bulkProfile_mem
    (ho : HasOrder 8 A b) (p : (11:K)=0)
    {theta : K} (H : ExceptionalHead A theta) (S : CenterPrefix A 4)
    {x z : Fin 10} (T : FiveCleanTail A x z) {k : ℕ} (k4 : 4≤k)
    (w : (Fin (k+1)→K) × (Fin 3→K)) :
    bulkProfile A k w ∈ treeSpace A k := by
  let P := ofFn (k+1) w.1
  let q : K[X] := exceptionalQuadratic
  let U : Finset K := {0,1,6}
  let vals (t : K) := if t=0 then w.2 0 else if t=6 then w.2 1 else w.2 2
  let R := Lagrange.interpolate U id (fun t=> (vals t-P.eval t)/q.eval t)
  have n6 : (6:K)≠0 := (ho.natCast_isUnit (n:=6) (by decide) (by decide)).ne_zero
  have n5 : (5:K)≠0 := (ho.natCast_isUnit (n:=5) (by decide) (by decide)).ne_zero
  have n61 : (6:K)≠1 := fun e => n5 (by linear_combination e)
  have card : U.card=3 := by simp [U,Finset.card_insert_of_notMem,zero_ne_one,n6.symm,n61.symm]
  have Rd : R.natDegree≤2 := by
    by_cases r : R=0
    · simp [r]
    have d := (natDegree_lt_iff_degree_lt r).mpr
      (Lagrange.degree_interpolate_lt (fun t => (vals t-P.eval t)/q.eval t)
        (Set.injOn_id _) (s:=U))
    change R.natDegree<U.card at d
    omega
  have Pd : P.natDegree≤k := Nat.le_of_lt_succ (ofFn_natDegree_lt (by omega) _)
  let V := evalNodes A (P+q*R)-theta⁻¹ • diag (g A) (evalNodes A R)
  have mem : V∈treeSpace A k := by
    have dd : (q*R).natDegree≤4 := natDegree_mul_le_of_le exceptionalQuadratic_degree Rd
    have pd : (P+q*R).natDegree≤k := by
      have dk := dd.trans k4
      simpa only [Nat.max_self] using natDegree_add_le_of_degree_le Pd dk
    have dg : diag (g A) (evalNodes A R)∈zeroSpace A 4 :=
      band_le A 2 (band_iff.mpr ⟨R,Rd,rfl⟩)
    exact (treeSpace A k).sub_mem (evalNodes_mem_treeSpace A _ pd)
      ((treeSpace A k).smul_mem _ (treeSpace_mono A k4 (zeroSpace_le_treeSpace A 4 dg)))
  have onAnchor (i : Fin 10) (ha : i∈anchorRows) : V i=vals (nodes A i) := by
    have gt := anchor_clean H S ha
    have cu : nodes A i∈U := anchor_clock_mem H S ha
    have nv : q.eval (nodes A i)≠0 := exceptional_quadratic_ne_at_anchors ho p cu
    have e := Lagrange.eval_interpolate_at_node (fun t=> (vals t-P.eval t)/q.eval t) (Set.injOn_id _) cu
    change R.eval (nodes A i)=(vals (nodes A i)-P.eval (nodes A i))/q.eval (nodes A i) at e
    simp only [V,Pi.sub_apply,Pi.smul_apply,smul_eq_mul,evalNodes_apply,diag_apply,eval_add,eval_mul,gt,
      zero_mul,mul_zero,sub_zero,e,mul_div_cancel₀ _ nv]
    ring
  have onBulk (i : Fin 10) (hi : i∈bulkRows) : V i=P.eval (nodes A i) := by
    simp only [V,Pi.sub_apply,Pi.smul_apply,smul_eq_mul,evalNodes_apply,diag_apply,eval_add,eval_mul]
    by_cases gi : g A i=0
    · have q0 : q.eval (nodes A i)=0 := bulk_clean_q_zero T hi gi
      simp [gi,q0]
    · have e : theta⁻¹*theta=1 := inv_mul_cancel₀ H.scale_ne
      rw [←H.fit i gi]
      change P.eval (nodes A i)+q.eval (nodes A i)*R.eval (nodes A i)-
        theta⁻¹*(theta*q.eval (nodes A i)*R.eval (nodes A i))=P.eval (nodes A i)
      linear_combination -(q.eval (nodes A i)*R.eval (nodes A i))*e
  have eq : bulkProfile A k w=V := by
    ext i
    by_cases h0 : i=0
    · subst i
      rw [onAnchor 0 (by decide),S.origin_clock]
      simp [bulkProfile,vals]
    by_cases h4 : i=4
    · subst i
      rw [onAnchor 4 (by decide),S.center_clock]
      simp [bulkProfile,vals,n6]
    by_cases h9 : i=9
    · subst i
      rw [onAnchor 9 (by decide),show nodes A 9=1 from H.terminal_clock]
      simp [bulkProfile,vals,n61.symm]
    rw [bulkProfile_bulk A k w (mem_bulkRows.mpr ⟨h0,h4,h9⟩),onBulk i (mem_bulkRows.mpr ⟨h0,h4,h9⟩)]
  rw [eq]
  exact mem

theorem bulkProfile_injective (five : (offKnots A).card=5) (cleanFive : (cleanKnots A).card=5)
    {theta : K} (H : ExceptionalHead A theta) {x z : Fin 10} (T : FiveCleanTail A x z)
    {k : ℕ} (k5 : k≤5) : Function.Injective (bulkProfile A k) := by
  intro w v eq
  let P := ofFn (k+1) w.1
  let Q := ofFn (k+1) v.1
  have Pd : P.natDegree≤k := Nat.le_of_lt_succ (ofFn_natDegree_lt (by omega) _)
  have Qd : Q.natDegree≤k := Nat.le_of_lt_succ (ofFn_natDegree_lt (by omega) _)
  have C := bulkClocks_card five cleanFive H T
  have pol : P=Q := by
    apply Polynomial.eq_of_natDegree_lt_card_of_eval_eq' _ _ (bulkClocks A) _ (by omega)
    intro y hy
    obtain ⟨i,hi,rfl⟩ := Finset.mem_image.mp hy
    have e := congrFun eq i
    rw [bulkProfile_bulk A k w hi,bulkProfile_bulk A k v hi] at e
    exact e
  apply Prod.ext
  · funext j
    have same := congrArg (fun R:K[X]=>R.coeff j.val) pol
    change (ofFn (k+1) w.1).coeff j.val=(ofFn (k+1) v.1).coeff j.val at same
    rw [ofFn_coeff_eq_val_of_lt w.1 j.isLt,ofFn_coeff_eq_val_of_lt v.1 j.isLt] at same
    exact same
  · have e0 : w.2 0=v.2 0 := by simpa [bulkProfile] using congrFun eq 0
    have e1 : w.2 1=v.2 1 := by simpa [bulkProfile] using congrFun eq 4
    have e2 : w.2 2=v.2 2 := by simpa [bulkProfile] using congrFun eq 9
    funext j
    fin_cases j <;> assumption

theorem bulkProfile_range_five
    (ha : ∀ i j, i≤j → A i j=0) (ho : HasOrder 8 A b) (p : (11:K)=0)
    (five : (offKnots A).card=5) (cleanFive : (cleanKnots A).card=5)
    {theta : K} (H : ExceptionalHead A theta) (S : CenterPrefix A 4)
    {x z : Fin 10} (T : FiveCleanTail A x z) :
    LinearMap.range (bulkProfile A 5)=treeSpace A 5 ∧ finrank K (treeSpace A 5)=9 := by
  have sub : LinearMap.range (bulkProfile A 5)≤treeSpace A 5 := by
    rintro _ ⟨w,rfl⟩
    exact bulkProfile_mem ho p H S T (by decide) w
  have rk : finrank K (LinearMap.range (bulkProfile A 5)) =9 := by
    rw [LinearMap.finrank_range_of_inj (bulkProfile_injective five cleanFive H T (by decide)),
      Module.finrank_prod,Module.finrank_fin_fun,Module.finrank_fin_fun]
  have upper := backward_count ha ho 5 1 (by decide)
  have ge := Submodule.finrank_mono sub
  exact ⟨Submodule.eq_of_le_of_finrank_le sub (by omega),by omega⟩

end RKResearch.Certified.Graded.ERK8CharEleven.FiveOff

#print axioms RKResearch.Certified.Graded.ERK8CharEleven.FiveOff.bulkProfile_range_five
