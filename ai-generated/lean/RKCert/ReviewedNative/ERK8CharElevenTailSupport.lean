module

public import RKCert.ReviewedNative.ERK8CharElevenHighWeights

import Mathlib.Tactic.FieldSimp
import Mathlib.Tactic.LinearCombination
import Mathlib.Tactic.Ring

@[expose] public section

/-! A degree-four pure test restricted to the literal seven off rows.
The clean-coordinate correction is grade four, not an assumed
identification of the tree space with a polynomial state space. -/
namespace RKResearch.Certified.Graded.ERK8CharEleven

open RKResearch Polynomial OneOff ERKTaggedHorizon ERK8PaidField LobattoEight RKCert.Endpoint
open scoped Matrix Classical BigOperators

variable {K : Type*} [Field K]
variable {A : Matrix (Fin 10) (Fin 10) K} {b : Fin 10 → K}

/-- Enforcing chronology and tags on the original physical stages.
The three last off rows are \(f,u,v\); any clean row after \(f\) has
zero reflected clock. -/
structure HighPhysicalTail (A : Matrix (Fin 10) (Fin 10) K) (f u v : Fin 10) : Prop where
  f_off : g A f ≠ 0
  u_off : g A u ≠ 0
  v_off : g A v ≠ 0
  fu : f < u
  uv : u < v
  earlier : ∀ j, g A j ≠ 0 → j < f ∨ j = f ∨ j = u ∨ j = v
  early_clean : ∀ j, g A j = 0 → f < j → nodes A j = 1

/-- Sender restriction by actual quadratic defect, without identifying
any physical rows or deleting a tableau coordinate. -/
noncomputable def offEval (A : Matrix (Fin 10) (Fin 10) K) (P : K[X]) : Fin 10 → K :=
  fun j => if g A j = 0 then 0 else P.eval (nodes A j)

theorem offEval_mem_treeSpace4 (three : (cleanKnots A).card = 3)
    {P : K[X]} (Pd : P.natDegree ≤ 2)
    (fit : ∀ j, g A j ≠ 0 → P.eval (nodes A j) = g A j)
    (nonzero_clean : ∀ x ∈ cleanKnots A, P.eval x ≠ 0)
    (U : K[X]) (Ud : U.natDegree ≤ 4) :
    offEval A U ∈ treeSpace A 4 := by
  let S := cleanKnots A
  let a : K → K := fun x => U.eval x / P.eval x
  let Q := Lagrange.interpolate S id a
  have Qd : Q.natDegree ≤ 2 := by
    by_cases q : Q = 0
    · simp [q]
    have t := (natDegree_lt_iff_degree_lt q).mpr
      (Lagrange.degree_interpolate_lt a (Set.injOn_id _) (s:=S))
    change Q.natDegree < (cleanKnots A).card at t
    omega
  have eq : offEval A U =
      evalNodes A (U-P*Q)+diag (g A) (evalNodes A Q) := by
    ext j
    simp only [offEval,Pi.add_apply,evalNodes_apply,eval_sub,eval_mul,diag_apply]
    by_cases gj : g A j = 0
    · have cl : nodes A j ∈ S := mem_cleanKnots.mpr ⟨j,gj,rfl⟩
      have e := Lagrange.eval_interpolate_at_node a (Set.injOn_id _) cl
      change Q.eval (nodes A j) = U.eval (nodes A j) / P.eval (nodes A j) at e
      have cancel := mul_div_cancel₀ (U.eval (nodes A j)) (nonzero_clean _ cl)
      simp [gj,e,cancel]
    · simp [gj,fit j gj]
  rw [eq]
  exact (treeSpace A 4).add_mem (evalNodes_mem_treeSpace A _
      (natDegree_sub_le_of_le Ud (natDegree_mul_le_of_le Pd Qd)))
    (zeroSpace_le_treeSpace A 4 (band_le A 2 (band_iff.mpr ⟨Q,Qd,rfl⟩)))

/-- At seven off and three clean clocks, the clean distribution is
exactly the three anchors already earned by the omitted-head proof. -/
theorem high_clean_clock_anchors (ha : ∀ i j, i ≤ j → A i j = 0) (ho : HasOrder 8 A b)
    (three : (cleanKnots A).card = 3) {theta : K} (H : ExceptionalHead A theta) :
    cleanKnots A = ({0,1,6} : Finset K) := by
  have h0 := zero_mem_cleanKnots (s:=9) ha
  have h1 : (1:K) ∈ cleanKnots A := mem_cleanKnots.mpr ⟨Fin.last 9,H.terminal_clean,H.terminal_clock⟩
  have n6 : (6:K)≠0 := (ho.natCast_isUnit (n:=6) (by decide) (by decide)).ne_zero
  have n5 : (5:K)≠0 := (ho.natCast_isUnit (n:=5) (by decide) (by decide)).ne_zero
  have n61 : (6:K)≠1 := fun e => n5 (by linear_combination e)
  have card : ({0,1,6} : Finset K).card = 3 := by
    simp [Finset.card_insert_of_notMem,zero_ne_one,n6.symm,n61.symm]
  have sub : ({0,1,6} : Finset K) ⊆ cleanKnots A := by
    intro x hx
    simp only [Finset.mem_insert,Finset.mem_singleton] at hx
    rcases hx with h|h|h
    · exact h.symm ▸ h0
    · exact h.symm ▸ h1
    · exact h.symm ▸ H.center_mem
  exact (Finset.eq_of_subset_of_card_le sub (by omega)).symm

theorem exceptional_quadratic_ne_at_anchors (ho : HasOrder 8 A b) (p : (11:K)=0)
    {x : K} (hx : x ∈ ({0,1,6} : Finset K)) : (exceptionalQuadratic : K[X]).eval x ≠ 0 := by
  have n8 : (8:K)≠0 := (ho.natCast_isUnit (n:=8) (by decide) (by decide)).ne_zero
  have n5 : (5:K)≠0 := (ho.natCast_isUnit (n:=5) (by decide) (by decide)).ne_zero
  simp only [Finset.mem_insert,Finset.mem_singleton] at hx
  rw [exceptionalQuadratic_eval]
  rcases hx with h|h|h
  · rw [h]
    intro e
    exact n8 (by linear_combination e)
  · rw [h]
    intro e
    exact n8 (by linear_combination e)
  · rw [h]
    intro e
    exact n5 (by linear_combination e-3*p)

theorem exceptional_quadratic_ne_off {theta : K} (H : ExceptionalHead A theta)
    {i : Fin 10} (gi : g A i ≠ 0) : (exceptionalQuadratic : K[X]).eval (nodes A i) ≠ 0 := by
  intro h
  exact gi (by rw [←H.fit i gi,h,mul_zero])

theorem high_offEval_mem_treeSpace4 (ha : ∀ i j, i ≤ j → A i j=0)
    (ho : HasOrder 8 A b) (p : (11:K)=0)
    (three : (cleanKnots A).card = 3) {theta : K} (H : ExceptionalHead A theta)
    (U : K[X]) (Ud : U.natDegree ≤ 4) : offEval A U ∈ treeSpace A 4 := by
  let P : K[X] := C theta * exceptionalQuadratic
  have Pd : P.natDegree ≤ 2 := (natDegree_C_mul_le _ _).trans exceptionalQuadratic_degree
  apply offEval_mem_treeSpace4 three Pd
      (fun j gj => by simpa only [P,eval_mul,eval_C] using H.fit j gj) _ U Ud
  intro x hx
  have nx := exceptional_quadratic_ne_at_anchors ho p ((high_clean_clock_anchors ha ho three H) ▸ hx)
  simpa only [P,eval_mul,eval_C] using mul_ne_zero H.scale_ne nx

/-- The three literal knots in the late physical off window. -/
noncomputable def highTailClocks (A : Matrix (Fin 10) (Fin 10) K) (f u v : Fin 10) : Finset K :=
  {nodes A f,nodes A u,nodes A v}

noncomputable def highPrefixHull (A : Matrix (Fin 10) (Fin 10) K) (f u v : Fin 10) : K[X] :=
  nodalHull (offKnots A \ highTailClocks A f u v)

noncomputable def highTailHull (A : Matrix (Fin 10) (Fin 10) K) (f u v : Fin 10) : K[X] :=
  nodalHull (highTailClocks A f u v)

noncomputable def highTailCofactor (A : Matrix (Fin 10) (Fin 10) K)
    (f u v : Fin 10) (x : K) : K :=
  (nodalHull ((highTailClocks A f u v).erase x)).eval x

theorem highTailCofactor_ne (A : Matrix (Fin 10) (Fin 10) K) (f u v : Fin 10) (x : K) :
    highTailCofactor A f u v x ≠ 0 :=
  nodalHull_eval_ne_zero_of_notMem (Finset.notMem_erase _ _)

theorem highTailClocks_subset {f u v : Fin 10} (T : HighPhysicalTail A f u v) :
    highTailClocks A f u v ⊆ offKnots A := by
  intro x hx
  simp only [highTailClocks,Finset.mem_insert,Finset.mem_singleton] at hx
  rcases hx with e|e|e
  · exact mem_offKnots.mpr ⟨f,T.f_off,e.symm⟩
  · exact mem_offKnots.mpr ⟨u,T.u_off,e.symm⟩
  · exact mem_offKnots.mpr ⟨v,T.v_off,e.symm⟩

theorem highTailClocks_distinct (seven : (offKnots A).card=7) (three : (cleanKnots A).card=3)
    {f u v : Fin 10} (T : HighPhysicalTail A f u v) :
    nodes A f ≠ nodes A u ∧ nodes A f ≠ nodes A v ∧ nodes A u ≠ nodes A v := by
  have inj := (order8_tag_injective_of_full_count (A:=A) (by omega)).2
  exact ⟨fun e => (ne_of_lt T.fu) (inj f u T.f_off T.u_off e),
    fun e => (ne_of_lt (T.fu.trans T.uv)) (inj f v T.f_off T.v_off e),
    fun e => (ne_of_lt T.uv) (inj u v T.u_off T.v_off e)⟩

theorem highTailClocks_card (seven : (offKnots A).card=7) (three : (cleanKnots A).card=3)
    {f u v : Fin 10} (T : HighPhysicalTail A f u v) :
    (highTailClocks A f u v).card = 3 := by
  obtain ⟨a,b,c⟩ := highTailClocks_distinct seven three T
  simp [highTailClocks,Finset.card_insert_of_notMem,a,b,c]

theorem highPrefixHull_degree (seven : (offKnots A).card=7) (three : (cleanKnots A).card=3)
    {f u v : Fin 10} (T : HighPhysicalTail A f u v) :
    (highPrefixHull A f u v).natDegree = 4 := by
  rw [highPrefixHull,natDegree_nodalHull,Finset.card_sdiff_of_subset (highTailClocks_subset T),
    seven,highTailClocks_card seven three T]

theorem highHull_factor {f u v : Fin 10} (T : HighPhysicalTail A f u v) :
    nodalHull (offKnots A) = highPrefixHull A f u v*highTailHull A f u v := by
  simp only [highPrefixHull,highTailHull,nodalHull]
  exact (Finset.prod_sdiff (highTailClocks_subset T)).symm

theorem highCofactor_factor {f u v : Fin 10} (T : HighPhysicalTail A f u v)
    {x : K} (hx : x ∈ highTailClocks A f u v) :
    offCofactor A x = (highPrefixHull A f u v).eval x*highTailCofactor A f u v x := by
  let U := highTailClocks A f u v
  let S := offKnots A
  have hsub : U.erase x ⊆ S.erase x := Finset.erase_subset_erase x (highTailClocks_subset T)
  have he : S.erase x \ U.erase x = S \ U := by
    ext y
    by_cases yx : y = x
    · simp [yx,show x∈U from hx]
    · simp [yx]
  unfold offCofactor highPrefixHull highTailCofactor
  change (nodalHull (S.erase x)).eval x =
      (nodalHull (S \ U)).eval x*(nodalHull (U.erase x)).eval x
  rw [←he,←eval_mul]
  exact congrArg (fun Q : K[X] => Q.eval x) ((Finset.prod_sdiff hsub).symm)

theorem highPrefixHull_ne {f u v : Fin 10} {x : K} (hx : x∈highTailClocks A f u v) :
    (highPrefixHull A f u v).eval x ≠ 0 :=
  nodalHull_eval_ne_zero_of_notMem (fun e => (Finset.mem_sdiff.mp e).2 hx)

theorem high_test_zero_before (seven : (offKnots A).card=7) (three : (cleanKnots A).card=3)
    {f u v : Fin 10} (T : HighPhysicalTail A f u v) {j : Fin 10} (jf : j < f) :
    offEval A (highPrefixHull A f u v) j = 0 := by
  unfold offEval
  by_cases gj : g A j=0
  · simp [gj]
  · simp [gj]
    apply nodalHull_eval_of_mem
    refine Finset.mem_sdiff.mpr ⟨mem_offKnots.mpr ⟨j,gj,rfl⟩,?_⟩
    have inj := (order8_tag_injective_of_full_count (A:=A) (by omega)).2
    intro hj
    simp only [highTailClocks,Finset.mem_insert,Finset.mem_singleton] at hj
    rcases hj with e|e|e
    · exact (ne_of_lt jf) (inj j f gj T.f_off e)
    · exact (ne_of_lt (jf.trans T.fu)) (inj j u gj T.u_off e)
    · exact (ne_of_lt (jf.trans (T.fu.trans T.uv))) (inj j v gj T.v_off e)

end RKResearch.Certified.Graded.ERK8CharEleven
