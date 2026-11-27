module

public import RKCert.ReviewedNative.ERK8CharElevenFourReverse
public import RKCert.ReviewedNative.ERK8CharElevenFiveWeights

import Mathlib.Tactic.FinCases
import Mathlib.Tactic.LinearCombination
import Mathlib.Tactic.Ring

@[expose] public section

/-! # Centered four-off: one paid test replaces the full cofactor ratio
The original repeated columns are retained. A quartic nodal test, cut
at the three anchor tags, pairs directly with the physical row difference. -/
namespace RKResearch.Certified.Graded.ERK8CharEleven.FourOff

open RKResearch Polynomial OneOff ERKTaggedHorizon ERK8PaidField Reverse FourOffPhysical
open FourOffNewton
open RKResearch.Certified.Graded.MultiOff.FourOff8CleanShape (CleanPrimitivePlacement)
open scoped Classical Matrix BigOperators

variable {K : Type*} [Field K]
variable {A : Matrix (Fin 10) (Fin 10) K} {b : Fin 10 → K} {P : K[X]} {dup k : Fin 10}

theorem exceptional_head_of_centered_four
    (p : (11:K)=0) (M : Placement A b P dup k)
    (L : CleanPrimitivePlacement A b k 6 (nodes A 7))
    (center : nodes A k=6) {theta : K} (tn : theta≠0) (fit : P=C theta*exceptionalQuadratic) :
    ExceptionalHead A theta := by
  refine ⟨tn,?_,M.rankData.bandFour,M.rankData.cleanNine,M.rankData.clockNine,
    M.rankData.uniqueOne, mem_cleanKnots.mpr ⟨k,M.firstClean,center⟩,?_⟩
  · intro i gi
    have h := M.rankData.fit i gi
    rwa [fit,eval_mul,eval_C] at h
  · intro i gi
    rcases marked_clean_value_census M i gi with h|h|h|h|h
    · exact Or.inl h
    · exact Or.inr (Or.inr (Or.inl (h.trans center)))
    · exact Or.inr (Or.inr (Or.inr (h ▸ (clean_center_or_quadratic p L.roots.root_x).resolve_left
        (fun h6=> L.roots.h_ne_x (center.trans h6.symm)))))
    · exact Or.inr (Or.inr (Or.inr (h ▸ (clean_center_or_quadratic p L.roots.root_z).resolve_left
        (fun h6=> L.roots.h_ne_z (center.trans h6.symm)))))
    · exact Or.inr (Or.inl h)

theorem actual_clean_center_prefix
    (ha : ∀ i j, i≤j → A i j=0) (ho : HasOrder 8 A b)
    (M : Placement A b P dup k) (center : nodes A k=6) :
    FiveOff.CenterPrefix A k := by
  have atK := M.firstAtFourOrFive
  refine ⟨M.rankData.clockZero,M.rankData.cleanZero,center,M.firstClean,
    by omega,by change k.val < 9; omega,M.noEarlierNonzeroClean,?_⟩
  exact first_nonzero_clean_has_three_off_clocks ha ho M.rankData.bandFour M.rankData.fit
    M.firstClean M.firstClockNe (fun j hj gj=>by
      rw [M.noEarlierNonzeroClean j hj gj,M.rankData.clockZero])

theorem clean_masses_through_two
    (M : Placement A b P dup k) (center : nodes A k=6)
    (L : CleanPrimitivePlacement A b k 6 (nodes A 7))
    (F : K[X]) (van : ∀ t∈({0,1,6}:Finset K), F.eval t=0) :
    probe A b 0 (evalNodes A F)=
      cleanMass A b (nodes A 6)*F.eval (nodes A 6)+
      cleanMass A b (nodes A 7)*F.eval (nodes A 7) := by
  have eb : probe A b 0 (evalNodes A F)=row b (evalNodes A F) := by simp [probe]
  rw [eb,row_evalNodes_tag_sum]
  have o : (∑ t∈offKnots A,offMass A b t*F.eval t)=0 :=
    Finset.sum_eq_zero (fun t ht=>by rw [M.rankData.cancel t ht,zero_mul])
  rw [o,add_zero]
  let T : Finset K := {nodes A 6,nodes A 7}
  have sub : T⊆cleanKnots A := by
    intro t ht
    simp only [T,Finset.mem_insert,Finset.mem_singleton] at ht
    rcases ht with rfl|rfl
    · exact mem_cleanKnots.mpr ⟨6,M.cleanSix,rfl⟩
    · exact mem_cleanKnots.mpr ⟨7,M.cleanSeven,rfl⟩
  have sum : (∑ t∈T,cleanMass A b t*F.eval t)=
      ∑ t∈cleanKnots A,cleanMass A b t*F.eval t := by
    apply Finset.sum_subset sub
    intro t ht nh
    obtain ⟨i,gi,rfl⟩ := mem_cleanKnots.mp ht
    rcases marked_clean_value_census M i gi with h|h|h|h|h
    · rw [van _ (by simp [h]),mul_zero]
    · rw [van _ (by simp [h,center]),mul_zero]
    · exact (nh (by simp [T,h])).elim
    · exact (nh (by simp [T,h])).elim
    · rw [van _ (by simp [h]),mul_zero]
  rw [←sum,show T={nodes A 6,nodes A 7} from rfl,Finset.sum_pair L.roots.x_ne_z]

theorem centered_clean_masses_match
    (ho : HasOrder 8 A b) (p : (11:K)=0) (M : Placement A b P dup k) (center : nodes A k=6)
    (L : CleanPrimitivePlacement A b k 6 (nodes A 7))
    (s : nodes A 6+nodes A 7=1) (m : nodes A 6*nodes A 7=8) :
    cleanMass A b (nodes A 6)=cleanMass A b (nodes A 7) ∧
      cleanMass A b (nodes A 7)≠0 := by
  let x := nodes A 6
  let z := nodes A 7
  let F : K[X] := highAnchorHull
  have xs : x^2-x+8=0 := by linear_combination x*s-m
  have qx : (exceptionalQuadratic : K[X]).eval x=0 := by rwa [exceptionalQuadratic_eval]
  have anti : F.eval z= -F.eval x := by
    have z1 : z=1-x := by linear_combination s
    rw [z1]
    simp only [F,highAnchorHull,eval_mul,eval_sub,eval_X,eval_C]
    linear_combination x*(1-x)*p
  have Xna : x∉({0,1,6}:Finset K) :=
    fun h=>exceptional_quadratic_ne_at_anchors ho p h qx
  have X0 : x≠0 := fun e=>Xna (by simp [e])
  have X1 : x≠1 := fun e=>Xna (by simp [e])
  have X6 : x≠6 := fun e=>Xna (by simp [e])
  have xn : F.eval x≠0 := by
    simp only [F,highAnchorHull,eval_mul,eval_sub,eval_X,eval_C]
    exact mul_ne_zero (mul_ne_zero X0 (sub_ne_zero.mpr X6)) (sub_ne_zero.mpr X1)
  have c := clean_masses_through_two M center L F (fun _ ht=>highAnchorHull_zero ht)
  rw [show F=highAnchorHull from rfl,paid_anchor_probe_zero ho p] at c
  change 0=cleanMass A b x*F.eval x+cleanMass A b z*F.eval z at c
  rw [anti] at c
  refine ⟨?_, M.rankData.cleanMassNe _ (mem_cleanKnots.mpr ⟨7,M.cleanSeven,rfl⟩)⟩
  apply mul_right_cancel₀ xn
  linear_combination -c

noncomputable def centeredMask (A : Matrix (Fin 10) (Fin 10) K) (F : K[X]) : Fin 10→K :=
  fun i=>if g A i=0 ∧ nodes A i∈({0,1,6}:Finset K) then 0 else F.eval (nodes A i)

theorem centeredMask_mem
    (ho : HasOrder 8 A b) (p : (11:K)=0) {theta : K} (H : ExceptionalHead A theta)
    (F : K[X]) (Fd : F.natDegree≤4) :
    centeredMask A F∈treeSpace A 4 := by
  let q : K[X] := exceptionalQuadratic
  let S : Finset K := {0,1,6}
  let r (t : K) := -F.eval t/q.eval t
  let R := Lagrange.interpolate S id r
  have n6 : (6:K)≠0 := (ho.natCast_isUnit (n:=6) (by decide) (by decide)).ne_zero
  have n5 : (5:K)≠0 := (ho.natCast_isUnit (n:=5) (by decide) (by decide)).ne_zero
  have n61 : (6:K)≠1 := fun e=>n5 (by linear_combination e)
  have card : S.card=3 := by simp [S,Finset.card_insert_of_notMem,zero_ne_one,n6.symm,n61.symm]
  have Rd : R.natDegree≤2 := by
    by_cases e : R=0
    · simp [e]
    have d := (natDegree_lt_iff_degree_lt e).mpr
      (Lagrange.degree_interpolate_lt r (Set.injOn_id _) (s:=S))
    change R.natDegree < S.card at d
    omega
  let W := evalNodes A (F+q*R)-theta⁻¹ • diag (g A) (evalNodes A R)
  have deg : (F+q*R).natDegree≤4 := natDegree_add_le_of_degree_le Fd
    (natDegree_mul_le_of_le exceptionalQuadratic_degree Rd)
  have defect : diag (g A) (evalNodes A R)∈zeroSpace A 4 :=
    band_le A 2 (band_iff.mpr ⟨R,Rd,rfl⟩)
  have mem : W∈treeSpace A 4 :=
    (treeSpace A 4).sub_mem (evalNodes_mem_treeSpace A _ deg)
      ((treeSpace A 4).smul_mem _ (zeroSpace_le_treeSpace A 4 defect))
  have eq : centeredMask A F=W := by
    ext i
    by_cases gi : g A i=0
    · by_cases hi : nodes A i∈S
      · have qn := exceptional_quadratic_ne_at_anchors ho p hi
        have h := Lagrange.eval_interpolate_at_node r (Set.injOn_id _) hi
        change R.eval (nodes A i)= -F.eval (nodes A i)/q.eval (nodes A i) at h
        have n : q.eval (nodes A i)≠0 := qn
        simp only [W,centeredMask,gi,true_and,show nodes A i∈({0,1,6}:Finset K) from hi,
          ite_true,Pi.sub_apply,Pi.smul_apply,smul_eq_mul,diag_apply,evalNodes_apply,eval_add,
          eval_mul,zero_mul,mul_zero,sub_zero,h,mul_div_cancel₀ _ n,add_neg_cancel]
      · have q0 : q.eval (nodes A i)=0 := by
          rcases H.clean_roots i gi with e|e|e|e
          · exact (hi (by simp [S,e])).elim
          · exact (hi (by simp [S,e])).elim
          · exact (hi (by simp [S,e])).elim
          · exact e
        simp [W,centeredMask,S,gi,hi,q0]
    · have e : theta⁻¹*theta=1 := inv_mul_cancel₀ H.scale_ne
      simp only [centeredMask,gi,false_and,ite_false,W,Pi.sub_apply,Pi.smul_apply,smul_eq_mul,
        diag_apply,evalNodes_apply,eval_add,eval_mul]
      rw [←H.fit i gi]
      change _ = F.eval (nodes A i)+q.eval (nodes A i)*R.eval (nodes A i)-
        theta⁻¹*(theta*q.eval (nodes A i)*R.eval (nodes A i))
      linear_combination q.eval (nodes A i)*R.eval (nodes A i)*e
  rw [eq]
  exact mem

theorem centered_mask_pairs_two
    (ha : ∀ i j, i≤j → A i j=0) (ho : HasOrder 8 A b) (p : (11:K)=0)
    (M : Placement A b P dup k) (center : nodes A k=6) {theta : K} (H : ExceptionalHead A theta)
    (F : K[X]) (Fd : F.natDegree≤4) (Fv : ∀ t∈offKnots A,F.eval t=0)
    (q6 : (exceptionalQuadratic : K[X]).eval (nodes A 6)=0)
    (q7 : (exceptionalQuadratic : K[X]).eval (nodes A 7)=0) :
    repeatDifference A dup 6*F.eval (nodes A 6)+repeatDifference A dup 7*F.eval (nodes A 7)=0 := by
  let W := centeredMask A F
  let Δ := repeatDifference A dup
  have s := mem_annih.mp (repeatDifference_annih M) W (centeredMask_mem ho p H F Fd)
  have e6 : W 6=F.eval (nodes A 6) := by
    have n : nodes A 6∉({0,1,6}:Finset K) :=
      fun h=>exceptional_quadratic_ne_at_anchors ho p h q6
    simp only [W,centeredMask,n,and_false,ite_false]
  have e7 : W 7=F.eval (nodes A 7) := by
    have n : nodes A 7∉({0,1,6}:Finset K) :=
      fun h=>exceptional_quadratic_ne_at_anchors ho p h q7
    simp only [W,centeredMask,n,and_false,ite_false]
  change row Δ W=0 at s
  rw [row_apply,dotProduct,FiveOff.sum_pair_of_support (by decide : (6:Fin 10)≠7)] at s
  · rwa [e6,e7] at s
  · intro j j6 j7
    by_cases j8 : j=8
    · subst j
      rw [show Δ 8=0 from repeatDifference_eight_zero ha M.repeatAtEight,zero_mul]
    by_cases j9 : j=9
    · subst j
      simp [W,centeredMask,M.cleanNine,M.rankData.clockNine]
    have lt : j < 6 := by omega
    by_cases j0 : j=0
    · subst j
      simp [W,centeredMask,M.rankData.cleanZero,M.rankData.clockZero]
    by_cases gj : g A j=0
    · have jk := M.onlyCleanInMiddle j (lt_of_le_of_ne (Fin.zero_le _) (Ne.symm j0)) lt gj
      subst j
      simp [W,centeredMask,gj,center]
    · have h := Fv _ (mem_offKnots.mpr ⟨j,gj,rfl⟩)
      simp [W,centeredMask,gj,h]

/-- This consumes only the vanishing quartic and its linear residue,
not a six-node coefficient formula or a nonzero off-row coefficient. -/
theorem centered_tail_contradiction
    (ha : ∀ i j, i≤j → A i j=0) (ho : HasOrder 8 A b) (p : (11:K)=0)
    (M : Placement A b P dup k) (center : nodes A k=6)
    (L : CleanPrimitivePlacement A b k 6 (nodes A 7))
    {theta : K} (H : ExceptionalHead A theta)
    (s : nodes A 6+nodes A 7=1) (m : nodes A 6*nodes A 7=8)
    (F : K[X]) (Fd : F.natDegree≤4) (Fv : ∀ t∈offKnots A,F.eval t=0)
    {beta : K} (bn : beta≠0) {U : K[X]}
    (rem : F=C beta*(C 6+C 2*X)+exceptionalQuadratic*U) : False := by
  let x := nodes A 6
  let z := nodes A 7
  let W₆ := cleanMass A b x
  let W₇ := cleanMass A b z
  let lam := b 8*reflectedClock A 8
  let Δ := repeatDifference A dup
  have qx : (exceptionalQuadratic : K[X]).eval x=0 := by
    rw [exceptionalQuadratic_eval]
    linear_combination x*s-m
  have qz : (exceptionalQuadratic : K[X]).eval z=0 := by
    rw [exceptionalQuadratic_eval]
    linear_combination z*s-m
  have x1 : x≠1 := fun e=>exceptional_quadratic_ne_at_anchors ho p (by simp [e]) qx
  have z1 : z≠1 := fun e=>exceptional_quadratic_ne_at_anchors ho p (by simp [e]) qz
  have xn : x≠0 := fun e=>exceptional_quadratic_ne_at_anchors ho p (by simp [e]) qx
  have Fx : F.eval x=beta*(6+2*x) := by rw [rem]; simp [qx]
  have Fz : F.eval z=beta*(6+2*z) := by rw [rem]; simp [qz]
  obtain ⟨eqW,nW⟩ := centered_clean_masses_match ho p M center L s m
  obtain ⟨ξ,e7,e7',e6,e6'⟩ := late_reflected_repeat_equations ha ho M x1 z1
  have ys : reflectedClock A 6=z := by
    change 1-x=z
    linear_combination -s
  have yz : reflectedClock A 7=x := by
    change 1-z=x
    linear_combination -s
  rw [yz] at e7 e7' e6 e6'
  rw [ys] at e6 e6'
  let D := 3*b 8*(reflectedClock A 8)^2-ξ
  change 2*lam*Δ 7=W₇*x^2 at e7
  change D*Δ 7=W₇*x^3 at e7'
  change 2*(W₇*x*A 7 6+lam*Δ 6)=W₆*z^2 at e6
  change 3*(W₇*x^2*A 7 6)+D*Δ 6=W₆*z^3 at e6'
  have nΔ : Δ 7≠0 := by
    intro v
    rw [v,mul_zero] at e7
    exact (mul_ne_zero nW (pow_ne_zero _ xn)) e7.symm
  have coef : D=2*lam*x := by
    apply mul_right_cancel₀ nΔ
    linear_combination e7'-x*e7
  change W₆=W₇ at eqW
  rw [coef,eqW] at e6'
  rw [eqW] at e6
  have first : 2*lam*x*Δ 6=W₇*z^2*(3*x-2*z) := by
    linear_combination 3*x*e6-2*e6'
  have pair := centered_mask_pairs_two ha ho p M center H F Fd Fv qx qz
  change Δ 6*F.eval x+Δ 7*F.eval z=0 at pair
  rw [Fx,Fz] at pair
  have close : (6+2*z)*x^3+(6+2*x)*z^2*(3*x-2*z)=0 := by
    apply mul_left_cancel₀ nW
    apply mul_left_cancel₀ bn
    linear_combination 2*lam*x*pair-beta*(6+2*x)*first-beta*(6+2*z)*x*e7
  exact impossible_four_late p s m close

end RKResearch.Certified.Graded.ERK8CharEleven.FourOff

#print axioms RKResearch.Certified.Graded.ERK8CharEleven.FourOff.centered_tail_contradiction
