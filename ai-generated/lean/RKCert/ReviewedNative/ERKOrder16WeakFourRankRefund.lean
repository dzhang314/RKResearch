module
public import RKCert.ReviewedNative.ERKOrder16WeakHead
import Mathlib.Tactic.Push
import Mathlib.Tactic.Ring
import Lean.Elab.Tactic.Omega

@[expose] public section

namespace RKResearch.Certified.ERK16
open RKResearch Polynomial Module RKCert.OneEscape RKCert.Endpoint RKCert.Endpoint.WeightedClock
open RKResearch.Certified.Graded RKResearch.Certified.Graded.Reverse
open RKResearch.Certified.Graded.Reverse.Thin
open scoped Classical BigOperators Matrix

noncomputable section
variable {K : Type*} [Field K] [LinearOrder K] [IsStrictOrderedRing K]
variable {A : Matrix (Fin 24) (Fin 24) K} {b w : Fin 24→K}
variable {U : Submodule K (Fin 24→K)} {Q P : K[X]}

/-- One more seed site, paid at E5 rather than E6. -/
theorem width24_quadratic_nine_sites (ha : ∀ i j,i≤j→A i j=0)
    (ho : HasOrder 16 A b) :
    9≤(weightedSites (reflectedClock A) (quadraticSeed A b)).card := by
  let S := weightedSites (reflectedClock A) (quadraticSeed A b)
  have cover := width24_quadratic_cover ha ho
  have eight : 8≤S.card := width24_quadratic_eight_sites ha ho
  by_contra! small
  change S.card<9 at small
  have ec : S.card=8 := by omega
  have out : coordinate (K:=K) (Fin.last 23)∉treeSpace A 5 :=
    fun h=>cover.frame.lastOut (treeSpace_mono A (by decide : 5≤7) h)
  have pay := primitiveBack_terminal_hull_budget ha ho cover.frame.lastLive cover.frame.seedZero
    (j:=5) (u:=8) ec (by decide) (by decide) out
  have h5 := grade_five_surplus_of_reviewed_order ha ho (by decide : 10≤16)
  have r5 := erk_midpoint_tree_rank ha ho (q:=5) (by decide) (by decide)
  change finrank K (treeSpace A 5)+8+5+1≤24 at pay
  omega

/-- Same grade-four peel as the checked weak-five admission, with the
intrinsic invariant core as its argument instead of the full carrier. -/
theorem weak_grade_four_of_invariant_strip
    (ha : ∀ i j,i≤j→A i j=0) (ho : HasOrder 16 A b)
    (rk : finrank K U=3) (stable : U.map (diag (nodes A))≤U)
    (seventh : zeroSpace A 7=chain (diag (nodes A)) U w 4)
    (unpaid : ((diag (nodes A))^4) w∉zeroSpace A 7) :
    finrank K (zeroSpace A 4)=4 ∧ zeroSpace A 4=U⊔(K∙w) := by
  let G := zeroSpace A 3
  let F := zeroSpace A 4
  let D := diag (nodes A)
  obtain ⟨inside,leQuad⟩ := weak_five_low_flag_of_strip stable seventh unpaid
  have j4 := coeff_separated ho (q:=4) (by decide)
  have ps : PolySeparated A 4 := PolySeparated.of_coeff j4
  have f3 : 2≤finrank K G := zeroSpace_finrank ha ho (by decide : 2+2≤16)
  have gap : finrank K G<finrank K F := Submodule.finrank_lt_finrank_of_lt
    (zeroSpace_strict_of_separation ha j4 (j:=3) (by decide) (by decide))
  have supCap : finrank K ↥(U⊔(K∙w))≤4 := by
    have e := Submodule.finrank_sup_add_finrank_inf_eq U (K∙w)
    have one : finrank K ↥(K∙w)≤1 := by
      by_cases z : w=0
      · rw [Submodule.span_singleton_eq_bot.mpr z,finrank_bot];decide
      · rw [finrank_span_singleton z]
    omega
  have cap : finrank K F≤4 := (Submodule.finrank_mono leQuad).trans supCap
  have four : finrank K F=4 := by
    by_contra ne
    have lower : finrank K G=2 := by omega
    have small : finrank K F=3 := by omega
    have esc : ¬G.map D≤G := by
      intro h
      have rise := clock_invariant_outgoing ha (ps.mono (by decide : 3≤4))
        (U:=G) le_rfl h
      change finrank K G+2≤finrank K F at rise
      omega
    have step : F=G⊔G.map D := zeroSpace_clock_step_of_unit
      (n:=3) (by change finrank K F≤finrank K G+1;omega) esc
    have inc : F≤U := step.symm ▸ sup_le inside ((Submodule.map_mono inside).trans stable)
    have eq : F=U := Submodule.eq_of_le_of_finrank_le inc (by change finrank K U≤finrank K F;omega)
    have stableF : F.map D≤F := eq.symm ▸ stable
    have rise := clock_invariant_incoming ha (j:=3) ps stableF
    change finrank K G+2≤finrank K F at rise
    omega
  refine ⟨four,Submodule.eq_of_le_of_finrank_le leQuad ?_⟩
  change finrank K ↥(U⊔(K∙w))≤finrank K F
  omega

/-- True carrier in F8 at the even endpoint. The original zero row
removes coefficient zero; the remaining 8×8 Cauchy square costs 16. -/
theorem width24_even_carrier_refund (ha : ∀ i j,i≤j→A i j=0)
    (ho : HasOrder 16 A b) : width24WeakFiveCarrier A b≤zeroSpace A 8 := by
  classical
  let H := width24WeakFiveCarrier A b
  have W := width24_quadratic_cover ha ho
  intro f hf
  change f∈H at hf
  have seed (i : Fin 24) (hi : quadraticSeed A b i≠0) : f i=0 :=
    Hidden.carrier_zero_on_active W.lastSeed hf hi
  have t8 : f∈treeSpace A 8 := by
    rw [←annih_annih (treeSpace A 8)]
    apply mem_annih.mpr
    intro u hu
    rw [W.band] at hu
    obtain ⟨R,_,rfl⟩ := mem_weightedBand.mp hu
    rw [row_apply,dotProduct]
    apply Finset.sum_eq_zero
    intro i _
    by_cases h : quadraticSeed A b i=0
    · simp [weightedEval_apply,h]
    · simp [seed i h]
  rw [treeSpace_coeff_sup ho (q:=8) (by decide)] at t8
  obtain ⟨_,⟨a,rfl⟩,v,hv,rep⟩ := Submodule.mem_sup.mp t8
  have f0 : f (0:Fin 24)=0 := (Hidden.mem_ambientHidden.mp hf).1 0
    (fun h=>((Hidden.mem_blindRows 0).mp h).1 rfl) (by decide)
  have v0 : v (0:Fin 24)=0 := origin_zeroSpace ha 8 hv
  have a0 : a 0=0 := by
    have e := congrFun rep 0
    rwa [Pi.add_apply,coeffEval_origin ha,v0,add_zero,f0] at e
  have mass (k : ℕ) : probe A b k f=0 := by
    have m := (Hidden.mem_ambientHidden.mp hf).2
    have same : probe A b k f=row b f := by
      rw [probe,row_apply,row_apply,dotProduct,dotProduct]
      apply Finset.sum_congr rfl
      intro i _
      have z := Hidden.carrier_mirror_weight_zero W.frame.lastClock hf i
      by_cases e : b i*f i=0
      · rw [show (b i*(nodes A i)^k)*f i=(b i*f i)*(nodes A i)^k by ring,e,zero_mul]
      · have one : nodes A i=1 := by
          have z' : (1-nodes A i)*(b i*f i)=0 := by simpa only [mul_assoc] using z
          exact (sub_eq_zero.mp ((mul_eq_zero.mp z').resolve_right e)).symm
        rw [one,one_pow,mul_one]
    rw [same,m]
  let aa : Fin 8→K := fun j=>a j.succ
  have tests (k : Fin 8) :
      (∑ j : Fin 8, aa j/((k.val+j.val+2:ℕ):K))=0 := by
    have kb : k.val+8+1≤16 := by have :=k.isLt;omega
    have vz : probe A b k.val v=0 := probe_zeroSpace ho kb hv
    have e := mass k.val
    rw [←rep,map_add,vz,add_zero,probe_coeffEval ho kb,Fin.sum_univ_succ,a0,zero_div,zero_add] at e
    simpa only [aa,Fin.val_succ,Nat.add_assoc,show (1:ℕ)+1=2 by decide] using e
  have aa0 := moments_detect ho (n:=8) (d:=2) (by decide) (by decide)
    (fun i j=>by have :=i.isLt;have :=j.isLt;omega) aa tests
  have az : a=0 := by
    ext j
    cases j using Fin.cases with
    | zero => exact a0
    | succ j => exact aa0 j
  rw [az,map_zero,zero_add] at rep
  exact rep ▸ hv

/-- Thus the genuine rank-four carrier plus five weighted head
powers saturates F8 and vanishes on the true contrast support. -/
theorem Width24OrdinaryWeakHead.rank_four_refund
    (L : Width24OrdinaryWeakHead A b U w Q P)
    (ha : ∀ i j,i≤j→A i j=0) (ho : HasOrder 16 A b)
    (seven : finrank K (zeroSpace A 7)=7)
    (four : finrank K (width24WeakFiveCarrier A b)=4) :
    finrank K U=3 ∧ U≤zeroSpace A 4 ∧ w∈zeroSpace A 4 ∧
      (∀ f∈zeroSpace A 8,∀ i∈weakFiveRows A b Q P,f i=0) := by
  classical
  let H := width24WeakFiveCarrier A b
  let y := reflectedClock A
  let S := weightedSites y (quadraticSeed A b)
  let W := weightedBand y w 5
  have base := L.flat.baseRank
  have r7 := L.flat.ranks 2 (by decide)
  change finrank K (zeroSpace A 7)=finrank K (zeroSpace A 5)+2 at r7
  have u3 : finrank K U=3 := by omega
  obtain ⟨_,F4⟩ := weak_grade_four_of_invariant_strip ha ho u3 L.flat.coreStable
    (L.flat.flags 2 (by decide)) L.flat.unpaid
  have U4 : U≤zeroSpace A 4 := F4.symm ▸ le_sup_left
  have w4 : w∈zeroSpace A 4 := by
    rw [F4]
    exact Submodule.mem_sup_right (Submodule.mem_span_singleton_self _)
  have cover := width24_quadratic_cover ha ho
  have s9 : 9≤S.card := width24_quadratic_nine_sites ha ho
  have van (R : K[X]) (d : R.natDegree≤4)
      (z : ∀ i,quadraticSeed A b i≠0→Q.eval (y i)*R.eval (y i)=0) : R=0 := by
    have prod : Q*R=0 := by
      apply eq_zero_of_degree_lt_of_eval_finset_eq_zero S
      · exact degree_le_natDegree.trans_lt (WithBot.coe_lt_coe.mpr
          ((natDegree_mul_le_of_le L.qDegree d).trans_lt (by omega : 4+4<S.card)))
      · intro x hx
        obtain ⟨i,hi,rfl⟩ := mem_weightedSites.mp hx
        rw [eval_mul]
        exact z i hi
    exact (mul_eq_zero.mp prod).resolve_left L.qNonzero
  have seed (i : Fin 24) (hi : quadraticSeed A b i≠0) : w i=Q.eval (y i) := by
    have h := L.qFit i
    rw [mul_comm (Q.eval (y i))] at h
    exact mul_left_cancel₀ hi h
  have wide : 5≤(weightedSites y w).card := by
    by_contra! sm
    let R := nodalHull (weightedSites y w)
    have rd : R.natDegree≤4 := by dsimp only [R]; rw [natDegree_nodalHull]; omega
    have rn : R≠0 := (monic_nodalHull _).ne_zero
    apply rn (van R rd ?_)
    intro i hi
    by_cases e : w i=0
    · rw [←seed i hi,e,zero_mul]
    · rw [nodalHull_eval_of_mem (mem_weightedSites.mpr ⟨i,e,rfl⟩),mul_zero]
  have w5 : finrank K W=5 := weightedBand_rank y w 5 wide
  have pdeg {R : K[X]} (h : R.degree<(5:WithBot ℕ)) : R.natDegree≤4 := by
    by_cases e : R=0
    · simp [e]
    · exact Nat.lt_succ_iff.mp ((natDegree_lt_iff_degree_lt e).mpr h)
  have W8 : W≤zeroSpace A 8 := by
    intro f hf
    obtain ⟨R,rd,rfl⟩ := mem_weightedBand.mp hf
    have af : (1-X:K[X]).natDegree≤1 := (natDegree_sub_le _ _).trans (by simp)
    have r4 : (R.comp (1-X)).natDegree≤4 :=
      natDegree_comp_le.trans (by simpa only [mul_one] using Nat.mul_le_mul (pdeg rd) af)
    have h := zeroSpace_mul_treeSpace ho (by decide : 4+1≤16) w4 (evalNodes_mem_treeSpace A _ r4)
    convert h using 1
    ext i
    simp only [weightedEval_apply,Pi.mul_apply,evalNodes_apply,eval_comp,eval_sub,eval_one,eval_X]
    change R.eval (1-nodes A i)*w i=w i*R.eval (1-nodes A i)
    ring
  have inter : H⊓W=(⊥:Submodule K (Fin 24→K)) := by
    apply le_antisymm _ bot_le
    intro f hf
    obtain ⟨hH,hW⟩ := Submodule.mem_inf.mp hf
    obtain ⟨R,rd,rfl⟩ := mem_weightedBand.mp hW
    have vz : R=0 := van R (pdeg rd) (by
      intro i hi
      have u := Hidden.carrier_zero_on_active cover.lastSeed hH hi
      rw [weightedEval_apply,seed i hi,mul_comm] at u
      exact u)
    rw [vz,map_zero]
    exact Submodule.zero_mem _
  have H8 : H≤zeroSpace A 8 := width24_even_carrier_refund ha ho
  have dim : finrank K ↥(H⊔W)=9 := by
    have e := Submodule.finrank_sup_add_finrank_inf_eq H W
    rw [inter,finrank_bot,add_zero,w5] at e
    change finrank K H=4 at four
    omega
  have all : H⊔W=zeroSpace A 8 :=
    Submodule.eq_of_le_of_finrank_le (sup_le H8 W8)
      (by rw [cover.frame.forward,dim])
  refine ⟨u3,U4,w4,?_⟩
  intro f hf i hi
  have showrow := reverse_contrast_true_support L.qFit L.pFit i ((mem_weakFiveRows i).mp hi)
  rw [←all] at hf
  obtain ⟨u,hu,v,hv,rfl⟩ := Submodule.mem_sup.mp hf
  obtain ⟨R,_,rfl⟩ := mem_weightedBand.mp hv
  have ui : u i=0 :=
    (mul_eq_zero.mp (Hidden.carrier_mirror_weight_zero cover.frame.lastClock hu i)).resolve_left
      (mul_ne_zero showrow.2.1 showrow.2.2.1)
  simp only [Pi.add_apply,weightedEval_apply,ui,showrow.2.2.2.2,mul_zero,add_zero]

end
end RKResearch.Certified.ERK16
