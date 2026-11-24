module
public import RKCert.ERKOrderedQ7Core

@[expose] public section

/-! # Three available head powers buy the low two-endpoint contrast -/
namespace RKCert.Paired.FiniteMidpoint
open RKCert.Paired RKCert.Paired.Clock RKCert.OneEscape RKCert.Endpoint Polynomial Module
variable {K:Type*} [Field K] [CharZero K] {s r:ℕ}
variable {A:Fin (s+1)→Fin (s+1)→K} {b:Vec K (s+1)}
variable {U:Submodule K (Vec K (s+1))} {w:Vec K (s+1)} {G P:K[X]}
set_option maxHeartbeats 2000000

omit [CharZero K] in
theorem weighted_seven_budget (H:MarkedHead A 7 0 r U w) (R:K[X]) (hr:R.natDegree≤r) :
    weightedEval (nodes A) w R∈defectPlus A 0 6 := by
  have rTwo:=H.rTwo
  apply weighted_paid
  intro k hk
  have dK := le_natDegree_of_mem_supp k hk
  by_cases ck:k<r
  · exact Fplus_mono A 0 (by decide) (marked_power H (by decide) ck)
  have ek:r-1+1=k := by omega
  have p := Fplus_power (marked_power H (by decide) (k:=r-1) (by omega)) 1
  change (diag (nodes A)^1) ((diag (nodes A)^(r-1)) w)∈defectPlus A 0 6 at p
  rw [←ek,pow_succ']
  simpa only [pow_one,mul_apply_eq_comp] using p

theorem physical_seven_knot (ha:StrictLower A) (S:Saturated A b 7 0)
    (M:Margin A b 7 0 0) (C:EvenSevenChart A r U w G) (Pr:SevenProfile A r U w P)
    (Q:K[X]) (qn:Q≠0) (qd:Q.natDegree≤r) :
    ∃ k:Fin (s+1), ¬Live U k ∧ w k=0 ∧
      (Q*P).eval (nodes A k)≠0 ∧
      ∀ R:K[X], R.natDegree+Q.natDegree≤r→
        (Paired.primitive (R*(Q*P))).eval (nodes A k)=0 := by
  classical
  obtain ⟨e,he,eVal⟩:=core_indicator Pr.algebra
  have Pdeg := Pr.degree
  let c := nodes A
  let F := Q*P
  let W : Vec K (s+1) := weightedEval c w Q+weightedEval c e F
  let v := evalNodes A F-W
  have Fdeg : F.natDegree≤6 := natDegree_mul_le.trans (by omega)
  have hW : W∈defectPlus A 0 6 := by
    exact Submodule.add_mem _
      (weighted_seven_budget C.marked _ (by omega))
      (Fplus_mono A 0 (by omega) (C.marked.core (weighted_core C.marked F he)))
  have vn : v≠0 := by
    intro h
    have eF : evalNodes A F=W := sub_eq_zero.mp h
    have z := separated_plus S M F (by omega)
      (by rw [eF];exact Fplus_mono A 0 (by omega) hW)
    exact mul_ne_zero qn Pr.nonzero z
  let R := Finset.univ.filter (fun i=>v i≠0)
  have hR:R.Nonempty := by
    by_contra h
    apply vn
    ext i
    change v i=0
    by_contra hn
    exact h ⟨i,Finset.mem_filter.mpr ⟨Finset.mem_univ _,hn⟩⟩
  let k:=R.min' hR
  have hk : v k≠0 := (Finset.mem_filter.mp (R.min'_mem hR)).2
  have before (i:Fin (s+1)) (hi:i<k) : v i=0 := by
    by_contra hn
    exact (not_le_of_gt hi) (R.min'_le i (Finset.mem_filter.mpr ⟨Finset.mem_univ _,hn⟩))
  have hko : ¬Live U k := by
    intro h
    apply hk
    simp [v,W,eVal,h,Pr.disjoint k h,c]
  have hwk : w k=0 := by
    by_contra h
    apply hk
    simp [v,W,eVal,hko,Pr.repr k h,F,c]
  have Fk : F.eval (c k)≠0 := by
    intro h
    apply hk
    simpa [v,W,eVal,hko,hwk,c] using h
  have core_zero (u:Vec K (s+1)) (hu:u∈U) : u k=0 := by
    by_contra hn
    exact hko ⟨u,hu,hn⟩
  refine ⟨k,hko,hwk,Fk,?_⟩
  intro J hj
  let T:=J*F
  let WJ:=weightedEval c w (J*Q)+weightedEval c e T
  have qdeg : (J*Q).natDegree≤r := natDegree_mul_le.trans hj
  have jdeg : T.natDegree≤6 := by
    have h:=natDegree_mul_le (p:=J*Q) (q:=P)
    change (J*(Q*P)).natDegree≤6
    rw [←mul_assoc]
    omega
  have hWJ : WJ∈defectPlus A 0 6 := by
    exact Submodule.add_mem _
      (weighted_seven_budget C.marked _ (by omega))
      (Fplus_mono A 0 (by omega) (C.marked.core (weighted_core C.marked T he)))
  have eq : weightedEval c v J=evalNodes A T-WJ := by
    ext i
    simp only [weightedEval_apply,evalNodes_apply,Pi.sub_apply,Pi.add_apply,v,W,WJ,T,eval_mul]
    ring
  have hA : mat A (evalNodes A T-WJ) k=0 := by
    rw [←eq]
    have h := strictlyCausal_mat ha k (weightedEval c v J) 0 (fun i hi=>by simp [before i hi])
    simpa only [map_zero,Pi.zero_apply] using h
  let y:=evalNodes A (Paired.primitive T)-mat A (evalNodes A T-WJ)
  have dF : mat A (evalNodes A T)-evalNodes A (Paired.primitive T)∈defectPlus A 0 7 := by
    have h := primitive_defect A T jdeg
    exact (show zeroSpace A 7≤defectPlus A 0 7 from le_sup_left) (zeroSpace_mono A (by omega) h)
  have dW : mat A WJ∈defectPlus A 0 7 :=
    Fplus_mono A 0 (by omega) (Fplus_mat ha 0 6 ⟨_,hWJ,rfl⟩)
  have yh : y∈defectPlus A 0 7 := by
    dsimp [y]
    rw [map_sub,show evalNodes A (Paired.primitive T)-(mat A (evalNodes A T)-mat A WJ)=
      -(mat A (evalNodes A T)-evalNodes A (Paired.primitive T))+mat A WJ by abel]
    exact Submodule.add_mem _ (Submodule.neg_mem _ dF) dW
  rw [C.marked.paid 7 (by decide) le_rfl] at yh
  obtain ⟨u,hu,J0,_,h⟩:=exists_head_poly yh
  have eFinal := h k
  change (Paired.primitive T).eval (c k)-mat A (evalNodes A T-WJ) k=u k+J0.eval (c k)*w k at eFinal
  rwa [hA,core_zero u hu,hwk,mul_zero,add_zero,sub_zero] at eFinal

end RKCert.Paired.FiniteMidpoint
