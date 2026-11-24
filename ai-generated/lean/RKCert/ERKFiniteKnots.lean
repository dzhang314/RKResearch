module
public import RKCert.ERKFiniteProfile

@[expose] public section

/-! # Two true causal knots from the marked finite chart -/
namespace RKCert.Paired.FiniteMidpoint
open RKCert.Paired RKCert.Paired.Clock RKCert.OneEscape RKCert.Endpoint Polynomial Module
set_option maxHeartbeats 1700000
variable {K:Type*} [Field K] [CharZero K] {s q ε d a r:ℕ}
variable {A:Fin (s+1)→Fin (s+1)→K} {b:Vec K (s+1)}
variable {U:Submodule K (Vec K (s+1))} {w:Vec K (s+1)} {G P:K[X]}

omit [CharZero K] in
theorem Fplus_power {v:Vec K (s+1)} {j:ℕ} (hv:v∈defectPlus A d j) (k:ℕ) :
    (diag (nodes A)^k) v∈defectPlus A d (j+k) := by
  induction k with
  | zero => simpa using hv
  | succ n ih =>
    rw [show j+(n+1)=j+n+1 by omega,pow_succ']
    exact Fplus_clock A d (j+n) ⟨_,ih,rfl⟩

omit [CharZero K] in
theorem weighted_head_budget (hq:5≤q) (H:MarkedHead A q d r U w)
    (Q:K[X]) {j:ℕ} (hj:5≤j) (hd:Q.natDegree+4≤j) :
    weightedEval (nodes A) w Q∈defectPlus A d j := by
  have rtwo:=H.rTwo
  have w0:=marked_power H hq (k:=0) (by omega)
  have w1:=marked_power H hq (k:=1) (by omega)
  change diag (nodes A) w∈defectPlus A d 5 at w1
  apply weighted_paid
  intro k hk
  have kn:=le_natDegree_of_mem_supp k hk
  by_cases h:k=0
  · subst k
    exact Fplus_mono A d hj w0
  · let D := diag (nodes A)
    have kp : (D^(k-1+1)) w = (D^(k-1)) (D w) := by rw [pow_succ];rfl
    have k1 : k-1+1=k := by omega
    rw [k1] at kp
    change (D^k) w∈defectPlus A d j
    rw [kp]
    exact Fplus_mono A d (by omega) (Fplus_power w1 _)

omit [CharZero K] in
theorem weighted_core (H:MarkedHead A q d r U w) (R:K[X]) {u:Vec K (s+1)}
    (hu:u∈U) : weightedEval (nodes A) u R∈U := by
  have e : weightedEval (nodes A) u R = fun i=>R.eval (nodes A i)*u i := by ext i;simp only [weightedEval_apply]
  rw [e]
  exact poly_preserves H.stable R u hu

theorem physical_knot (ha:StrictLower A) (hq:8≤q) (S:Saturated A b q ε)
    (M:Margin A b q ε d) (C:Chart A q ε d a r U w G) (Pr:Profile A q a U w G P)
    (Q:K[X]) (qn:Q≠0) (qd:Q.natDegree≤q-5) :
    ∃ k:Fin (s+1), ¬Live U k ∧ w k=0 ∧ G.eval (nodes A k)=0 ∧
      (Q*P).eval (nodes A k)≠0 ∧
      ∀ R:K[X], R.natDegree+Q.natDegree≤q-5→
        (Paired.primitive (R*(Q*P))).eval (nodes A k)=0 := by
  classical
  obtain ⟨e,he,eVal⟩:=core_indicator Pr.algebra
  have Pdeg := Pr.degree
  let c := nodes A
  let F := Q*P
  let W : Vec K (s+1) := weightedEval c w Q+weightedEval c e F
  let v := evalNodes A F-W
  have Fdeg : F.natDegree≤q-1 := natDegree_mul_le.trans (by omega)
  have hW : W∈defectPlus A d (q-1) := by
    exact Submodule.add_mem _
      (weighted_head_budget (by omega) C.marked _ (by omega) (by omega))
      (Fplus_mono A d (by omega) (C.marked.core (weighted_core C.marked F he)))
  have vn : v≠0 := by
    intro h
    have eF : evalNodes A F=W := sub_eq_zero.mp h
    have z := separated_plus S M F (by omega)
      (by rw [eF];exact Fplus_mono A d (by omega) hW)
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
  have Gk : G.eval (c k)=0 := by
    have h := C.meshPaid
    rw [C.marked.edge] at h
    obtain ⟨u,hu,Q,_,huQ⟩:=exists_head_poly h
    simpa [c,core_zero u hu,hwk] using huQ k
  refine ⟨k,hko,hwk,Gk,Fk,?_⟩
  intro J hj
  let T:=J*F
  let WJ:=weightedEval c w (J*Q)+weightedEval c e T
  have qdeg : (J*Q).natDegree≤q-5 := natDegree_mul_le.trans hj
  have jdeg : T.natDegree≤q-1 := by
    have h:=natDegree_mul_le (p:=J*Q) (q:=P)
    change (J*(Q*P)).natDegree≤q-1
    rw [←mul_assoc]
    omega
  have hWJ : WJ∈defectPlus A d (q-1) := by
    exact Submodule.add_mem _
      (weighted_head_budget (by omega) C.marked _ (by omega) (by omega))
      (Fplus_mono A d (by omega) (C.marked.core (weighted_core C.marked T he)))
  have eq : weightedEval c v J=evalNodes A T-WJ := by
    ext i
    simp only [weightedEval_apply,evalNodes_apply,Pi.sub_apply,Pi.add_apply,v,W,WJ,T,eval_mul]
    ring
  have hA : mat A (evalNodes A T-WJ) k=0 := by
    rw [←eq]
    have h := strictlyCausal_mat ha k (weightedEval c v J) 0 (fun i hi=>by simp [before i hi])
    simpa only [map_zero,Pi.zero_apply] using h
  let y:=evalNodes A (Paired.primitive T)-mat A (evalNodes A T-WJ)
  have dF : mat A (evalNodes A T)-evalNodes A (Paired.primitive T)∈defectPlus A d q := by
    have h := primitive_defect A T jdeg
    exact (show zeroSpace A q≤defectPlus A d q from le_sup_left) (zeroSpace_mono A (by omega) h)
  have dW : mat A WJ∈defectPlus A d q :=
    Fplus_mono A d (by omega) (Fplus_mat ha d (q-1) ⟨_,hWJ,rfl⟩)
  have yh : y∈defectPlus A d q := by
    dsimp [y]
    rw [map_sub,show evalNodes A (Paired.primitive T)-(mat A (evalNodes A T)-mat A WJ)=
      -(mat A (evalNodes A T)-evalNodes A (Paired.primitive T))+mat A WJ by abel]
    exact Submodule.add_mem _ (Submodule.neg_mem _ dF) dW
  rw [C.marked.paid q (by omega) le_rfl] at yh
  obtain ⟨u,hu,J0,_,h⟩:=exists_head_poly yh
  have eFinal := h k
  change (Paired.primitive T).eval (c k)-mat A (evalNodes A T-WJ) k=u k+J0.eval (c k)*w k at eFinal
  rwa [hA,core_zero u hu,hwk,mul_zero,add_zero,sub_zero] at eFinal

end RKCert.Paired.FiniteMidpoint

