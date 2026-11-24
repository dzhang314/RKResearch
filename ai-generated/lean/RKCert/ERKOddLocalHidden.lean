module
public import RKCert.ERKOddLocalTrace
public import RKCert.CoreSupport

@[expose] public section
/-! # The finite coordinate algebra attached to a localized reverse band
No assumption is made that the early adjoint subspace itself is a coordinate
algebra. All masks are produced in this separate ordinary forward kernel. -/
namespace RKCert.Paired.ReverseHull
open RKCert.Paired.Clock RKCert.Paired.FiniteMidpoint RKCert.Endpoint Polynomial Module
variable {K:Type*} [Field K] [LinearOrder K] [IsStrictOrderedRing K]
variable {A:Fin 26→Fin 26→K}{b τ:Vec K 26}{r:ℕ}{U:Submodule K (Vec K 26)}
noncomputable section

def reverseHidden (b τ:Vec K 26)(U:Submodule K (Vec K 26)):Submodule K (Vec K 26) where
  carrier:={v|τ*v=0∧b*v∈U∧∀u∈U,v*u∈U}
  zero_mem':=by simp
  add_mem':=by
    intro v w hv hw
    exact ⟨by rw [mul_add,hv.1,hw.1,add_zero],
      by rw [mul_add];exact U.add_mem hv.2.1 hw.2.1,
      fun u hu=>by rw [add_mul];exact U.add_mem (hv.2.2 _ hu) (hw.2.2 _ hu)⟩
  smul_mem':=by
    intro a v hv
    exact ⟨by rw [mul_smul_comm,hv.1,smul_zero],
      by rw [mul_smul_comm];exact U.smul_mem _ hv.2.1,
      fun u hu=>by rw [smul_mul_assoc];exact U.smul_mem _ (hv.2.2 _ hu)⟩

omit [LinearOrder K] [IsStrictOrderedRing K] in
theorem mem_reverseHidden {v:Vec K 26} :
    v∈reverseHidden b τ U↔τ*v=0∧b*v∈U∧∀u∈U,v*u∈U:=Iff.rfl

omit [LinearOrder K] [IsStrictOrderedRing K] in
theorem reverse_hidden_mul :
    Clock.MulClosed (reverseHidden b τ U):=by
  intro v hv w hw
  obtain ⟨v0,vb,vu⟩:=mem_reverseHidden.mp hv
  obtain ⟨_,wb,wu⟩:=mem_reverseHidden.mp hw
  apply mem_reverseHidden.mpr
  refine ⟨by rw [←mul_assoc,v0,zero_mul],?_,?_⟩
  · rw [show b*(v*w)=v*(b*w) by ring]
    exact vu _ wb
  · intro u hu
    rw [mul_assoc]
    exact vu _ (wu _ hu)

theorem LocalLinearBand.forward_clock (B:LocalLinearBand A b r U τ):
    U.map (diag (nodes A))≤U:=by
  rintro _ ⟨v,h,rfl⟩
  have eq:diag (nodes A) v=v-diag (mirror A) v:=by
    ext i;simp only [diag_apply,Pi.sub_apply,mirror,Pi.one_apply];ring
  rw [eq]
  exact U.sub_mem h (B.clock (Submodule.mem_map_of_mem h))

theorem LocalLinearBand.hidden_invariant (B:LocalLinearBand A b r U τ):
    (reverseHidden b τ U).map (diag (nodes A))≤reverseHidden b τ U:=by
  rintro _ ⟨v,h,rfl⟩
  obtain ⟨eq,bv,vu⟩:=mem_reverseHidden.mp h
  have comm(u:Vec K 26):u*diag (nodes A) v=diag (nodes A) (u*v):=by
    ext i;simp only [Pi.mul_apply,diag_apply];ring
  apply mem_reverseHidden.mpr
  refine ⟨by rw [comm,eq,map_zero],by rw [comm];exact B.forward_clock (Submodule.mem_map_of_mem bv),?_⟩
  intro u hu
  rw [mul_comm,comm,mul_comm]
  exact B.forward_clock (Submodule.mem_map_of_mem (vu _ hu))

set_option maxHeartbeats 1000000 in
theorem LocalLinearBand.hidden_pure (B:LocalLinearBand A b r U τ)
    (ho:HasTreeOrderAtLeast A b 17):reverseHidden b τ U≤zeroSpace A 8:=by
  classical
  let : DecidableEq K:=Classical.decEq K
  intro v hv
  obtain ⟨V,Bv,vu⟩:=mem_reverseHidden.mp hv
  have haslow:1≤r ∧ r≤2:=by rcases B.short with e|e <;> omega
  have e:v∈treeSpace A 8:=by
    rw [←annih_annih_paired (treeSpace A 8)]
    apply mem_annih.mpr
    intro w hw
    obtain ⟨u,hu,P,_,eq⟩:=B.representation hw
    have pairU (u:Vec K 26)(hu:u∈U): row v u=0:=by
      have Z:=mem_annih.mp (B.base_annih ho (vu u hu)) (1:Vec K 26)
        (stageWeight_mem_space A .leaf (by change 1≤16-r+1;omega))
      simpa only [row_apply,Pi.mul_apply,Pi.one_apply,mul_one] using Z
    have pairP:row v (weightedEval (mirror A) τ P)=0:=by
      rw [row_apply]
      apply Finset.sum_eq_zero
      intro i _
      have vi:=congrFun V i
      simp only [Pi.mul_apply,Pi.zero_apply] at vi
      simp only [weightedEval_apply]
      calc
        _=P.eval (mirror A i)*(τ i*v i):=by ring
        _=0:=by rw [vi,mul_zero]
    rw [eq,map_add,pairU _ hu,pairP,add_zero]
  obtain ⟨a,rep⟩:=exists_poly_zeroSpace ho (by decide:8+1≤17) e
  let P:K[X]:=ofFn 9 a
  have dp:P.natDegree≤8:=by have e:=ofFn_natDegree_lt (by decide:0<9) a;change P.natDegree<9 at e;omega
  have T:OrdinaryTrace A 8 v P:=⟨dp,by rw [evalNodes_ofFn];exact rep⟩
  have zero:P=0:=by
    by_contra nz
    have h:=T.pair_polynomial ho P (by omega)
    have k:=mem_annih.mp (B.base_annih ho Bv) _ (evalNodes_mem_treeSpace A _ (dp.trans (by omega:8≤16-r)))
    have z:row (weightedEval (nodes A) b P) v=0:=by
      rw [row_apply] at k ⊢
      convert k using 1
      apply Finset.sum_congr rfl
      intro i _
      simp only [weightedEval_apply,evalNodes_apply,Pi.mul_apply]
      ring
    rw [z,formalPrimitive_eq_treePrimitive,←pow_two] at h
    have p:=RKCert.OrderedGram.pow_square_pos 0 P nz
    rw [pow_zero,one_mul] at p
    exact p.ne' h.symm
  have z:evalNodes A (0:K[X])=0:=by ext i;simp
  simpa only [zero,z,sub_zero] using T.pure

/-- Detect a genuine hidden ordinary defect from a vanished scalar trace.
Orthogonality and the true site count keep any early adjoint correction. -/
theorem LocalLinearBand.hidden_of_zero_profile (B:LocalLinearBand A b r U τ)
    (ho:HasTreeOrderAtLeast A b 17){j:ℕ}(pay:j+r≤8)
    {f:Vec K 26}(hf:f∈zeroSpace A j)(headZero:τ*f=0):f∈reverseHidden b τ U:=by
  have low:1≤r ∧ r≤2:=by rcases B.short with e|e <;> omega
  obtain ⟨u,hu,P,dp,fit⟩:=B.weight_trace ho hf (by omega)
  have P0:P=0:=by
    rcases dp with z|dp
    · exact z
    classical
    let y:=mirror A
    let T:=headSites y τ
    have count:9-r≤T.card:=B.sites
    apply eq_of_degrees_lt_of_eval_finset_eq T
    · exact degree_le_natDegree.trans_lt (by exact_mod_cast (show P.natDegree<T.card by omega))
    · exact degree_le_natDegree.trans_lt (by rw [natDegree_zero];exact_mod_cast (show 0<T.card by omega))
    intro x hx
    let z:=fiber y x τ
    have zo:z∈annih U:=fiber_mem (diag_annih_invariant B.clock) x B.orthogonal
    have zn:z≠0:=nonzero_fiber hx
    have b0:row z (b*f)=0:=by
      rw [row_apply]
      apply Finset.sum_eq_zero
      intro i _
      by_cases e:y i=x
      · have h:=congrFun headZero i
        simp only [Pi.mul_apply,Pi.zero_apply] at h
        simp only [z,fiber,e,ite_true,Pi.mul_apply]
        calc
          _=b i*(τ i*f i):=by ring
          _=0:=by rw [h,mul_zero]
      · simp [z,fiber,e]
    rw [fit,map_add,mem_annih.mp zo _ hu,zero_add,row_apply] at b0
    have E:(∑i,z i*weightedEval y τ P i)=P.eval x*(∑i,z i*z i):=by
      simp only [Finset.mul_sum];apply Finset.sum_congr rfl;intro i _
      rw [weightedEval_apply]
      by_cases e:y i=x
      · simp only [z,fiber,e,ite_true]
        ring
      · simp [z,fiber,e]
    rw [E] at b0
    have positive:(∑i,z i*z i)≠0:=by
      obtain ⟨i,n⟩:∃i,z i≠0:=by by_contra! e;exact zn (funext e)
      exact ne_of_gt ((mul_self_pos.mpr n).trans_le (Finset.single_le_sum
        (f:=fun i=>z i*z i) (fun i _=>mul_self_nonneg _) (Finset.mem_univ i)))
    rw [eval_zero]
    exact (mul_eq_zero.mp b0).resolve_right positive
  refine mem_reverseHidden.mpr ⟨headZero,?_,fun u hu=>B.mul_base ho pay hf hu⟩
  have e:b*f=u:=by simpa [P0] using fit
  rwa [e]
end
end RKCert.Paired.ReverseHull

