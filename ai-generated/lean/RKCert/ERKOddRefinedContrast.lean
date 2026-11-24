module
public import RKCert.ERKOddFourAxis
public import RKCert.ERKOddLocalHeadTrace

@[expose] public section
/-! # The exceptional extra axis is removed from the actual contrast
The removed contribution lies in the early adjoint space. No nonzero
physical axis node is discarded from the chronological tableau. -/
namespace RKCert.Paired.ReverseHull
open RKCert.Paired.Clock RKCert.Paired.FiniteMidpoint RKCert.Endpoint Polynomial
open scoped Classical
variable {K:Type*} [Field K] [LinearOrder K] [IsStrictOrderedRing K]
variable {A:Fin 26→Fin 26→K}{b τ h ξ W:Vec K 26}{U:Submodule K (Vec K 26)}{Q:K[X]}
noncomputable section

set_option maxHeartbeats 3900000 in
theorem LocalLinearBand.refine_by_second_axis (B:LocalLinearBand A b 2 U τ)
    (ho:HasTreeOrderAtLeast A b 17)
    (D:LocalFourAxis A b τ h ξ U)(H:LocalHeadContrast A b τ h W U Q)
    (value:∀i,W i=if (¬Clock.Live (reverseHidden b τ U) i)∧h i=0
        then Q.eval (mirror A i)*b i else 0):
    ∃W':Vec K 26,LocalHeadContrast A b τ h W' U Q∧∀i,W' i≠0→ξ i=0:=by
  classical
  let G:=reverseHidden b τ U
  let y:=mirror A
  let V:Vec K 26:=fun i=>if ξ i=0 then W i else 0
  have Vval(i:Fin 26):V i=(if ξ i=0 then W i else 0):=rfl
  obtain ⟨u,uU,P,_,rep⟩:=D.bRefund
  have xInv:U.map (diag ξ)≤U:=by
    rintro _ ⟨v,vU,rfl⟩
    exact B.mul_base ho (by decide) D.sixth vU
  have hInv:U.map (diag h)≤U:=by
    rintro _ ⟨v,vU,rfl⟩
    exact H.preserved v vU
  let z:Vec K 26:=fun i=>Q.eval (y i)/ξ i*u i
  have zU:z∈U:=joint_selector_mem B.clock xInv uU (fun a x=>Q.eval a/x)
  let q:=fiber h 0 z
  have qU:q∈U:=fiber_mem hInv 0 zU
  obtain ⟨e,eG,eAt⟩:=core_indicator (reverse_hidden_mul (τ:=τ) (b:=b) (U:=U))
  have e_at(i:Fin 26):e i=(if Clock.Live G i then 1 else 0):=eAt i
  let c:=q-e*q
  have cU:c∈U:=U.sub_mem qU ((mem_reverseHidden.mp eG).2.2 _ qU)
  have eW:W-V=c:=by
    ext i
    have d:W i=(if (¬Clock.Live G i)∧h i=0 then Q.eval (y i)*b i else 0):=value i
    have ig:W i-V i=q i-e i*q i:=by
      by_cases live:Clock.Live G i
      · have e1:e i=1:=by rw [e_at,ite_eq_left live]
        have w0:W i=0:=by rw [d,ite_eq_right (fun t=>t.1 live)]
        rw [Vval,w0,e1,one_mul,sub_self]
        split <;> simp
      have e0:e i=0:=by rw [e_at,ite_eq_right live]
      rw [e0,zero_mul,sub_zero,Vval]
      change _=Clock.fiber h 0 z i
      unfold Clock.fiber
      by_cases h0:h i=0
      · rw [ite_eq_left h0]
        have w:W i=Q.eval (y i)*b i:=by rw [d,ite_eq_left ⟨live,h0⟩]
        by_cases x0:ξ i=0
        · simp [z,x0]
        rw [ite_eq_right x0,sub_zero,w]
        by_cases q0:Q.eval (y i)=0
        · simp [z,q0]
        have τ0:τ i=0:=by
          by_contra nz
          have d: h i=Q.eval (y i):=(H.headValue i nz).1
          rw [h0] at d
          exact q0 d.symm
        have eq:=congrFun rep i
        simp only [Pi.mul_apply,Pi.add_apply,weightedEval_apply,τ0,mul_zero,add_zero] at eq
        change Q.eval (y i)*b i=Q.eval (y i)/ξ i*u i
        rw [←eq]
        field_simp [x0]
      have w0:W i=0:=by rw [d,ite_eq_right (fun t=>h0 t.2)]
      rw [w0,ite_eq_right h0]
      split <;> simp
    simpa only [Pi.sub_apply,c,Pi.mul_apply] using ig
  have filt:V=W-c:=by rw [←eW];abel
  have off(i:Fin 26)(wi:V i≠0):W i≠0∧ξ i=0:=by
    by_cases p:ξ i=0
    · refine ⟨?_,p⟩
      simpa only [Vval,ite_eq_left p] using wi
    · exact False.elim (wi (by rw [Vval,ite_eq_right p]))
  refine ⟨V,⟨H.degree,H.nonzero,H.preserved,H.headValue,?_,?_⟩,fun i h=>(off i h).2⟩
  · exact fun i wi=>H.contrastValue i (off i wi).1
  · intro R rd
    have c0:(∑i,weightedEval y c R i)=0:=by
      have k:=mem_annih.mp (B.base_annih ho cU) _ (mirror_eval_in_tree (A:=A) R (rd.trans (by decide:11≤16-2)))
      simpa only [row_apply,weightedEval_apply,mul_comm] using k
    have w:=H.moments R rd
    have e:weightedEval y V R=weightedEval y W R-weightedEval y c R:=by
      ext i;rw [filt];simp only [weightedEval_apply,Pi.sub_apply];ring
    rw [e]
    simp only [Pi.sub_apply,Finset.sum_sub_distrib]
    rw [c0,sub_zero,w]
end
end RKCert.Paired.ReverseHull
