module
public import RKCert.DirkEightPortField
@[expose] public section
namespace RKCert.Paired.Terminal.PaidReverseBand
open Module Polynomial RKCert.Endpoint RKCert.EndpointPhysical
variable {K:Type*} [Field K] [CharZero K] {s p H:ℕ} {A:Fin (s+1)→Fin (s+1)→K} {b v:Vec K (s+1)}
noncomputable section
set_option maxRecDepth 3500

/-- A reverse trace of X*Q whose extra factor X has already been paid
before grade six. The chronological cut uses two different physical rows
and prices each observation separately. -/
theorem reduced_ports (D:PaidReverseBand A b p H) (ha:LowerArray A) (ho:HasTreeOrderAtLeast A b p)
    (room:8≤H) {θ:Vec K (s+1)} {Q:K[X]}
    (h:ReverseTrace A b p 5 (diag (mirror A) θ) (X*Q)) (nz:Q≠0)
    (active:∀i,θ i≠0 → b i≠0 ∧ tau A b i=0) :
    ∃ i l:Fin (s+1),let u:=mirror A i;let z:=mirror A l
      b i≠0 ∧ tau A b i=0 ∧ b l≠0 ∧ tau A b l=0 ∧ u≠0 ∧ z≠0 ∧ z≠u ∧
      (∀k:Fin 3,(Paired.primitive (X^(k.val+1)*Q)).eval u=0) ∧
      ∀k:Fin 2,(Paired.primitive (X^(k.val+1)*((X-C u)*Q))).eval z=0:=by
  have budget:=D.paid
  let y:=mirror A
  let a:=diag y θ
  have on(i:Fin (s+1)) (hi:a i≠0):y i≠0 ∧ θ i≠0:=mul_ne_zero_iff.mp hi
  have paid(i:Fin (s+1)) (hi:a i≠0):=active i (on i hi).2
  obtain ⟨i,ai,bi,ti,_,first⟩:=D.physical_reverse_pivot ha ho (D.nonlocal_cubic ha ho) (by decide) (by omega) h paid
    (mul_ne_zero X_ne_zero nz)
  let u:=y i
  let z:=diag y a-u • a
  let P:=X*(X*Q)-u • (X*Q)
  have rep:P=(X-C u)*(X*Q):=by simp only [P,Polynomial.smul_eq_C_mul,sub_mul]
  have tr:ReverseTrace A b p 6 z P:=rev_shift h u (by omega)
  have on'(l:Fin (s+1))(hl:z l≠0):y l≠u ∧ a l≠0:=by
    have eqn:z l=(y l-u)*a l:=by simp [z,diag_apply,sub_mul]
    rw [eqn] at hl
    exact ⟨sub_ne_zero.mp (mul_ne_zero_iff.mp hl).1,(mul_ne_zero_iff.mp hl).2⟩
  obtain ⟨l,al,bl,tl,_,next⟩:=D.physical_reverse_pivot ha ho (D.nonlocal_cubic ha ho) (by decide) (by omega) tr
    (fun l al=>paid _ (on' l al).2) (by rw [rep];exact mul_ne_zero (X_sub_C_ne_zero _) (mul_ne_zero X_ne_zero nz))
  refine ⟨i,l,bi,ti,bl,tl,(on i ai).1,(on l (on' l al).2).1,(on' l al).1,?_,?_⟩
  · intro k
    have f:=first k.val (by have:=k.isLt;omega)
    rwa [←mul_assoc,←pow_succ,formalPrimitive_eq_treePrimitive] at f
  · intro k
    have f:=next k.val (by have:=k.isLt;omega)
    have eqn:X^k.val*P=X^(k.val+1)*((X-C u)*Q):=by rw [rep,pow_succ];ring
    rwa [eqn,formalPrimitive_eq_treePrimitive] at f

/-- If v and Cv are both paid in the genuine F5, the two physical reverse
ports see a quartic, not a quintic, and the initial clock costs no extra
grade. No physical invisible row is deleted. -/
theorem synchronous_fifth_hidden (D:PaidReverseBand A b p H) (ha:LowerArray A) (ho:HasTreeOrderAtLeast A b p)
    (field:NoExceptionalRatio K) (room:8≤H) (hv:v∈zeroSpace A 5) (hc:diag (nodes A) v∈zeroSpace A 5)
    (vt:v (Fin.last s)=0) : b*v=0 ∧ tau A b*v=0:=by
  classical
  have hp:=D.paid
  let y:=mirror A
  let Y:=diag y
  have eqv:Y v=v-diag (nodes A) v:=by ext i;change (1-nodes A i)*v i=v i-nodes A i*v i;ring
  have hy:Y v∈zeroSpace A 5:=eqv ▸ (zeroSpace A 5).sub_mem hv hc
  have ty:Y v (Fin.last s)=0:=by change y _*v _=0;rw [vt,mul_zero]
  obtain ⟨Q,dQ,fit,off,_⟩:=D.port_contrast ha ho (by decide) (by omega) hv vt
  obtain ⟨R,dR,fitR,_⟩:=D.port_contrast ha ho (by decide) (by omega) hy ty
  have dd:(R-X*Q).natDegree≤6:=(natDegree_sub_le _ _).trans (max_le (by omega) (natDegree_mul_le.trans (by rw [natDegree_X];omega)))
  let S:=Clock.headSites y (tau A b)
  have big:7≤S.card:=by have h:=D.nonlocal_sites ha ho (D.nonlocal_cubic ha ho);change H-1≤S.card at h;omega
  have eqn:R=X*Q:=by
    apply sub_eq_zero.mp
    apply eq_zero_of_natDegree_lt_card_of_eval_eq_zero (R-X*Q) (Subtype.val_injective (p:=(·∈S)))
    · intro z
      obtain ⟨i,hi,e⟩:=Finset.mem_image.mp z.property
      have dirty:tau A b i≠0:=(Finset.mem_filter.mp hi).2
      rw [←e,eval_sub,eval_mul,eval_X,←fit i dirty,←fitR i dirty]
      exact sub_self _
    · simpa using (by omega:(R-X*Q).natDegree<S.card)
  have zero:Q=0:=by
    by_contra nz
    have low:Q.natDegree≤4:=by rw [eqn,natDegree_mul X_ne_zero nz,natDegree_X] at dR;omega
    let θ:=weightedEval y b Q-b*v
    have ay(i:Fin (s+1))(hi:θ i≠0):b i≠0 ∧ tau A b i=0:=by
      refine ⟨fun z=>hi (by simp [θ,z]),?_⟩
      by_contra dirty
      apply hi;simp [θ,fit i dirty,mul_comm,y]
    have rep:Y θ=weightedEval y b (X*Q)-b*(Y v):=by
      ext i;simp [Y,θ,diag_apply];ring
    have tr:ReverseTrace A b p 5 (Y θ) (X*Q):=by
      rw [rep,←eqn]
      exact (ReverseTrace.scalar A b dR).sub_pure (weights_mul_zeroSpace ho (by omega) hy)
    obtain ⟨i,l,_,_,_,_,ui,ul,ne,first,second⟩:=D.reduced_ports ha ho room tr nz ay
    exact field _ ((quartic_physical_alternative Q low ui ul ne first second).resolve_left nz)
  have hit(i:Fin (s+1)) (t:tau A b i≠0):v i=0:=by simpa [zero] using fit i t
  constructor <;> ext i
  · by_cases t:tau A b i=0
    · exact off i t
    · simp [hit i t]
  · by_cases t:tau A b i=0
    · simp [t]
    · simp [hit i t]
end
end RKCert.Paired.Terminal.PaidReverseBand
