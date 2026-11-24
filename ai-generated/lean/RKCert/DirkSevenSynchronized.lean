module
public import RKCert.DirkSevenCleanSpectators
public import RKCert.DirkSevenNativeGate
@[expose] public section
namespace RKCert.Paired.Terminal.PaidReverseBand
open Module Polynomial RKCert.Endpoint RKCert.EndpointPhysical
variable {K:Type*} [Field K] [CharZero K] {s:ℕ} {A:Fin (s+1)→Fin (s+1)→K} {b v:Vec K (s+1)}
noncomputable section
set_option maxRecDepth 3500
/-- A true grade-five synchronized ordinary vector is jointly hidden in a
p17 grade-eight band having at most seven active clean clocks, including
zero. Both otherwise exceptional complex port ratios are now eliminated. -/
theorem synchronous_fifth_seven (D:PaidReverseBand A b 17 8) (ha:LowerArray A) (ho:HasTreeOrderAtLeast A b 17)
    (many:(cleanSites A b).card≤7) (zeroSite:0∈cleanSites A b) (hv:v∈zeroSpace A 5) (hc:diag (nodes A) v∈zeroSpace A 5)
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
  have big:7≤S.card:=by have h:=D.nonlocal_sites ha ho (D.nonlocal_cubic ha ho);change 7≤S.card at h;omega
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
    have tr:ReverseTrace A b 17 5 (Y θ) (X*Q):=by
      rw [rep,←eqn]
      exact (ReverseTrace.scalar A b dR).sub_pure (weights_mul_zeroSpace ho (by omega) hy)
    obtain ⟨i,l,bi,ti,bl,tl,ui,ul,ne,first,second⟩:=D.reduced_ports ha ho (by decide) tr nz ay
    obtain ⟨T,dT,tn,mom⟩:=seven_clean_global ho Q (y i) (y l) many zeroSite (mem_cleanSites i bi ti)
      (mem_cleanSites l bl tl) ui ul ne tr ay
    exact nz (RKCert.SevenPort.quartic_seven_clean Q T low dT tn ui ul ne first second mom)
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
