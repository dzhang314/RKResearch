module
public import RKCert.ERKThinReversePorts
public import RKCert.ERKEvenThinTrace

@[expose] public section

/-! # Two actual paid reverse ports force low-grade invisibility

The degree budgets belong to the two recovered polynomial representatives,
not to the original forward grade. This permits a paid same-grade clock
shift to refund a degree before applying the chronology. -/
namespace RKCert.Paired.ReverseHull
open RKCert.Endpoint Polynomial
open scoped Classical
noncomputable section
variable {K:Type*} [Field K] [LinearOrder K] [IsStrictOrderedRing K]
variable {s p m:ℕ} {A:Fin s→Fin s→K} {b f:Vec K s}

/-- If the nonzero contrast polynomial were supported at only one active
clock, the genuine two moments would make a positive x-weighted square
zero. The clock can be exterior and the original weights signed. -/
theorem reverse_contrast_many (ho:HasTreeOrderAtLeast A b p) (Q P:K[X]) (qn:Q≠0)
    (qpay:2*Q.natDegree+4≤p) (ppay:Q.natDegree+P.natDegree+5≤p) :
    ∀ a:K,∃i,reverseContrast A b Q P i≠0 ∧ mirror A i≠a := by
  intro a
  by_contra! onlySite
  let y:=mirror A
  let W:=reverseContrast A b Q P
  let R:K[X]:=(X-C a)^2*Q
  let S:K[X]:=R*(X*Q)
  let T:K[X]:=R*P
  have dR:R.natDegree≤2+Q.natDegree:=by
    have h:=natDegree_mul_le (p:=(X-C a)^2) (q:=Q)
    rw [natDegree_pow,natDegree_X_sub_C,mul_one] at h
    exact h
  have dS:S.natDegree+1≤p:=by
    have h:=natDegree_mul_le (p:=R) (q:=X*Q)
    have q:=natDegree_mul_le (p:=X) (q:=Q)
    rw [natDegree_X] at q
    dsimp only [S]
    omega
  have dT:T.natDegree+3≤p:=by
    have h:=natDegree_mul_le (p:=R) (q:=P)
    dsimp only [T]
    omega
  have a0:(∑i,weightedEval y W R i)=0:=by
    apply Finset.sum_eq_zero
    intro i _
    by_cases w:W i=0
    · simp [w]
    · have zi:y i=a:=onlySite i w
      simp [R,zi]
  have eq:=congrArg (fun v:Vec K s=>∑i,v i) (reverseContrast_weighted (A:=A) (b:=b) Q P R)
  change (∑ i,weightedEval y W R i)=(∑i,(weightedEval y b S-weightedEval y (backSeed2 A b) T) i) at eq
  simp only [Pi.sub_apply,Finset.sum_sub_distrib] at eq
  rw [a0,reflected_scalar_budget ho S dS,seed_eval_mass ho T dT,sub_zero] at eq
  have h:S=X*(Q*(X-C a))^2:=by dsimp [S,R];ring
  have pos:=RKCert.OrderedGram.pow_square_pos 1 (Q*(X-C a)) (mul_ne_zero qn (X_sub_C_ne_zero a))
  rw [pow_one,←h,←formalPrimitive_eq_treePrimitive] at pos
  exact pos.ne' eq.symm

/-- The pure scalar representative of a true thin contrast must vanish
once the two signed physical port budgets are available. No positivity is
required of RK coefficients, nor do we order the abscissae chronologically. -/
theorem ordered_thin_reverse_profile_zero (ha:StrictLower A) (ho:HasTreeOrderAtLeast A b p)
    {t:Fin s} (y0:mirror A t=0) (col:∀k,A k t=0) (cover:SupportsComplement A b m t)
    (Q P:K[X]) (deg:Q.natDegree≤4)
    (qm:2*Q.natDegree+4≤p) (pm:Q.natDegree+P.natDegree+5≤p)
    (qport:m+Q.natDegree+5≤p) (pport:m+P.natDegree+6≤p)
    (qfit:∀i,backSeed2 A b i*f i=Q.eval (mirror A i)*backSeed2 A b i)
    (pfit:∀i,mirror A i*b i*f i=P.eval (mirror A i)*backSeed2 A b i) :
    Q=0 := by
  by_contra qn
  have out (i:Fin s)(wi:reverseContrast A b Q P i≠0):backSeed2 A b i=0:=by
    by_contra dn
    have q:=qfit i
    rw [mul_comm (Q.eval (mirror A i))] at q
    have hf:=mul_left_cancel₀ dn q
    have e:=pfit i
    rw [hf] at e
    apply wi
    simp only [reverseContrast,Pi.sub_apply,weightedEval_apply,eval_mul,eval_X]
    linear_combination e
  obtain ⟨u,v,R⟩:=actual_reverse_three_two ha ho y0 col cover Q P qport pport out
    (reverse_contrast_many ho Q P qn qm pm)
  exact qn (ordered_quartic_physical Q deg R.u_ne R.v_ne R.different R.left R.right)

/-- On the actual quadratic and weighted support, the forward defect
vanishes pointwise. Use this form with reps of any genuinely paid forward
grade, including reps after a same-grade clock refund. -/
theorem ordered_thin_invisible_given_reps (ha:StrictLower A) (ho:HasTreeOrderAtLeast A b p)
    {t:Fin s} (y0:mirror A t=0) (col:∀k,A k t=0) (cover:SupportsComplement A b m t)
    (Q P:K[X]) (deg:Q.natDegree≤4)
    (qm:2*Q.natDegree+4≤p) (pm:Q.natDegree+P.natDegree+5≤p)
    (qport:m+Q.natDegree+5≤p) (pport:m+P.natDegree+6≤p)
    (qfit:∀i,backSeed2 A b i*f i=Q.eval (mirror A i)*backSeed2 A b i)
    (pfit:∀i,mirror A i*b i*f i=P.eval (mirror A i)*backSeed2 A b i) :
    ∀i,backSeed2 A b i*f i=0 ∧ mirror A i*b i*f i=0 := by
  have vanish:=ordered_thin_reverse_profile_zero ha ho y0 col cover Q P deg qm pm qport pport qfit pfit
  intro i
  have q:=qfit i
  rw [vanish,eval_zero,zero_mul] at q
  refine ⟨q,?_⟩
  by_cases d:backSeed2 A b i=0
  · simpa only [d,mul_zero] using pfit i
  · rw [(mul_eq_zero.mp q).resolve_left d,mul_zero]

/-- Natural combined statement for the entire low-grade forward defect
space under a genuinely paid terminal-zero thin reverse horizon. -/
theorem ordered_thin_invisible (ha:StrictLower A) (ho:HasTreeOrderAtLeast A b p)
    {j h:ℕ} (hf:f∈zeroSpace A j) (one:1≤j) (jh:j≤h) (four:j≤4)
    (pay:m+h+3≤p) (ports:m+j+5≤p) (mass:2*j+4≤p)
    (t:Fin s) (y0:mirror A t=0) (col:∀k,A k t=0) (d0:backSeed2 A b t=0)
    (big:h+1<(Clock.headSites (mirror A) (backSeed2 A b)).card)
    (cover:∀v∈annih (treeSpace A m)⊓LinearMap.ker (LinearMap.proj t),
      ∃P:K[X],P.natDegree≤h ∧ weightedEval (mirror A) (backSeed2 A b) P=v) :
    ∀i,backSeed2 A b i*f i=0 ∧ mirror A i*b i*f i=0 := by
  obtain ⟨Q,P,dQ,dP,qfit,pfit⟩:=thin_reverse_two_traces ho hf one jh pay t y0 d0 big cover
  have off:SupportsComplement A b m t:=by
    intro v hv i hi
    obtain ⟨T,_,e⟩:=cover v hv
    rw [←e,weightedEval_apply,hi,mul_zero]
  exact ordered_thin_invisible_given_reps ha ho y0 col off Q P (by omega)
    (by omega) (by omega) (by omega) (by omega) qfit pfit

end
end RKCert.Paired.ReverseHull
