module
public import RKCert.DirkMidpointFactor
@[expose] public section
namespace RKCert.Paired.Terminal.MidpointHead
open Polynomial Module RKCert.OneEscape RKCert.Endpoint
variable {K:Type*} [Field K] [CharZero K] {s:ℕ}
variable {A:Fin (s+1)→Fin (s+1)→K} {b w:Vec K (s+1)} {U:Submodule K (Vec K (s+1))}
noncomputable section

/-- In the singleton case at order sixteen the cardinal, rather than a
second grade-five head, supplies the missing scalar equation. Its actual
cubic factor is nonzero, so it kills the degree-eight pure trace. -/
theorem no_single_head16 (h:MidpointHead A 8 U w 1)
    (ha:LowerArray A) (ho:HasTreeOrderAtLeast A b 16) (he:s+1+3=3*8)
    (cut:∀i,Clock.Live U i → w i=0) (mul:Clock.MulClosed U) :False:=by
  classical
  let c:=nodes A
  let O:=chain (diag c) U w
  have hs:=h.physical_head_site_bound (Or.inr (Or.inl rfl)) ha ho he (q:=13) (by decide) (by decide)
  have w5:=h.head_paid (by decide)
  obtain ⟨β,Q,bn,dQ,card⟩:=h.head_cardinal (Or.inr rfl) ha ho he cut
  have qnz:Q≠0:=by
    intro q0
    have zg:lobatto (K:=K) 8=0:=by
      apply vanish_on_head (w:=w) (A:=A) (by have:=lobatto_degree (K:=K) (m:=8) (by decide);omega)
      intro i wi
      have zero:=card i wi
      rw [q0,eval_zero,zero_mul,add_zero] at zero
      exact (mul_eq_zero.mp zero).resolve_left bn
    have dd:=closed_lobatto_degree (K:=K) (m:=8) (by decide)
    rw [zg,mul_zero,natDegree_zero] at dd
    omega
  obtain ⟨H,x,hx,tail,rep⟩:=h.pure_decompose (Or.inr rfl) ha ho he (q:=10) (by decide) (by decide)
    (zeroSpace_mul (A:=A) (m:=5) (n:=5) w5 w5) (fun i cl=>by rw [Pi.mul_apply,cl w w5,zero_mul])
  have w0:w∈O 1 := by rw [show O 1=zeroSpace A 5 from (h.band 5 le_rfl (by decide)).symm];exact w5
  have pw:weightedEval c w (lobatto 8)∈O 9:=by
    apply chain_length_le (by have:=lobatto_degree (K:=K) (m:=8) (by decide);omega:1+(lobatto (K:=K) 8).natDegree≤9)
    exact orbit_mul_polynomial h.invariant (by decide) w0 _
  have px:weightedEval c x Q∈O 9:=by
    apply chain_length_le (by omega:1+(10-5)+Q.natDegree≤9)
    exact orbit_mul_polynomial h.invariant (by decide) hx _
  have num:evalNodes A (Q*H)=(-β) • weightedEval c w (lobatto 8)-weightedEval c x Q:=by
    ext i
    have z:Q.eval (c i)*(w i*w i)= -(β*(lobatto 8).eval (c i)*w i):=by
      by_cases wi:w i=0
      · simp [wi]
      · have cc:=card i wi
        change β*(lobatto 8).eval (c i)+Q.eval (c i)*w i=0 at cc
        linear_combination (w i)*cc
    have e:=congrFun rep i
    change w i*w i=H.eval (c i)+x i at e
    rw [e] at z
    simp only [evalNodes_apply,eval_mul,Pi.sub_apply,Pi.smul_apply,smul_eq_mul,weightedEval_apply]
    change Q.eval (c i)*H.eval (c i)= -β*((lobatto 8).eval (c i)*w i)- Q.eval (c i)*x i
    linear_combination z
  have dvd:(X-1)*lobatto 8 ∣ Q*H:=by
    apply h.grid_dvd_of_pure_polynomial (Or.inr (Or.inl rfl)) ha ho he (q:=13) (by decide) (by decide)
    · exact natDegree_mul_le.trans (by have:=tail.degree;omega)
    · rw [num];exact (O 9).sub_mem ((O 9).smul_mem _ pw) px
  have zH:=lobatto8_tail_short_factor tail qnz (by omega) dvd
  have sq:w*w∈O 6:=by rw [rep,zH,show evalNodes A (0:K[X])=0 from by ext i;simp,zero_add];exact hx
  have band (k:ℕ) (hk:k≤0):(diag c^k) (w*w)∈chain (diag c) U w 6 := by
    obtain rfl : k=0:=by omega
    simpa only [pow_zero,Module.End.one_eq_id,LinearMap.id_apply] using sq
  obtain ⟨P,dp,val⟩:=Clock.multiplier_degree (a:=w) (c:=c) cut (by dsimp [c];omega:6<(Clock.headSites c w).card) band
  have deg:P.natDegree≤5:=by
    rcases dp with z|z
    · simp [z]
    · omega
  have fact:=h.nodal_factor (Or.inr rfl) ha ho he cut val (by omega) (by omega)
  exact h.factor_kills (Or.inr rfl) ha ho he cut mul fact val (Or.inl ⟨rfl,deg⟩)

end
end RKCert.Paired.Terminal.MidpointHead

