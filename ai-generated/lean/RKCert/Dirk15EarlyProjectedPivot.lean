module
public import RKCert.Dirk15EarlyScalars
public import RKCert.Dirk15EarlyQuartic
public import RKCert.DirkJointClockRetraction
@[expose] public section
namespace RKCert.Paired.EarlyFifteen
open Polynomial Module RKCert.OneEscape RKCert.Endpoint RKCert.Paired.Signature
open PivotProjection
open scoped Classical
noncomputable section
variable {K:Type*} [Field K] [CharZero K]
variable {A:Fin 20→Fin 20→K} {b:Vec K 20} {U:Submodule K (Vec K 20)}
variable {P:ClockRetraction (nodes A) U} {i:Fin 20} {z:Vec K 20}

omit [CharZero K] in
theorem projected_eval (P:ClockRetraction (nodes A) U) (H:K[X]) (i:Fin 20) :
    P.projection (evalNodes A H) i=H.eval (nodes A i)*(P.projection 1) i:=by
  have e:evalNodes A H=weightedEval (nodes A) (1:Vec K 20) H:=by ext j;simp
  rw [e,P.weighted,weightedEval_apply]

omit [CharZero K] in
theorem projected_clean {w:Vec K 20} {r:ℕ} (h:Heads A U w r)
    (off:P.projection w i=0) (f:Vec K 20) (hf:f∈zeroSpace A 8) : P.projection f i=0:=by
  rw [show zeroSpace A 8=chain (diag (nodes A)) U w (r+2) from h.band 2 (by decide)] at hf
  obtain ⟨u,hu,Q,_,he⟩:=Clock.exists_head_poly hf
  have eq:f=u+weightedEval (nodes A) w Q:=by ext j;simpa only [Pi.add_apply,weightedEval_apply] using he j
  rw [eq,map_add,P.kills _ hu,zero_add,P.weighted,weightedEval_apply,off,mul_zero]

private theorem projected_nonzero {n:ℕ} (inc:U≤zeroSpace A 6)
    (ho:HasTreeOrderAtLeast A b 15) (nn:n≤6) {H:K[X]} (hn:H≠0) (dH:H.natDegree≤5)
    (tr:OrdinaryTrace A n z (X*H)) : P.projection z≠0:=by
  intro eq
  have hf:=inc (P.defect z)
  rw [eq,sub_zero] at hf
  have tt:=((tr.mono nn).sub_pure hf)
  rw [sub_self] at tt
  have th:OrdinaryTrace A 6 (0:Vec K 20) (X^1*H):=by simpa only [pow_one] using tt
  exact hn (th.zero_numeric dH ho (by decide : 5+6+1≤15))

theorem projected_primitive_at_first (ha:LowerArray A) (ho:HasTreeOrderAtLeast A b 15)
    (inc:U≤zeroSpace A 6) {n:ℕ} {H:K[X]} (tr:OrdinaryTrace A n z H)
    (pay:n+2≤8) (active:P.projection z i≠0)
    (pref:∀ j < i,P.projection z j=0) (unit:(P.projection 1) i≠0)
    (clean:∀ f∈zeroSpace A 8,P.projection f i=0) (k:ℕ) (pk:n+k+1≤8) :
    (formalPrimitive (X^k*H)).eval (nodes A i)=0:=by
  let C:=diag (nodes A)
  let N:=mat A
  let L:=P.contractedOp N
  let delta:=P.diagonal*((fun j=>A j j)*P.diagonal)
  have lc:CausalDiag (Equiv.refl (Fin 20)) L delta:=P.contractedOp_causal (causalDiag_mat ha)
  have apply0(j:Fin 20)(x:Vec K 20)(h:∀ l < j,x l=0):L x j=delta j*x j:=lc j x h
  have left:=apply0 i (P.projection z) pref
  have fore:∀ j < i,L (P.projection z) j=0:=by
    intro j hj
    rw [apply0 j _ (fun l hl=>pref l (hl.trans hj)),pref j hj,mul_zero]
  have sum:commutatorR L C (P.projection z) i=-(delta i)^2*P.projection z i:=by
    have con:=apply0 i (C (P.projection z)) (fun j hj=>by simp [C,pref j hj])
    have two:=apply0 i (L (P.projection z)) fore
    change C (L (P.projection z)) i-L (C (P.projection z)) i-L (L (P.projection z)) i=_
    rw [con,two,diag_apply,diag_apply,left]
    ring
  have kills {f:Vec K 20} (hf:f∈U) : P.projection (N f) i=0:=
    clean _ (zeroSpace_mono A (by decide:7≤8) (mat_zeroSpace_charZero A 6 (inc hf)))
  have killsC {f:Vec K 20} (hf:f∈U) : P.projection (C (N f)) i=0:=
    clean _ (diag_zeroSpace A 7 (mat_zeroSpace_charZero A 6 (inc hf)))
  have killsN {f:Vec K 20} (hf:f∈U) : P.projection (N (N f)) i=0:=
    clean _ (mat_zeroSpace_charZero A 7 (mat_zeroSpace_charZero A 6 (inc hf)))
  have old:P.projection (commutatorR N C z) i=0:=
    clean _ (zeroSpace_mono A pay (commutator_mem_zeroSpace ho n (by omega) tr.stage))
  have e:=congrFun (P.contractedOp_commutator_error N z) i
  change (commutatorR L C (P.projection z)-P.projection (commutatorR N C z)) i=_ at e
  have eNC:P.projection (N (diag (nodes A) z-P.projection (diag (nodes A) z))) i=0:=
    kills (P.defect (diag (nodes A) z))
  have eCN:P.projection (diag (nodes A) (N (z-P.projection z))) i=0:=
    killsC (P.defect z)
  have out:commutatorR L C (P.projection z) i=0:=by
    simpa only [Pi.add_apply,Pi.sub_apply,old,sub_zero,zero_sub,zero_add,neg_zero,
      eNC,eCN,killsN (P.defect z),kills (P.defect (N (P.projection z)))] using e
  rw [sum] at out
  have dz:delta i=0:=sq_eq_zero_iff.mp (neg_eq_zero.mp ((mul_eq_zero.mp out).resolve_right active))
  let x:=(C^k) z
  have prex:∀ j < i,P.projection x j=0:=by
    intro j hj
    change P.projection ((diag (nodes A)^k) z) j=0
    rw [P.clock_pow,Clock.pow_diag_apply,pref j hj,mul_zero]
  have n0:L (P.projection x) i=0:=by rw [apply0 i _ prex,dz,zero_mul]
  have n1:=congrFun (P.contractedOp_on_projection N x) i
  change L (P.projection x) i=(P.projection (N x)-P.projection (N (x-P.projection x))) i at n1
  have projectedN:P.projection (N x) i=0:=by
    simpa only [n0,Pi.sub_apply,kills (P.defect x),sub_zero] using n1.symm
  have tt:OrdinaryTrace A (n+k) x (X^k*H):=tr.clock_pow k
  have fzero:=clean _ (zeroSpace_mono A pk tt.primitive.pure)
  have eval0:P.projection (evalNodes A (formalPrimitive (X^k*H))) i=0:=by
    rw [map_sub,Pi.sub_apply,projectedN,zero_sub,neg_eq_zero] at fzero
    exact fzero
  rw [projected_eval] at eval0
  exact (mul_eq_zero.mp eval0).resolve_right unit

/-- A native grade-five masked quartic, if its retracted support is clean at
grade eight and the original projected constant is nonzero at each pivot,
has zero scalar profile. The 3+2 primitive tests are genuine original-array
tests. The clock retraction never posits order on a shortened tableau. -/
theorem projected_quartic_zero (ha:LowerArray A) (ho:HasTreeOrderAtLeast A b 15)
    (inc:U≤zeroSpace A 6) (rel:evalNodes A (relation K)∈zeroSpace A 8)
    (Q:K[X]) (dQ:Q.natDegree≤4) (tr:OrdinaryTrace A 5 z (X*Q))
    (clean:∀ i,P.projection z i≠0→(P.projection 1) i≠0 ∧ nodes A i≠0 ∧
      ∀ f∈zeroSpace A 8,P.projection f i=0) : Q=0:=by
  by_contra qn
  obtain ⟨i,inz,ipre⟩:=exists_first_coordinate (projected_nonzero (P:=P) inc ho (by decide)
    qn (dQ.trans (by decide)) tr)
  obtain ⟨bi,ui,ci⟩:=clean i inz
  let u:=nodes A i
  have root (j:Fin 20) (h:P.projection z j≠0) : (radauLeft7:K[X]).eval (nodes A j)=0:=by
    obtain ⟨bb,nn,cc⟩:=clean j h
    have fzero:=cc _ rel
    rw [projected_eval,relation,eval_mul,eval_X] at fzero
    exact (mul_eq_zero.mp ((mul_eq_zero.mp fzero).resolve_right bb)).resolve_left nn
  let x:=diag (nodes A) z-u • z
  let Q' := (X-C u)*Q
  have qd:Q'.natDegree≤5:=natDegree_mul_le.trans (by rw [natDegree_X_sub_C];omega)
  have qn':Q'≠0:=mul_ne_zero (monic_X_sub_C u).ne_zero qn
  have tx:OrdinaryTrace A 6 x (X*Q'):=by
    have er:=tr.clock.sub ((tr.mono (by decide:5≤6)).smul u)
    change OrdinaryTrace A 6 x (X*(X*Q)-C u*(X*Q)) at er
    rwa [show X*(X*Q)-C u*(X*Q)=X*Q' by dsimp [Q'];ring] at er
  obtain ⟨j,jnz,jpre⟩:=exists_first_coordinate (projected_nonzero (P:=P) inc ho (by decide) qn' qd tx)
  have fact:P.projection x j=(nodes A j-u)*P.projection z j:=by
    simp only [x,map_sub,P.clock,map_smul,Pi.sub_apply,Pi.smul_apply,smul_eq_mul,diag_apply]
    ring
  have jact:P.projection z j≠0:=(mul_ne_zero_iff.mp (fact ▸ jnz)).2
  have ne:nodes A j≠u:=sub_ne_zero.mp (mul_ne_zero_iff.mp (fact ▸ jnz)).1
  obtain ⟨bj,vj,cj⟩:=clean j jact
  have t₁:=projected_primitive_at_first ha ho inc tr (by decide) inz ipre bi ci 0 (by decide)
  have t₂:=projected_primitive_at_first ha ho inc tr (by decide) inz ipre bi ci 1 (by decide)
  have t₃:=projected_primitive_at_first ha ho inc tr (by decide) inz ipre bi ci 2 (by decide)
  have s₁:=projected_primitive_at_first ha ho inc tx (by decide) jnz jpre bj cj 0 (by decide)
  have s₂:=projected_primitive_at_first ha ho inc tx (by decide) jnz jpre bj cj 1 (by decide)
  apply quartic_three_two_impossible Q qn dQ ui vj ne (root i inz) (root j jact)
  · simpa only [paidMoment,pow_one,pow_zero,one_mul,u] using t₁
  · simpa only [paidMoment,pow_two,pow_one,mul_assoc,u] using t₂
  · simpa only [paidMoment,show (X:K[X])^3=X^2*X by rw [pow_succ],mul_assoc,u] using t₃
  · simpa only [paidMoment,pow_one,pow_zero,one_mul,Q'] using s₁
  · simpa only [paidMoment,pow_two,pow_one,mul_assoc,Q'] using s₂
end
end RKCert.Paired.EarlyFifteen
