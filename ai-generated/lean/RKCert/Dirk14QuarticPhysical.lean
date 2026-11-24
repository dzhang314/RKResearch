module
public import RKCert.DirkEvenPhysicalCount
@[expose] public section
namespace RKCert.Paired
open RKCert.Endpoint Polynomial
open scoped Classical
variable {K:Type*} [Field K] [CharZero K] {s p n:ℕ} {A:Fin s→Fin s→K} {b w:Vec K s} {Q:K[X]}
noncomputable section

/-- Paid polynomial spectators on a true marked row with polynomial trace. -/
theorem ReverseTrace.pair_polynomial (h:ReverseTrace A b p n w Q) (ho:HasTreeOrderAtLeast A b p)
    (P:K[X]) (hp:n+P.natDegree+1≤p) :
    row (weightedEval (mirror A) w P) 1=(formalPrimitive (P*Q)).eval 1 := by
  let L:=pairEval (mirror A) w (1:Vec K s)
  let M : K[X] →ₗ[K] K :=(leval (1:K)).comp (formalPrimitiveLinear.comp (LinearMap.mulLeft K Q))
  rw [mul_comm P Q]
  change L P=M P
  conv_lhs => rw [P.as_sum_range]
  conv_rhs => rw [P.as_sum_range]
  rw [map_sum,map_sum]
  apply Finset.sum_congr rfl
  intro j hj
  have bound:=Finset.mem_range.mp hj
  rw [show monomial j (P.coeff j)=P.coeff j • (X^j:K[X]) by rw [smul_eq_C_mul,C_mul_X_pow_eq_monomial],map_smul,map_smul]
  congr 1
  change row (weightedEval (mirror A) w (X^j)) 1=(formalPrimitive (Q*X^j)).eval 1
  rw [mul_comm Q,(h.weighted_moment ho j (by omega)).symm]
  simp only [row_apply,weightedEval_apply,eval_pow,eval_X,Pi.one_apply,one_mul,mul_comm]

namespace Terminal
omit [CharZero K] in
theorem nodal_dvd_vanishing (S:Finset K) (P:K[X]) (roots:∀a∈S,P.eval a=0) :
    Lagrange.nodal S id ∣ P := by
  classical
  induction S using Finset.induction_on generalizing P with
  | empty=>simp [Lagrange.nodal]
  | @insert a S ha ih=>
    obtain ⟨H,ph⟩:=dvd_iff_isRoot.mpr (roots a (Finset.mem_insert_self a S))
    have hd:=ih H (fun z hz=>by
      have he:=roots _ (Finset.mem_insert_of_mem hz)
      rw [ph,eval_mul,eval_sub,eval_X,eval_C] at he
      exact (mul_eq_zero.mp he).resolve_left (sub_ne_zero.mpr (fun e=>ha (e ▸ hz))))
    rw [Lagrange.nodal_insert_eq_nodal ha,ph]
    exact mul_dvd_mul_left _ hd

omit [CharZero K] in
/-- Reflection of the true closed p14 grid via Mathlib Legendre parity. -/
theorem closed_lobatto7_reflect (x:K) :
    ((X-1)*lobatto 7).eval (1-x)=((X-1)*lobatto 7).eval x := by
  have parity:=Polynomial.neg_one_pow_mul_shiftedLegendre_comp_one_sub_X_eq 7
  norm_num at parity
  have deriv:=congrArg Polynomial.derivative parity
  simp only [derivative_neg,derivative_comp,derivative_sub,derivative_one,derivative_X,zero_sub] at deriv
  let R:=((shiftedLegendre 7).derivative.map (Int.castRingHom K))
  have ref:R.eval (1-x)=R.eval x := by
    have eqn:=congrArg (fun H:ℤ[X] => (H.map (Int.castRingHom K)).eval x) deriv
    simpa [Polynomial.map_comp,R] using eqn
  simp only [lobatto,eval_mul,eval_sub,eval_X,eval_one,eval_C]
  change (1-x-1)*((-1)^7*((1-x)*R.eval (1-x)))=(x-1)*((-1)^7*(x*R.eval x))
  rw [ref];ring

variable {T:Fin 18→Fin 18→K} {β f:Vec K 18}

/-- All seven scalar equations are derived from physically counted clean
sites and a refunded pivot on the original array; no sign or ordering. -/
theorem order14_quartic_reduction (ha:LowerArray T) (ho:HasTreeOrderAtLeast T β 14) (hf:f∈zeroSpace T 4) :
    (β*f=0 ∧ tau T β*f=0) ∨ ∃Z Q:K[X],∃u:K,
      Z.Monic ∧ Z.natDegree≤5 ∧ Z ∣ (X-1)*lobatto 7 ∧ u≠0 ∧ Z.eval u=0 ∧ Q.natDegree≤4 ∧ Q≠0 ∧
      (∀k:Fin 5,(Paired.primitive ((X^k.val*Z)*Q)).eval 1=0) ∧
      (Paired.primitive (X*Q)).eval u=0 ∧ (Paired.primitive (X^2*Q)).eval u=0 := by
  classical
  have non:=even_reverse_nonlocal (s:=17) (m:=7) (by decide) ha ho (by decide)
  let y:=mirror T
  let I:=Finset.univ.filter fun i:Fin 18=>β i≠0 ∧ tau T β i=0
  let S:=I.image y
  let Z:=Lagrange.nodal S id
  have card:S.card≤5:=Finset.card_image_le.trans (clean_active_budget (s:=17) (m:=7) (by decide) ha ho (by decide))
  have zd:Z.natDegree≤5 := by rw [show Z.natDegree=S.card from Lagrange.natDegree_nodal];exact card
  have cl (i:Fin 18) (bi:β i≠0) (ti:tau T β i=0) : Z.eval (y i)=0 :=
    Lagrange.eval_nodal_at_node (v:=id) (Finset.mem_image_of_mem y (Finset.mem_filter.mpr ⟨Finset.mem_univ _,bi,ti⟩))
  have divi:Z ∣ (X-1)*lobatto 7:=by
    apply nodal_dvd_vanishing
    obtain ⟨t,nt,_,_,_,root⟩:=fixed_even_boundary (s:=17) (m:=7) (Or.inl rfl) ha ho (by decide)
    intro a h
    obtain ⟨i,hi,rfl⟩:=Finset.mem_image.mp h
    obtain ⟨bi,ti⟩:=(Finset.mem_filter.mp hi).2
    by_cases e:i=t
    · simp [y,mirror,e,nt,lobatto]
    change ((X-1)*lobatto 7).eval (1-nodes T i)=0
    rw [closed_lobatto7_reflect,eval_mul,root i e (fun h hh=>weighted_clean (by decide:7≤7) ha ho (by decide)
      non i bi ti h (zeroSpace_mono T (by decide:6≤7) hh)),mul_zero]
  obtain ⟨Q,hd,fit,off,θ,hθ,active⟩:=port_contrast (by decide:7≤7) ha ho (by decide) non (by decide) (by decide) hf
  by_cases hQ:Q=0
  · left
    have on (i) (hi:tau T β i≠0):f i=0:=by simpa [hQ] using fit i hi
    constructor <;> ext i
    · by_cases h:tau T β i=0
      · exact off i h
      · simp [on i h]
    · by_cases h:tau T β i=0
      · simp [h]
      · simp [on i h]
  right
  have hai (i:Fin 18) (h:diag y θ i≠0) : β i≠0 ∧ tau T β i=0 :=
    active i (fun z=>h (by rw [diag_apply,z,mul_zero]))
  obtain ⟨i,vi,bi,ti,_,alltests⟩:=physical_reverse_pivot (by decide:7≤7) ha ho (by decide) non
    (by decide) (by decide) (hθ.clock (by decide)) hai (mul_ne_zero X_ne_zero hQ)
  have yn:y i≠0:=fun z=> vi (by change y i*θ i=0;rw [z,zero_mul])
  refine ⟨Z,Q,y i,Lagrange.nodal_monic,zd,divi,yn,cl i bi ti,hd,hQ,?_,?_,?_⟩
  · intro k
    have deg:(X^k.val*Z).natDegree≤9 := natDegree_mul_le.trans (by rw [natDegree_X_pow];omega)
    have eqn:=hθ.pair_polynomial ho (X^k.val*Z) (by omega)
    have zz:weightedEval y θ (X^k.val*Z)=0 := by
      ext l
      by_cases h:θ l=0
      · simp [h]
      · have ac:=active l h
        simp [cl l ac.1 ac.2]
    rw [←formalPrimitive_eq_treePrimitive,←eqn,show weightedEval (mirror T) θ (X^k.val*Z)=0 from zz]
    simp
  · simpa only [formalPrimitive_eq_treePrimitive,pow_zero,one_mul] using alltests 0 (by decide)
  · have eqn:=alltests 1 (by decide)
    rw [show X^1*(X*Q)=X^2*Q by ring,formalPrimitive_eq_treePrimitive] at eqn
    exact eqn
end Terminal
end
end RKCert.Paired
