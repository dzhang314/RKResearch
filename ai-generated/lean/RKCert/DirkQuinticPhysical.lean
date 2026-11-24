module
public import RKCert.Dirk14QuarticPhysical
public import RKCert.DirkEvenFifthFloor
@[expose] public section
namespace RKCert.Paired.Terminal
open RKCert.Endpoint Polynomial
open scoped Classical
variable {K:Type*} [Field K] [CharZero K] {s m:ℕ}
variable {A:Fin (s+1)→Fin (s+1)→K} {b:Vec K (s+1)}
noncomputable section

omit [CharZero K] in
/-- The full fixed Lobatto grid includes both endpoints and is stable
under reflection for every degree. Only fixed integer polynomial parity. -/
theorem lobatto_grid_reflect_zero (m:ℕ) (x:K) (hz:((X-1)*lobatto m).eval x=0) :
    ((X-1)*lobatto m).eval (1-x)=0 := by
  let R:=((shiftedLegendre m).derivative.map (Int.castRingHom K))
  have parity:=Polynomial.neg_one_pow_mul_shiftedLegendre_comp_one_sub_X_eq m
  have hp:(-1)^m*(shiftedLegendre m).comp (1-X)=shiftedLegendre m:=parity
  have hd:=congrArg Polynomial.derivative hp
  have scalar : (-1:ℤ[X])^m=C ((-1:ℤ)^m) := by simp
  rw [scalar,derivative_C_mul,derivative_comp_one_sub_X] at hd
  have vals:=congrArg (fun H:ℤ[X] => (H.map (Int.castRingHom K)).eval x) hd
  have eqn:(-1:K)^m*(-R.eval (1-x))=R.eval x:=by simpa [R,Polynomial.map_comp] using vals
  change ((X-1)*(C ((-1:K)^m)*(X*R))).eval x=0 at hz
  simp only [lobatto,eval_mul,eval_sub,eval_X,eval_one,eval_C] at hz ⊢
  change (1-x-1)*((-1)^m*((1-x)*R.eval (1-x)))=0
  apply (mul_left_cancel₀ (pow_ne_zero m (neg_ne_zero.mpr one_ne_zero: (-1:K)≠0)))
  rw [mul_zero]
  rw [←eqn] at hz
  linear_combination -hz

theorem fifth_grid_reduction (hm:m=9 ∨ m=10) (ha:LowerArray A) (ho:HasTreeOrderAtLeast A b (2*m))
    (he:s+1+3=3*m) :
    ∃Z Q:K[X],∃u:K, Z.Monic ∧ Z.natDegree≤m-2 ∧ Z ∣ (X-1)*lobatto m ∧
      u≠0 ∧ Z.eval u=0 ∧ Q.natDegree≤5 ∧ Q≠0 ∧
      (∀W:K[X],5+(W*Z).natDegree+1≤2*m → (Paired.primitive ((W*Z)*Q)).eval 1=0) ∧
      ∀k:Fin 3,(Paired.primitive (X^(1+k.val)*Q)).eval u=0 := by
  classical
  have hh:9≤m:=by rcases hm with rfl|rfl <;>omega
  have n:=fifth_not_hidden (by omega) ha ho he
  push Not at n
  obtain ⟨f,hf,hnot⟩:=n
  have non:=even_reverse_nonlocal (by omega) ha ho he
  let y:=mirror A
  let I:=Finset.univ.filter fun i:Fin (s+1)=>b i≠0 ∧ tau A b i=0
  let S:=I.image y
  let Z:=Lagrange.nodal S id
  have card:S.card≤m-2:=Finset.card_image_le.trans (clean_active_budget (by omega) ha ho he)
  have zd:Z.natDegree≤m-2 :=by rw [show Z.natDegree=S.card from Lagrange.natDegree_nodal];exact card
  have cl (i:Fin (s+1)) (bi:b i≠0) (ti:tau A b i=0) : Z.eval (y i)=0 :=
    Lagrange.eval_nodal_at_node (v:=id) (Finset.mem_image_of_mem y (Finset.mem_filter.mpr ⟨Finset.mem_univ _,bi,ti⟩))
  have divi:Z ∣ (X-1)*lobatto m:=by
    apply nodal_dvd_vanishing
    obtain ⟨t,nt,_,_,_,root⟩:=fixed_even_boundary (Or.inr (Or.inr hm)) ha ho he
    intro a h
    obtain ⟨i,hi,rfl⟩:=Finset.mem_image.mp h
    obtain ⟨bi,ti⟩:=(Finset.mem_filter.mp hi).2
    by_cases e:i=t
    · simp [y,mirror,e,nt,lobatto]
    apply lobatto_grid_reflect_zero
    rw [eval_mul,root i e (fun v hv=>weighted_clean (by omega) ha ho he
      non i bi ti v (zeroSpace_mono A (by omega) hv)),mul_zero]
  obtain ⟨Q,hd,fit,off,θ,hθ,active⟩:=port_contrast (by omega) ha ho he non (by decide) (by omega) hf
  have hQ:Q≠0 :=by
    intro eqn
    have on (i) (hi:tau A b i≠0):f i=0:=by simpa [eqn] using fit i hi
    have both:b*f=0 ∧ tau A b*f=0 :=by
      constructor <;> ext i
      · by_cases h:tau A b i=0
        · exact off i h
        · simp [on i h]
      · by_cases h:tau A b i=0
        · simp [h]
        · simp [on i h]
    exact hnot both.1 both.2
  have hai (i:Fin (s+1)) (h:diag y θ i≠0) : b i≠0 ∧ tau A b i=0 :=
    active i (fun z=>h (by rw [diag_apply,z,mul_zero]))
  obtain ⟨i,vi,bi,ti,_,alltests⟩:=physical_reverse_pivot (by omega) ha ho he non
    (by decide) (by omega) (hθ.clock (by omega)) hai (mul_ne_zero X_ne_zero hQ)
  have yn:y i≠0:=fun z=> vi (by change y i*θ i=0;rw [z,zero_mul])
  refine ⟨Z,Q,y i,Lagrange.nodal_monic,zd,divi,yn,cl i bi ti,hd,hQ,?_,?_⟩
  · intro W deg
    have eqn:=hθ.pair_polynomial ho (W*Z) deg
    have zz:weightedEval y θ (W*Z)=0:=by
      ext l
      by_cases h:θ l=0
      · simp [h]
      · have ac:=active l h
        simp [cl l ac.1 ac.2]
    rw [←formalPrimitive_eq_treePrimitive,←eqn,show weightedEval (mirror A) θ (W*Z)=0 from zz];simp
  · intro k
    have eqn:=alltests k.val (by have:=k.isLt;omega)
    rw [show X^k.val*(X*Q)=X^(1+k.val)*Q by rw [pow_add];ring,formalPrimitive_eq_treePrimitive] at eqn
    exact eqn

end
end RKCert.Paired.Terminal
