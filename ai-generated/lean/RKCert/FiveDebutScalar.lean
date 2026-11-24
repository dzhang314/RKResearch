module

public import RKCert.FiveDebutScalarSkeleton

@[expose] public section

/-! # The refunded fifth-site contradiction, independent of any array
The physical proof supplies exactly three observations: the first
primitive on the three earlier knots, and two primitives through the
actual explicit fifth pivot. No fourth refund or sixth site is assumed. -/
namespace RKCert.FiveDebut
open Polynomial RKCert.Endpoint RKCert.Paired
open scoped Classical
noncomputable section
variable {K : Type*} [Field K] [CharZero K]

def prefixThree (i : Fin 3) : Fin 5 := Fin.castLE (by decide) i
def prefixFour (i : Fin 4) : Fin 5 := Fin.castLE (by decide) i

def threeNodal (z : Fin 5→K) : K[X] := Lagrange.nodal Finset.univ (z ∘ prefixThree)
def fourNodal (z : Fin 5→K) : K[X] := Lagrange.nodal Finset.univ (z ∘ prefixFour)

omit [CharZero K] in
private theorem nodal_dvd_of_eval_zero {n : ℕ} (a : Fin n→K) (ai : Function.Injective a)
    {P : K[X]} (h : ∀ i,P.eval (a i)=0) : Lagrange.nodal Finset.univ a∣P := by
  classical
  rw [Lagrange.nodal_eq]
  apply Finset.prod_dvd_of_coprime
  · intro i _ j _ ij
    exact isCoprime_X_sub_C_of_isUnit_sub (sub_ne_zero.mpr (fun e => ij (ai e))).isUnit
  · intro i _
    exact dvd_iff_isRoot.mpr (h i)

omit [CharZero K] in
private theorem nodal_quotient {n r : ℕ} (a : Fin n→K) (ai : Function.Injective a)
    (P Q : K[X]) (dP : P.natDegree≤n+r) (dQ : Q.natDegree≤n+r)
    (ev : ∀ i,P.eval (a i)=Q.eval (a i)) :
    ∃ R : K[X],R.natDegree≤r ∧ P=Q+R*Lagrange.nodal Finset.univ a := by
  obtain ⟨R,e⟩ := nodal_dvd_of_eval_zero a ai (P:=P-Q) (fun i => by simp [ev i])
  refine ⟨R,?_,?_⟩
  · by_cases z : R=0
    · simp [z]
    have d := (natDegree_sub_le P Q).trans (max_le dP dQ)
    rw [e,natDegree_mul Lagrange.nodal_ne_zero z,Lagrange.natDegree_nodal,
      Finset.card_univ,Fintype.card_fin] at d
    omega
  · linear_combination e

omit [CharZero K] in
private theorem nodal_deriv_ne {n : ℕ} (a : Fin n→K) (ai : Function.Injective a) (i : Fin n) :
    (Lagrange.nodal Finset.univ a).derivative.eval (a i)≠0 := by
  classical
  rw [Lagrange.eval_nodal_derivative_eval_node_eq (Finset.mem_univ i)]
  apply Lagrange.eval_nodal_not_at_node
  intro j hj h
  exact Finset.ne_of_mem_erase hj (ai h.symm)

omit [CharZero K] in
private theorem natDegree_of_small_degree {P : K[X]} {n : ℕ} (hn : 0<n)
    (h : P.degree<(n:WithBot ℕ)) : P.natDegree<n := by
  by_cases hp : P=0
  · simpa only [hp,natDegree_zero] using hn
  exact (natDegree_lt_iff_degree_lt hp).mpr h

omit [CharZero K] in
private theorem eq_polys_at_nodes {n : ℕ} (a : Fin n→K) (ai : Function.Injective a)
    {P Q : K[X]} (dp : P.natDegree<n) (dq : Q.natDegree<n)
    (ev : ∀ i,P.eval (a i)=Q.eval (a i)) : P=Q := by
  classical
  let S := Finset.univ.image a
  have cs : S.card=n := by rw [Finset.card_image_of_injective _ ai,Finset.card_univ,Fintype.card_fin]
  apply eq_of_degrees_lt_of_eval_finset_eq S
  · rw [cs]
    exact degree_le_natDegree.trans_lt (by exact_mod_cast dp)
  · rw [cs]
    exact degree_le_natDegree.trans_lt (by exact_mod_cast dq)
  · intro v hv
    obtain ⟨i,_,rfl⟩ := Finset.mem_image.mp hv
    exact ev i

private def predOne (u : K) : K[X] := C (1/18:K)*(X-C u)
private def restZero : K[X] := C (-(1/18:K))
private def factorTwo (u : K) : K[X] := C (1/14:K)*(C 18*X-C 2*C u)
private def predTwo (u : K) : K[X] := factorTwo u*predOne u
private def restOne (u : K) : K[X] := factorTwo u*restZero-C (1/14:K)*(X-C u)

omit [CharZero K] in
private theorem predOne_degree (u : K) : (predOne u).natDegree≤1 :=
  (natDegree_C_mul_le _ _).trans (natDegree_X_sub_C u).le

omit [CharZero K] in
private theorem predTwo_degree (u : K) : (predTwo u).natDegree≤2 := by
  apply natDegree_mul_le.trans
  have t : (factorTwo u).natDegree≤1 := by
    apply (natDegree_C_mul_le _ _).trans
    apply (natDegree_sub_le _ _).trans
    refine max_le ((natDegree_C_mul_le _ _).trans natDegree_X_le) ?_
    exact (natDegree_C_mul_le _ _).trans (by rw [natDegree_C]; omega)
  have v := predOne_degree u
  omega

/-- The second refunded primitive is a fixed polynomial expression in the
first slope. The fourth knot is symbolic, not normalized by a numerical map. -/
private theorem two_paid_forms (V : K[X]) (u : K)
    (h : shiftedPrimitive V=C (1/18:K)*(X-C u)*V.derivative-C (1/18:K)*V) :
    formalPrimitive (X*V)=X^2*(predOne u*V.derivative+restZero*V) ∧
      formalPrimitive (X^2*V)=X^2*(predTwo u*V.derivative+restOne u*V) := by
  have h1 : formalPrimitive (X*V)=X^2*(predOne u*V.derivative+restZero*V) := by
    rw [←shiftedPrimitive_mul,h,predOne,restZero,map_neg]
    ring
  have c18 : C (18:K)*C (1/18:K)=1 := by rw [←map_mul]; norm_num
  have c14 : C (14:K)*C (1/14:K)=1 := by rw [←map_mul]; norm_num
  have scaled : C 18*formalPrimitive (X*V)=X^2*((X-C u)*V.derivative-V) := by
    rw [h1,predOne,restZero,map_neg]
    calc
      _ = (C (18:K)*C (1/18:K))*(X^2*((X-C u)*V.derivative-V)) := by ring
      _ = _ := by rw [c18,one_mul]
  have rel : C 14*formalPrimitive (X^2*V) =
      (C 18*X-C 2*C u)*formalPrimitive (X*V)-X^2*(X-C u)*V := by
    apply eq_of_derivative_and_eval_zero
    · simp only [derivative_mul,derivative_sub,derivative_C,derivative_X,derivative_X_pow,
        derivative_formalPrimitive,zero_mul,zero_add,mul_zero,add_zero,mul_one]
      norm_num
      simp only [map_ofNat] at scaled ⊢
      linear_combination -scaled
    · simp
  refine ⟨h1,?_⟩
  apply mul_left_cancel₀ (C_ne_zero.mpr (by norm_num : (14:K)≠0))
  rw [rel,h1,predTwo,restOne,factorTwo]
  calc
    _ = X^2*(((C (18:K)*X-C 2*C u)*predOne u)*V.derivative+
          ((C (18:K)*X-C 2*C u)*restZero-(X-C u))*V) := by ring
    _ = _ := by
      rw [←one_mul (X^2*(((C (18:K)*X-C 2*C u)*predOne u)*V.derivative+
          ((C (18:K)*X-C 2*C u)*restZero-(X-C u))*V)),←c14]
      ring

private theorem predicted_det (u : K) :
    restZero*predTwo u-restOne u*predOne u=C (1/252:K)*(X-C u)^2 := by
  have hc : C (1/14:K)*C (1/18:K)=C (1/252:K) := by rw [←map_mul]; norm_num
  rw [predTwo,restOne,predOne,←hc]
  ring

set_option maxHeartbeats 650000 in
theorem five_scalar_impossible (z w : Fin 5→K) (zi : Function.Injective z)
    (zn : ∀ i,z i≠0) (lam : K) (lam_ne : lam≠0)
    (amp : ∀ i : Fin 4, w (prefixFour i)=lam*z (prefixFour i)^2*
      (fourNodal z).derivative.eval (z (prefixFour i)))
    (obs3 : ∃ A : K[X], A.degree<(2:WithBot ℕ) ∧
      ∀ i : Fin 3,(primitive (X*threeNodal z)).eval (z (prefixThree i))=
        w (prefixThree i)*A.eval (z (prefixThree i)))
    (obs4 : ∃ B : K[X], B.degree<(2:WithBot ℕ) ∧
      ∀ i : Fin 5,(primitive (X*fourNodal z)).eval (z i)=w i*B.eval (z i))
    (obs5 : ∃ D : K[X], D.degree<(3:WithBot ℕ) ∧
      ∀ i : Fin 5,(primitive (X^2*fourNodal z)).eval (z i)=w i*D.eval (z i)) : False := by
  classical
  let a₃ := z ∘ prefixThree
  let a₄ := z ∘ prefixFour
  let U := threeNodal z
  let V := fourNodal z
  let u := a₄ (Fin.last 3)
  let v := z (Fin.last 4)
  have i₃ : Function.Injective a₃ := fun i j h => Fin.ext (congrArg (fun x : Fin 5 => x.val) (zi h))
  have i₄ : Function.Injective a₄ := fun i j h => Fin.ext (congrArg (fun x : Fin 5 => x.val) (zi h))
  have un : u≠0 := zn _
  have vn : v≠0 := zn _
  have vu : v≠u := fun e => (by decide : (Fin.last 4 : Fin 5)≠prefixFour (Fin.last 3)) (zi e)
  have dU : U.natDegree=3 := by simp only [U,threeNodal,Lagrange.natDegree_nodal,Finset.card_univ,Fintype.card_fin]
  have dV : V.natDegree=4 := by simp only [V,fourNodal,Lagrange.natDegree_nodal,Finset.card_univ,Fintype.card_fin]
  have uv : V=(X-C u)*U := by
    simp only [V,U,fourNodal,threeNodal,Lagrange.nodal_eq]
    rw [Fin.prod_univ_castSucc,mul_comm]
    rfl
  have Uu : U.eval u≠0 := by
    apply Lagrange.eval_nodal_not_at_node
    intro i _ e
    exact (show prefixFour (Fin.last 3)≠prefixThree i from fun h => by
      have hk := congrArg Fin.val h
      change 3=i.val at hk
      omega) (zi e)
  have V0 : V.eval 0≠0 := by
    apply Lagrange.eval_nodal_not_at_node
    intro i _
    exact Ne.symm (zn (prefixFour i))
  have Vv : V.eval v≠0 := by
    apply Lagrange.eval_nodal_not_at_node
    intro i _ e
    have hk := congrArg Fin.val (zi e)
    change 4=i.val at hk
    omega
  have uz (i : Fin 3) : U.eval (a₃ i)=0 := Lagrange.eval_nodal_at_node (Finset.mem_univ i)
  have vz (i : Fin 4) : V.eval (a₄ i)=0 := Lagrange.eval_nodal_at_node (Finset.mem_univ i)
  have dUroot := nodal_deriv_ne a₃ i₃
  have dVroot (i : Fin 4) : V.derivative.eval (a₄ i)≠0 := nodal_deriv_ne a₄ i₄ i
  have an3 (i : Fin 3) : a₃ i≠0 := zn _
  have an4 (i : Fin 4) : a₄ i≠0 := zn _
  have amplit (i : Fin 4) : w (prefixFour i)=lam*(a₄ i)^2*V.derivative.eval (a₄ i) := amp i
  have dVeq : V.derivative=(X-C u)*U.derivative+U := by
    rw [uv,derivative_mul,derivative_sub,derivative_X,derivative_C,sub_zero,one_mul,add_comm]
  obtain ⟨T,dt,obsU⟩ := obs3
  obtain ⟨A,da,obsV⟩ := obs4
  obtain ⟨B,db,obsW⟩ := obs5
  have dT : T.natDegree≤1 := Nat.le_of_lt_succ (natDegree_of_small_degree (n:=2) (by decide) dt)
  have dA : A.natDegree≤1 := Nat.le_of_lt_succ (natDegree_of_small_degree (n:=2) (by decide) da)
  have dB : B.natDegree≤2 := Nat.le_of_lt_succ (natDegree_of_small_degree (n:=3) (by decide) db)
  let K₃ := C lam*T
  let K₄ := C lam*A
  have dK₃ : K₃.natDegree≤1 := (natDegree_C_mul_le _ _).trans dT
  have dK₄ : K₄.natDegree≤1 := (natDegree_C_mul_le _ _).trans dA
  have obsL₃ (i : Fin 3) :
      (shiftedPrimitive U).eval (a₃ i)=(((X-C u)*K₃)*U.derivative).eval (a₃ i) := by
    have e := congrArg (Polynomial.eval (a₃ i)) (shiftedPrimitive_mul U)
    have hp : (formalPrimitive (X*U)).eval (a₃ i)=w (prefixThree i)*T.eval (a₃ i) := by
      rw [formalPrimitive_eq_treePrimitive]
      exact obsU i
    have h := amplit i.castSucc
    change w (prefixThree i)=lam*(a₃ i)^2*V.derivative.eval (a₃ i) at h
    rw [dVeq] at h
    simp only [eval_mul,eval_pow,eval_X,hp,h,eval_add,uz i,add_zero,eval_sub,eval_C] at e
    apply mul_left_cancel₀ (pow_ne_zero 2 (an3 i))
    simp only [K₃,eval_mul,eval_sub,eval_C,eval_X]
    linear_combination e
  have obsL₄ (i : Fin 4) : (shiftedPrimitive V).eval (a₄ i)=(K₄*V.derivative).eval (a₄ i) := by
    have e := congrArg (Polynomial.eval (a₄ i)) (shiftedPrimitive_mul V)
    have hp : (formalPrimitive (X*V)).eval (a₄ i)=w (prefixFour i)*A.eval (a₄ i) := by
      rw [formalPrimitive_eq_treePrimitive]
      exact obsV _
    simp only [eval_mul,eval_pow,eval_X,hp,amplit i] at e
    apply mul_left_cancel₀ (pow_ne_zero 2 (an4 i))
    simp only [K₄,eval_mul,eval_C]
    linear_combination e
  have dg₃ : (((X-C u)*K₃)*U.derivative).natDegree≤3+1 := by
    apply natDegree_mul_le.trans
    have m : ((X-C u)*K₃).natDegree≤2 := natDegree_mul_le.trans (by
      rw [natDegree_X_sub_C]; omega)
    rw [natDegree_derivative,dU]
    omega
  have dg₄ : (K₄*V.derivative).natDegree≤4+0 := by
    apply natDegree_mul_le.trans
    rw [natDegree_derivative,dV]
    omega
  obtain ⟨E,dE,hE⟩ := nodal_quotient a₃ i₃ (shiftedPrimitive U) (((X-C u)*K₃)*U.derivative)
    (by rw [shiftedPrimitive_degree,dU]; decide) dg₃ obsL₃
  obtain ⟨R,dR,hR⟩ := nodal_quotient a₄ i₄ (shiftedPrimitive V) (K₄*V.derivative)
    (by rw [shiftedPrimitive_degree,dV]) dg₄ obsL₄
  rw [eq_C_of_natDegree_le_zero dR] at hR
  have skeleton := four_knot_skeleton u un uv dU Uu V0 a₃ i₃
    (fun i => zn (prefixThree i)) uz dUroot dK₄ dK₃ dE (R.coeff 0) hR hE
  obtain ⟨J₁,J₂⟩ := two_paid_forms V u skeleton
  have fit₁ : C lam*A=predOne u := by
    apply eq_polys_at_nodes a₄ i₄
      (lt_of_le_of_lt dK₄ (by decide)) ((predOne_degree u).trans_lt (by decide))
    intro i
    have e := congrArg (Polynomial.eval (a₄ i)) J₁
    have hp : (formalPrimitive (X*V)).eval (a₄ i)=w (prefixFour i)*A.eval (a₄ i) := by
      rw [formalPrimitive_eq_treePrimitive]
      exact obsV _
    simp only [eval_mul,eval_pow,eval_X,eval_add,hp,amplit i,vz i,mul_zero,add_zero] at e
    apply mul_left_cancel₀ (mul_ne_zero (pow_ne_zero 2 (an4 i)) (dVroot i))
    change (a₄ i)^2*V.derivative.eval (a₄ i)*(C lam*A).eval (a₄ i)=_
    simp only [eval_mul,eval_C]
    linear_combination e
  have fit₂ : C lam*B=predTwo u := by
    apply eq_polys_at_nodes a₄ i₄
      (((natDegree_C_mul_le _ _).trans dB).trans_lt (by decide))
      ((predTwo_degree u).trans_lt (by decide))
    intro i
    have e := congrArg (Polynomial.eval (a₄ i)) J₂
    have hp : (formalPrimitive (X^2*V)).eval (a₄ i)=w (prefixFour i)*B.eval (a₄ i) := by
      rw [formalPrimitive_eq_treePrimitive]
      exact obsW _
    simp only [eval_mul,eval_pow,eval_X,eval_add,hp,amplit i,vz i,mul_zero,add_zero] at e
    apply mul_left_cancel₀ (mul_ne_zero (pow_ne_zero 2 (an4 i)) (dVroot i))
    simp only [eval_mul,eval_C]
    linear_combination e
  have r₁ := congrArg (Polynomial.eval v) J₁
  have r₂ := congrArg (Polynomial.eval v) J₂
  have c₁ := congrArg (Polynomial.eval v) fit₁
  have c₂ := congrArg (Polynomial.eval v) fit₂
  have p₁ : (formalPrimitive (X*V)).eval v=w (Fin.last 4)*A.eval v := by
    rw [formalPrimitive_eq_treePrimitive]; exact obsV _
  have p₂ : (formalPrimitive (X^2*V)).eval v=w (Fin.last 4)*B.eval v := by
    rw [formalPrimitive_eq_treePrimitive]; exact obsW _
  simp only [eval_mul,eval_C] at c₁ c₂
  simp only [eval_mul,eval_pow,eval_X,eval_add,p₁,p₂] at r₁ r₂
  let g := lam*v^2*V.eval v
  let r := w (Fin.last 4)-lam*v^2*V.derivative.eval v
  have e₁ : g*(restZero : K[X]).eval v=r*(predOne u).eval v := by
    dsimp only [g,r]; linear_combination -lam*r₁+w (Fin.last 4)*c₁
  have e₂ : g*(restOne u).eval v=r*(predTwo u).eval v := by
    dsimp only [g,r]; linear_combination -lam*r₂+w (Fin.last 4)*c₂
  have ed : g*((restZero : K[X]).eval v*(predTwo u).eval v-(restOne u).eval v*(predOne u).eval v)=0 := by
    linear_combination (predTwo u).eval v*e₁-(predOne u).eval v*e₂
  have ne : g≠0 := mul_ne_zero (mul_ne_zero lam_ne (pow_ne_zero _ vn)) Vv
  have d0 := (mul_eq_zero.mp ed).resolve_left ne
  have dd := congrArg (Polynomial.eval v) (predicted_det u)
  simp only [eval_sub,eval_mul,eval_C,eval_pow,eval_X,d0] at dd
  exact mul_ne_zero (by norm_num : (1/252:K)≠0) (pow_ne_zero 2 (sub_ne_zero.mpr vu)) dd.symm

end
end RKCert.FiveDebut
