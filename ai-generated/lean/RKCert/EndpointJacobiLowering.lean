module

public import RKCert.EndpointJacobiTwoRecurrence

@[expose] public section

/-! # Jacobi derivative lowering follows from paid algebraic moments

The leading terms and the formal integration-by-parts identity establish
the lowering remainder without a fitted or modular discriminant.
-/
namespace RKCert.Paired
open Polynomial RKCert.Endpoint
open scoped Classical
noncomputable section
variable {K : Type*} [Field K] [CharZero K]

def jacobiWeight (K : Type*) [Field K] : K[X] := X*(1-X)

omit [CharZero K] in
theorem jacobiWeight_form : jacobiWeight K=X-X^2 := by unfold jacobiWeight; ring

omit [CharZero K] in
theorem jacobiWeight_degree : (jacobiWeight K).natDegree=2 := by
  rw [jacobiWeight_form,show (X-X^2:K[X])= - (X^2-X) by ring,natDegree_neg,
    natDegree_sub_eq_left_of_natDegree_lt (by rw [natDegree_X,natDegree_X_pow]; decide),
    natDegree_X_pow]

omit [CharZero K] in
theorem jacobiWeight_derivative : (jacobiWeight K).derivative=1-C (2:K)*X := by
  rw [jacobiWeight_form,derivative_sub,derivative_X,derivative_sq,derivative_X,mul_one]

theorem jacobiTwo_coeff_top (n : ℕ) : (jacobiTwo K n).coeff n=1 := calc
  _ = (jacobiTwo K n).coeff (jacobiTwo K n).natDegree :=
    congrArg (fun a => (jacobiTwo K n).coeff a) (jacobiTwo_degree n).symm
  _ = (jacobiTwo K n).leadingCoeff := coeff_natDegree
  _ = 1 := jacobiTwo_monic n

theorem jacobiPair_top_coeff (n : ℕ) (pos : 0<n) {Q : K[X]} (deg : Q.natDegree≤n) :
    jacobiPair (jacobiTwo K n) Q=Q.coeff n*jacobiPair (jacobiTwo K n) (jacobiTwo K n) := by
  have dR := jacobiTwo_strip pos deg
  have orth := jacobiPair_orthogonal n (Q-C (Q.coeff n)*jacobiTwo K n) (by omega)
  rw [jacobiPair_symm (jacobiTwo K n) (Q-C (Q.coeff n)*jacobiTwo K n),
    jacobiPair_sub,jacobiPair_C_mul,sub_eq_zero] at orth
  rw [jacobiPair_symm]
  exact orth

theorem jacobiPair_lowering_parts (J Q : K[X]) :
    jacobiPair (jacobiWeight K*J.derivative) Q =
      -jacobiPair J (C (2:K)*(jacobiWeight K).derivative*Q+jacobiWeight K*Q.derivative) := by
  let W := jacobiWeight K
  let S := W^2*Q
  have e0 : S.eval 0=0 := by simp [S,W,jacobiWeight]
  have e1 : S.eval 1=0 := by simp [S,W,jacobiWeight]
  have t := unitIntegral_by_parts (Q:=J) e0 e1
  have T : S.derivative=W*(C (2:K)*W.derivative*Q+W*Q.derivative) := by
    change (W^2*Q).derivative=_
    rw [derivative_mul,derivative_sq]
    ring
  change unitIntegral (J*S.derivative)=-unitIntegral (J.derivative*S) at t
  rw [T,show J*(W*(C (2:K)*W.derivative*Q+W*Q.derivative)) =
    W*J*(C (2:K)*W.derivative*Q+W*Q.derivative) by ring,
    show J.derivative*S=W*(W*J.derivative)*Q by dsimp [S]; ring] at t
  change jacobiPair J (C (2:K)*W.derivative*Q+W*Q.derivative)=
    -jacobiPair (W*J.derivative) Q at t
  change jacobiPair (W*J.derivative) Q=
    -jacobiPair J (C (2:K)*W.derivative*Q+W*Q.derivative)
  linear_combination t

theorem jacobi_lower_combination_degree (n : ℕ) (pos : 0<n) :
    (jacobiWeight K*(jacobiTwo K n).derivative+C (n:K)*(X*jacobiTwo K n)).natDegree≤n := by
  let J := jacobiTwo K n
  let W := jacobiWeight K
  let R := W*J.derivative+C (n:K)*(X*J)
  have jd : J.natDegree=n := jacobiTwo_degree n
  have dd := natDegree_derivative_le J
  have wd : W.natDegree=2 := jacobiWeight_degree
  have wf := natDegree_mul_le (p:=W) (q:=J.derivative)
  have x := natDegree_mul_le (p:=(X:K[X])) (q:=J)
  rw [natDegree_X] at x
  have xc := natDegree_C_mul_le (n:K) (X*J)
  have r : R.natDegree≤n+1 := (natDegree_add_le _ _).trans (max_le (by omega) (by omega))
  have base : J.derivative.coeff n=0 := coeff_eq_zero_of_natDegree_lt (by omega)
  have next : (X^2*J.derivative).coeff (n+1)=(n:K) := by
    rw [coeff_X_pow_mul',ite_eq_left (by omega),coeff_derivative]
    have e : n+1-2+1=n := by omega
    rw [e]
    have top : J.coeff n=1 := jacobiTwo_coeff_top n
    rw [top,one_mul]
    have e' : ((n+1-2:ℕ):K)+1=(n:K) := by exact_mod_cast e
    exact e'
  have c : R.coeff (n+1)=0 := by
    change (jacobiWeight K*J.derivative+C (n:K)*(X*J)).coeff (n+1)=0
    rw [jacobiWeight_form,sub_mul,coeff_add,coeff_sub,coeff_C_mul,coeff_X_mul,base,next,coeff_X_mul]
    have top : J.coeff n=1 := jacobiTwo_coeff_top n
    rw [top,mul_one,zero_sub,neg_add_cancel]
  change R.natDegree≤n
  apply natDegree_le_iff_coeff_eq_zero.mpr
  intro j g
  by_cases e : j=n+1
  · rwa [e]
  · exact coeff_eq_zero_of_natDegree_lt (by omega)

theorem jacobi_lower_bracket_degree (Q : K[X]) {n : ℕ} (hn : 2≤n)
    (dq : Q.natDegree≤n-2) :
    (C (2:K)*(jacobiWeight K).derivative*Q+jacobiWeight K*Q.derivative).natDegree<n := by
  let W := jacobiWeight K
  have dw : W.natDegree=2 := jacobiWeight_degree
  have dp : W.derivative.natDegree≤1 := by have h := natDegree_derivative_le W; omega
  have db : (C (2:K)*W.derivative*Q).natDegree<n := by
    have a := natDegree_C_mul_le (2:K) W.derivative
    exact natDegree_mul_le.trans_lt (by omega)
  have dr : (W*Q.derivative).natDegree<n := by
    by_cases e : Q.natDegree=0
    · rw [derivative_of_natDegree_zero e,mul_zero,natDegree_zero]; omega
    · have p := natDegree_derivative_le Q
      exact natDegree_mul_le.trans_lt (by omega)
  exact (natDegree_add_le _ _).trans_lt (max_lt db dr)

theorem jacobi_lower_bracket_top (n : ℕ) (hn : 2≤n) :
    let J := jacobiTwo K (n-1)
    let T := C (2:K)*(jacobiWeight K).derivative*J+jacobiWeight K*J.derivative
    T.natDegree≤n ∧ T.coeff n= -((n:K)+3) := by
  let J := jacobiTwo K (n-1)
  let W := jacobiWeight K
  let T := C (2:K)*W.derivative*J+W*J.derivative
  have jt : J.natDegree=n-1 := jacobiTwo_degree (n-1)
  have w : W.natDegree=2 := jacobiWeight_degree
  have jd := natDegree_derivative_le J
  have wd := natDegree_derivative_le W
  have a := natDegree_C_mul_le (2:K) W.derivative
  have Tn : T.natDegree≤n := (natDegree_add_le _ _).trans
    (max_le (natDegree_mul_le.trans (by omega)) (natDegree_mul_le.trans (by omega)))
  refine ⟨Tn,?_⟩
  change T.coeff n= -((n:K)+3)
  have Teq : T=C (2:K)*J-C (4:K)*(X*J)+X*J.derivative-X^2*J.derivative := by
    change C (2:K)*(jacobiWeight K).derivative*J+jacobiWeight K*J.derivative=_
    rw [jacobiWeight_derivative,jacobiWeight_form]
    rw [show C (4:K)=C (2:K)*C (2:K) by rw [←map_mul]; norm_num]
    ring
  have at0 : J.coeff n=0 := coeff_eq_zero_of_natDegree_lt (by omega)
  have at1 : (X*J).coeff n=1 := by
    rw [show n=(n-1)+1 by omega,coeff_X_mul]
    exact jacobiTwo_coeff_top _
  have at2 : (X*J.derivative).coeff n=0 := by
    rw [show n=(n-1)+1 by omega,coeff_X_mul]
    exact coeff_eq_zero_of_natDegree_lt (by omega)
  have at3 : (X^2*J.derivative).coeff n=((n-1:ℕ):K) := by
    rw [coeff_X_pow_mul',ite_eq_left hn,coeff_derivative]
    have e : n-2+1=n-1 := by omega
    rw [e]
    have top : J.coeff (n-1)=1 := jacobiTwo_coeff_top _
    rw [top,one_mul,←Nat.cast_one,←Nat.cast_add,e]
  rw [Teq,coeff_sub,coeff_add,coeff_sub,coeff_C_mul,coeff_C_mul,at0,at1,at2,at3]
  push_cast [Nat.cast_sub (by omega : 1≤n)]
  ring

set_option maxHeartbeats 2300000 in
theorem jacobiTwo_lowering (n : ℕ) (hn : 2≤n) (a b : K)
    (recurrence : X*jacobiTwo K n=jacobiTwo K (n+1)+C a*jacobiTwo K n+C b*jacobiTwo K (n-1)) :
    ∃ m : K, jacobiWeight K*(jacobiTwo K n).derivative =
      (C m-C (n:K)*X)*jacobiTwo K n+C ((2*(n:K)+3)*b)*jacobiTwo K (n-1) := by
  let J := jacobiTwo K n
  let L := jacobiTwo K (n-1)
  let W := jacobiWeight K
  let P := W*J.derivative+C (n:K)*(X*J)
  have pd : P.natDegree≤n := jacobi_lower_combination_degree n (by omega)
  have lt (Q : K[X]) (hq : Q.natDegree≤n-2) : jacobiPair P Q=0 := by
    have d := natDegree_mul_le (p:=(X:K[X])) (q:=Q)
    rw [natDegree_X] at d
    change jacobiPair (jacobiWeight K*J.derivative+C (n:K)*(X*J)) Q=0
    rw [jacobiPair_add,jacobiPair_lowering_parts,jacobiPair_C_mul,jacobiPair_mul_X,
      jacobiPair_orthogonal _ _ (jacobi_lower_bracket_degree Q hn hq),
      jacobiPair_orthogonal _ _ (by omega : (X*Q).natDegree<n),neg_zero,mul_zero,add_zero]
  obtain ⟨m,r,e⟩ := jacobiTwo_top_two hn pd lt
  have ld : L.natDegree=n-1 := jacobiTwo_degree (n-1)
  have xd : (X*L).natDegree≤n := by
    have p := natDegree_mul_le (p:=(X:K[X])) (q:=L)
    rw [natDegree_X] at p
    omega
  have xcoeff : (X*L).coeff n=1 := by
    rw [show n=(n-1)+1 by omega,coeff_X_mul]
    exact jacobiTwo_coeff_top _
  have cross : jacobiPair (X*J) L=jacobiPair J J := by
    rw [jacobiPair_mul_X,jacobiPair_top_coeff n (by omega) xd,xcoeff,one_mul]
  have db : b*jacobiPair L L=jacobiPair J J := by
    change X*J=jacobiTwo K (n+1)+C a*J+C b*L at recurrence
    rw [recurrence,jacobiPair_add,jacobiPair_add,jacobiPair_C_mul,jacobiPair_C_mul,
      jacobiPair_orthogonal _ _ (by omega : L.natDegree<n+1),
      jacobiPair_orthogonal _ _ (by omega : L.natDegree<n),mul_zero,add_zero,zero_add] at cross
    exact cross
  have di : jacobiPair (W*J.derivative) L=((n:K)+3)*jacobiPair J J := by
    obtain ⟨bd,eq⟩ := jacobi_lower_bracket_top (K:=K) n hn
    change (C (2:K)*W.derivative*L+W*L.derivative).natDegree≤n at bd
    change (C (2:K)*W.derivative*L+W*L.derivative).coeff n= -((n:K)+3) at eq
    rw [jacobiPair_lowering_parts,jacobiPair_top_coeff n (by omega) bd,eq]
    ring
  have left : jacobiPair P L=(2*(n:K)+3)*jacobiPair J J := by
    change jacobiPair (W*J.derivative+C (n:K)*(X*J)) L=_
    rw [jacobiPair_add,jacobiPair_C_mul,di,cross]
    ring
  have right : jacobiPair P L=r*jacobiPair L L := by
    change P=C m*J+C r*L at e
    rw [e,jacobiPair_add,jacobiPair_C_mul,jacobiPair_C_mul,
      jacobiPair_orthogonal _ _ (by omega : L.natDegree<n),mul_zero,zero_add]
  have rr : r=(2*(n:K)+3)*b := by
    apply mul_right_cancel₀ (jacobiTwo_diagonal_ne (K:=K) (n-1))
    change r*jacobiPair L L=(2*(n:K)+3)*b*jacobiPair L L
    rw [mul_assoc,db,←left,right]
  refine ⟨m,?_⟩
  change W*J.derivative=(C m-C (n:K)*X)*J+C ((2*(n:K)+3)*b)*L
  change W*J.derivative+C (n:K)*(X*J)=C m*J+C r*L at e
  rw [rr] at e
  linear_combination e

end
end RKCert.Paired
