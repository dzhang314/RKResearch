module
public import RKCert.TerminalLobatto
public import RKCert.DirkPolynomialMarked
@[expose] public section
namespace RKCert.Paired.Terminal
open RKCert.Endpoint Polynomial
variable {K:Type*} [Field K] [CharZero K] {m:ℕ}
noncomputable section

def integral : K[X] →ₗ[K] K := (leval (1:K)).comp Paired.primitive

omit [CharZero K] in
@[simp] theorem integral_eq (P:K[X]) : integral P=(Paired.primitive P).eval 1:=rfl

theorem lobatto_represented (hm:m=7 ∨ m=8 ∨ m=9 ∨ m=10) (P:K[X]) (hp:P.natDegree<m) :
    integral (P*lobatto m)=P.eval 1 := by
  have pos:0<m:=by rcases hm with rfl|rfl|rfl|rfl <;>decide
  have fixed:=(lobatto_fixed (K:=K) hm).1
  let L:K[X] →ₗ[K] K:=integral.comp (LinearMap.mulLeft K (lobatto m))
  rw [mul_comm P];change L P=(leval (1:K)) P
  conv_lhs=>rw [P.as_sum_range]
  conv_rhs=>rw [P.as_sum_range]
  rw [map_sum,map_sum]
  apply Finset.sum_congr rfl
  intro k hk
  have bound:=Finset.mem_range.mp hk
  rw [show monomial k (P.coeff k)=P.coeff k •(X^k:K[X]) by rw [smul_eq_C_mul,C_mul_X_pow_eq_monomial],map_smul,map_smul]
  congr 1
  change (Paired.primitive (lobatto m*X^k)).eval 1=(X^k:K[X]).eval 1
  rw [mul_comm,←formalPrimitive_eq_treePrimitive,primitive_eval_power_mul _ _ _ (lobatto_degree pos)]
  simpa only [lobatto_coeff,one_pow,mul_one,eval_pow,eval_X] using fixed ⟨k,by omega⟩

/-- The full closed-grid polynomial is scalar-orthogonal through degree m−2,
from the already certified native shifted-Legendre moment identity. -/
theorem closed_lobatto_orthogonal (hm:m=7 ∨ m=8 ∨ m=9 ∨ m=10) (P:K[X]) (hp:P.natDegree+2≤m) :
    integral (((X-1)*lobatto m)*P)=0 := by
  rw [show ((X-1)*lobatto m)*P=(X*P)*lobatto m-P*lobatto m by ring,map_sub,
    lobatto_represented hm (X*P) (natDegree_mul_le.trans_lt (by rw [natDegree_X];omega)),
    lobatto_represented hm P (by omega)]
  simp

/-- Evaluation is reproduced after multiplying a grid cardinal L by a paid
test polynomial, since the difference has a closed grid factor. -/
theorem grid_cardinal_eval (hm:m=7 ∨ m=8 ∨ m=9 ∨ m=10) {L:K[X]} {a:K}
    (rep:(X-C a)*L=(X-1)*lobatto m) (Q:K[X]) (dq:Q.natDegree<m) :
    integral (L*Q)=Q.eval a*integral L := by
  obtain ⟨H,e⟩:=dvd_iff_isRoot.mpr (show (Q-C (Q.eval a)).eval a=0 by simp)
  have eqn:Q=(X-C a)*H+C (Q.eval a):=sub_eq_iff_eq_add.mp e
  have pay:H.natDegree+2≤m := by
    by_cases hz:H=0
    · rw [hz,natDegree_zero];rcases hm with rfl|rfl|rfl|rfl <;>decide
    have bound:=natDegree_sub_le Q (C (Q.eval a))
    rw [e,natDegree_mul (X_sub_C_ne_zero _) hz,natDegree_X_sub_C,natDegree_C,max_eq_left (Nat.zero_le _)] at bound
    omega
  have eqn':L*Q=((X-1)*lobatto m)*H+(Q.eval a) • L:=by
    rw [←rep,Polynomial.smul_eq_C_mul]
    calc
      L*Q=L*((X-C a)*H+C (Q.eval a)):=congrArg (L*·) eqn
      _ = _:=by ring
  rw [eqn',map_add,closed_lobatto_orthogonal hm H pay,map_smul,zero_add,smul_eq_mul]

/-- A scalar polynomial through degree m with one endpoint root and all
m low moments zero is zero. Reflection handles the other endpoint with
the exact polynomial integration identity, not positivity over K. -/
theorem endpoint_moment_detect (hm:2≤m) (L:K[X]) (dL:L.natDegree≤m)
    (h0:L.eval 0=0 ∨ L.eval 1=0) (h:∀Q:K[X],Q.natDegree<m → integral (L*Q)=0) : L=0 := by
  have zero (H:K[X]) (deg:H.natDegree≤m) (at0:H.eval 0=0) (mom:∀Q:K[X],Q.natDegree<m → integral (H*Q)=0) : H=0 := by
    obtain ⟨T,hh⟩:=X_dvd_iff.mpr (by simpa only [coeff_zero_eq_eval_zero] using at0)
    by_cases hn:T=0
    · simp [hh,hn]
    have dT:T.natDegree≤m-1:=by rw [hh,natDegree_X_mul hn] at deg;omega
    have eqn:T=0:=primitive_shift_detect T (k:=1) dT 1 one_ne_zero (fun k=>by
      have val:=mom (X^k.val) (by rw [natDegree_X_pow];have:=k.isLt;omega)
      rw [integral_eq,hh,show X*T*X^k.val=X^(1+k.val)*T by rw [pow_add];ring,←formalPrimitive_eq_treePrimitive] at val
      exact val)
    simp [hh,eqn]
  rcases h0 with at0|at1
  · exact zero L dL at0 h
  have val:reflectPolynomial L=0:=zero (reflectPolynomial L) ((reflectPolynomial_degree L).trans dL)
    (by simpa [reflectPolynomial,eval_comp] using at1) (fun Q dQ=>by
      have eqn:=h (reflectPolynomial Q) ((reflectPolynomial_degree Q).trans_lt dQ)
      have e:reflectPolynomial (L*reflectPolynomial Q)=reflectPolynomial L*Q:=by
        simp [reflectPolynomial,mul_comp,comp_assoc]
      change (Paired.primitive _).eval 1=_
      rw [←e,←formalPrimitive_eq_treePrimitive,reflectPolynomial_integral,formalPrimitive_eq_treePrimitive]
      exact eqn)
  have eqn:=congrArg (fun P:K[X]=>reflectPolynomial P) val
  simpa [reflectPolynomial,comp_assoc] using eqn

/-- Every closed-grid cardinal numerator has a nonzero integral. Holds
over arbitrary characteristic-zero fields and at either endpoint. -/
theorem grid_cardinal_nz (hm:m=7 ∨ m=8 ∨ m=9 ∨ m=10) {L:K[X]} {a:K}
    (rep:(X-C a)*L=(X-1)*lobatto m) (dL:L.natDegree≤m) (nz:L≠0) : integral L≠0 := by
  intro no
  have val (x:K): (x-a)*L.eval x=(x-1)*(lobatto m).eval x:= by simpa using congrArg (fun P:K[X]=>P.eval x) rep
  have ep:L.eval 0=0 ∨ L.eval 1=0 := by
    by_cases ha:a=0
    · right;simpa [ha] using val 1
    · left; have e:=val 0
      have f:(lobatto (K:=K) m).eval 0=0:=by simp [lobatto]
      rw [f,mul_zero,zero_sub] at e
      exact (mul_eq_zero.mp e).resolve_left (neg_ne_zero.mpr ha)
  apply nz
  exact endpoint_moment_detect (by rcases hm with rfl|rfl|rfl|rfl <;>decide) L dL ep
    (fun Q hQ=>by rw [grid_cardinal_eval hm rep Q hQ,no,mul_zero])

end
end RKCert.Paired.Terminal
