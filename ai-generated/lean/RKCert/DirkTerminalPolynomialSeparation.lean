module

public import RKCert.Dirk15RadauPorts

@[expose] public section

/-! # One paid terminal condition replaces the highest scalar test -/
namespace RKCert.Paired
open Polynomial RKCert.Endpoint
open scoped Classical
noncomputable section
variable {K : Type*} [Field K] [CharZero K] {s p j m : ℕ}
variable {A : Fin s→Fin s→K} {b : Vec K s}

theorem terminal_polynomial_defect_zero (ho : HasTreeOrderAtLeast A b p)
    (hm : 1≤m) (hj : m≤j) (hp : j+m≤p) {P : K[X]}
    (dP : P.natDegree≤m) (terminal : P.eval 1=0)
    (pure : evalNodes A P∈zeroSpace A j) : P=0 := by
  let Q := reflectPolynomial P
  by_contra nz
  have qn : Q≠0 := by
    intro e
    apply nz
    have r := reflectPolynomial_involutive P
    change reflectPolynomial Q=P at r
    rw [e,show reflectPolynomial (0:K[X])=0 by simp [reflectPolynomial]] at r
    exact r.symm
  have q0 : Q.eval 0=0 := by
    simpa [Q,reflectPolynomial,Polynomial.eval_comp] using terminal
  have div : X∣Q := by rwa [X_dvd_iff,coeff_zero_eq_eval_zero]
  obtain ⟨T,qt⟩ := div
  have tn : T≠0 := fun e => qn (by rw [qt,e,mul_zero])
  have dt : T.natDegree≤m-1 := by
    have d := (reflectPolynomial_degree P).trans dP
    change Q.natDegree≤m at d
    rw [qt,natDegree_X_mul tn] at d
    omega
  apply tn
  apply primitive_shift_detect T (k:=1) dt 1 one_ne_zero
  intro i
  let R := reflectPolynomial (X^i.val : K[X])
  have dr : R.natDegree ≤ i.val := (reflectPolynomial_degree _).trans (natDegree_X_pow _).le
  have pay : j+R.natDegree+1≤p := by have := i.isLt; omega
  have tr : OrdinaryTrace A j (evalNodes A P) 0 := by
    refine ⟨by simp,?_⟩
    have z : evalNodes A (0:K[X])=0 := by ext a; simp
    simpa only [z,sub_zero] using pure
  have t0 := tr.pair_polynomial ho R pay
  have t1 := (OrdinaryTrace.scalar A (n:=j) (dP.trans hj)).pair_polynomial ho R pay
  have zero : (formalPrimitive (P*R)).eval 1=0 := by
    rw [←t1,t0,zero_mul]
    simp [formalPrimitive]
  have e : reflectPolynomial (P*R)=Q*X^i.val := by
    change (P*R).comp (1-X)=_
    rw [mul_comp]
    change Q*reflectPolynomial (reflectPolynomial (X^i.val))=_
    rw [reflectPolynomial_involutive]
  have reflect := reflectPolynomial_integral (P*R)
  rw [e,qt,show X*T*X^i.val=X^(1+i.val)*T by rw [pow_add,pow_one]; ring] at reflect
  exact reflect.trans zero

end
end RKCert.Paired
