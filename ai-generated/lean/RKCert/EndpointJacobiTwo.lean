module

public import RKCert.DirkOneEndpointHilbert
public import RKCert.RadauMissingRoot
public import Mathlib.RingTheory.Polynomial.ShiftedLegendre

@[expose] public section

/-! # Algebraic orthogonality for the fixed weight x(1-x)

Mathlib's integer shifted Legendre polynomials give the Jacobi basis via
differentiation. Orthogonality uses algebraic formal integration by parts,
not positivity, real zeros, or an order on the coefficient field.
-/
namespace RKCert.Paired
open Polynomial RKCert.Endpoint
open scoped Classical
noncomputable section
variable {K : Type*} [Field K] [CharZero K]

theorem unitIntegral_derivative (Q : K[X]) :
    unitIntegral Q.derivative=Q.eval 1-Q.eval 0 := by
  have he : formalPrimitive Q.derivative=Q-C (Q.eval 0) := by
    apply eq_of_derivative_and_eval_zero
    · rw [derivative_formalPrimitive,derivative_sub,derivative_C,sub_zero]
    · simp
  rw [unitIntegral_apply,he,eval_sub,eval_C]

theorem unitIntegral_by_parts {Q P : K[X]} (h0 : P.eval 0=0) (h1 : P.eval 1=0) :
    unitIntegral (Q*P.derivative)=-unitIntegral (Q.derivative*P) := by
  have h := unitIntegral_derivative (Q*P)
  rw [derivative_mul,map_add,eval_mul,eval_mul,h0,h1,mul_zero,mul_zero,sub_self] at h
  exact eq_neg_of_add_eq_zero_right h

theorem unitIntegral_iterate_by_parts (P Q : K[X]) (n : ℕ)
    (ends : ∀ k<n, (Polynomial.derivative^[k] P).eval 0=0 ∧
      (Polynomial.derivative^[k] P).eval 1=0) :
    unitIntegral (Q*(Polynomial.derivative^[n] P)) =
      (-1:K)^n*unitIntegral ((Polynomial.derivative^[n] Q)*P) := by
  induction n generalizing Q with
  | zero => simp
  | succ n ih =>
    rw [Function.iterate_succ_apply',unitIntegral_by_parts
      (ends n (Nat.lt_succ_self n)).1 (ends n (Nat.lt_succ_self n)).2]
    rw [ih Q.derivative (fun k hk => ends k (hk.trans (Nat.lt_succ_self n)))]
    rw [Function.iterate_succ_apply,pow_succ]
    ring

def mappedLegendre (K : Type*) [Field K] (n : ℕ) : K[X] :=
  (shiftedLegendre n).map (Int.castRingHom K)

theorem mappedLegendre_degree (n : ℕ) : (mappedLegendre K n).natDegree=n := by
  rw [mappedLegendre,natDegree_map_eq_of_injective (Int.cast_injective (α:=K)),natDegree_shiftedLegendre]

omit [CharZero K] in
theorem mappedLegendre_rodrigues (n : ℕ) :
    C (Nat.factorial n : K)*mappedLegendre K n =
      Polynomial.derivative^[n] ((X:K[X])^n*(1-X)^n) := by
  let phi := Int.castRingHom K
  have e := congrArg (Polynomial.map phi) (factorial_mul_shiftedLegendre_eq n)
  rw [Polynomial.map_mul,←iterate_derivative_map,Polynomial.map_natCast] at e
  have e' : (Nat.factorial n:K[X])*mappedLegendre K n =
      Polynomial.derivative^[n] ((X:K[X])^n*(1-X)^n) := by
    simpa only [Polynomial.map_mul,Polynomial.map_pow,Polynomial.map_sub,Polynomial.map_X,
      Polynomial.map_one,mappedLegendre] using e
  rwa [←C_eq_natCast] at e'

theorem mappedLegendre_orthogonal (n : ℕ) (Q : K[X]) (d : Q.natDegree<n) :
    unitIntegral (Q*mappedLegendre K n)=0 := by
  let P : K[X] := X^n*(1-X)^n
  have e0 : (X:K[X])^n∣P := ⟨(1-X)^n,rfl⟩
  have e1 : (1-X:K[X])^n∣P := ⟨X^n,mul_comm _ _⟩
  have ends (k : ℕ) (h : k<n) :
      (Polynomial.derivative^[k] P).eval 0=0 ∧ (Polynomial.derivative^[k] P).eval 1=0 := by
    obtain ⟨Z,z⟩ := pow_sub_dvd_iterate_derivative_of_pow_dvd k e0
    obtain ⟨T,t⟩ := pow_sub_dvd_iterate_derivative_of_pow_dvd k e1
    have pos : n-k≠0 := by omega
    constructor
    · rw [z,eval_mul,eval_pow,eval_X,zero_pow pos,zero_mul]
    · rw [t,eval_mul,eval_pow,eval_sub,eval_one,eval_X,sub_self,zero_pow pos,zero_mul]
  have h := unitIntegral_iterate_by_parts P Q n ends
  rw [iterate_derivative_eq_zero d,zero_mul,map_zero,mul_zero] at h
  change unitIntegral (Q*(Polynomial.derivative^[n] ((X:K[X])^n*(1-X)^n)))=0 at h
  rw [←mappedLegendre_rodrigues,show Q*(C (Nat.factorial n : K)*mappedLegendre K n) =
    (Nat.factorial n : K) • (Q*mappedLegendre K n) by rw [smul_eq_C_mul]; ac_rfl,
    map_smul,smul_eq_mul] at h
  exact (mul_eq_zero.mp h).resolve_left (Nat.cast_ne_zero.mpr (Nat.factorial_ne_zero n))

def jacobiTwo (K : Type*) [Field K] (n : ℕ) : K[X] :=
  normalize ((mappedLegendre K (n+1)).derivative)

theorem jacobiTwo_degree (n : ℕ) : (jacobiTwo K n).natDegree=n := by
  rw [jacobiTwo,natDegree_normalize,natDegree_derivative,mappedLegendre_degree]
  omega

theorem jacobiTwo_raw_ne (n : ℕ) : (mappedLegendre K (n+1)).derivative≠0 :=
  derivative_ne_zero.mpr (by rw [mappedLegendre_degree]; omega)

theorem jacobiTwo_monic (n : ℕ) : (jacobiTwo K n).Monic :=
  monic_normalize (jacobiTwo_raw_ne n)

theorem jacobiTwo_orthogonal (n : ℕ) (Q : K[X]) (d : Q.natDegree<n) :
    unitIntegral (((X:K[X])*(1-X))*(jacobiTwo K n)*Q)=0 := by
  let S : K[X] := X*(1-X)*Q
  let J := mappedLegendre K (n+1)
  have end0 : S.eval 0=0 := by simp [S]
  have end1 : S.eval 1=0 := by simp [S]
  have bound : S.natDegree≤Q.natDegree+2 := by
    have W : ((X:K[X])*(1-X)).natDegree≤2 := by
      have h := natDegree_mul_le (p:=(X:K[X])) (q:=1-X)
      have w : (1-X:K[X]).natDegree≤1 := (natDegree_sub_le _ _).trans (by simp)
      rw [natDegree_X] at h
      omega
    exact natDegree_mul_le.trans (by have := Nat.add_le_add_right W Q.natDegree; omega)
  have der : S.derivative.natDegree<n+1 := by
    have e := natDegree_derivative_le S
    omega
  have h := unitIntegral_by_parts (Q:=J) end0 end1
  rw [show J*S.derivative=S.derivative*J by ac_rfl,
    mappedLegendre_orthogonal _ _ der] at h
  have both : unitIntegral (J.derivative*S)=0 := neg_eq_zero.mp h.symm
  have raw := jacobiTwo_raw_ne (K:=K) n
  have nm : jacobiTwo K n=J.derivative*C J.derivative.leadingCoeff⁻¹ := by
    change normalize J.derivative=_
    rw [normalize_apply,coe_normUnit_of_ne_zero raw]
  rw [nm,show ((X:K[X])*(1-X))*(J.derivative*C J.derivative.leadingCoeff⁻¹)*Q =
    J.derivative.leadingCoeff⁻¹ • (J.derivative*S) by rw [smul_eq_C_mul]; dsimp [S]; ac_rfl,
    map_smul,both,smul_zero]

end
end RKCert.Paired
