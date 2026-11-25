module

public import RKCert.ReviewedNative.NativePrimitiveMoments
public import RKCert.ReviewedNative.NativePrimitiveRootTransport
public import RKCert.ReviewedNative.WeightXEightIrreducible

import Mathlib.Tactic.FinCases
import Mathlib.Tactic.NormNum
import Mathlib.Tactic.Ring
import Lean.Elab.Tactic.Omega

@[expose] public section

/-! # Recognize the first-Radau polynomial from the literal eight moments

No stage/order theorem occurs in the statements here. The only fixed scalar
calculations are the eight linear Rodrigues moment identities. The candidate
is independent of the proof of nonvanishing at a selected algebraic root.
-/
namespace RKCert.ReviewedNative.WeightXEight
open Polynomial
open RKResearch.Certified.Graded RKResearch.Certified.Graded.NativeMoments
open RKResearch.Certified.Graded.NativeRootTransport
open scoped BigOperators

noncomputable section

private theorem unnormalized_rat_moment (i : Fin 8) :
    (primitive ((X:ℚ[X])^i.val *
      (X * integralPolynomial.map (Int.castRingHom ℚ)))).eval 1=0 := by
  let a : Fin 9 → ℚ := fun j => (coefficients j : ℚ)
  have rep : integralPolynomial.map (Int.castRingHom ℚ)=ofFn 9 a := by
    simp only [integralPolynomial,ofFn_eq_sum_monomial,Polynomial.map_sum,
      Polynomial.map_monomial,a]
    rfl
  rw [rep,show (X:ℚ[X])*ofFn 9 a=X^1*ofFn 9 a by rw [pow_one]]
  have m (i : Fin 8) :
      (primitive ((X:ℚ[X])^i.val*(X^1*ofFn 9 a))).eval 1 =
      ∑ j : Fin 9, a j/((i.val+j.val+2:ℕ):ℚ) := by
    rw [←mul_assoc,←pow_add,ofFn_eq_sum_monomial,Finset.mul_sum,map_sum,eval_finsetSum]
    apply Finset.sum_congr rfl
    intro j _
    rw [X_pow_mul_monomial,primitive_monomial,eval_monomial,one_pow,mul_one]
    congr 2
    omega
  rw [m]
  fin_cases i <;> norm_num [a,coefficients,Fin.sum_univ_succ]

theorem rational_moment (i : Fin 8) :
    (primitive ((X:ℚ[X])^i.val*(X*rationalPolynomial))).eval 1=0 := by
  have eq : (X:ℚ[X])^i.val*(X*rationalPolynomial) =
      (24310:ℚ)⁻¹ • ((X:ℚ[X])^i.val*(X*integralPolynomial.map (Int.castRingHom ℚ))) := by
    rw [rationalPolynomial,smul_eq_C_mul]
    ring
  change (Polynomial.leval (1:ℚ)) (primitive (X^i.val*(X*rationalPolynomial)))=0
  rw [eq,map_smul,map_smul,
    show (Polynomial.leval (1:ℚ)) (primitive (X^i.val*
      (X*integralPolynomial.map (Int.castRingHom ℚ))))=0 from unnormalized_rat_moment i,
    smul_zero]

theorem mapped_moment {K : Type*} [Field K] [CharZero K] (i : Fin 8) :
    (primitive ((X:K[X])^i.val *
       (X*rationalPolynomial.map (algebraMap ℚ K)))).eval 1=0 := by
  let f := algebraMap ℚ K
  have z : ((primitive ((X:ℚ[X])^i.val*(X*rationalPolynomial))).map f).eval (f 1)=0 := by
    rw [eval_map_apply,rational_moment,map_zero]
  simpa only [f,primitive_map,Polynomial.map_mul,Polynomial.map_pow,Polynomial.map_X,map_one]
    using z

/-- Recognition by the already checked Cauchy kernel, not by a new solve. -/
theorem recognise_product {K : Type*} [Field K] [CharZero K]
    {D : K[X]} (dn : D≠0) (dD : D.natDegree≤8)
    (test : ∀ i : Fin 8, (primitive ((X:K[X])^i.val*(X*D))).eval 1=0) :
    D.natDegree=8 ∧ D=C D.leadingCoeff * rationalPolynomial.map (algebraMap ℚ K) := by
  let H := rationalPolynomial.map (algebraMap ℚ K)
  have hm : H.Monic := rational_monic.map _
  have hD : H.natDegree=8 := by
    rw [show H=rationalPolynomial.map (algebraMap ℚ K) from rfl,
      natDegree_map_eq_of_injective (algebraMap ℚ K).injective,rational_degree]
  have d8 : D.natDegree=8 := by
    by_contra ne
    exact dn (x_moments_detect (n:=7) (show D.natDegree≤7 by omega) test)
  let T := D-C D.leadingCoeff*H
  have leadD : D.leadingCoeff≠0 := leadingCoeff_ne_zero.mpr dn
  have t8 : T.natDegree≤8 := by
    change (D-C D.leadingCoeff*H).natDegree≤8
    exact natDegree_sub_le_of_le dD (by rw [natDegree_C_mul leadD,hD])
  have h8 : H.coeff 8=1 := by rw [←hD,coeff_natDegree,hm.leadingCoeff]
  have dc : D.coeff 8=D.leadingCoeff := by rw [←d8,coeff_natDegree]
  have t7 : T.natDegree≤7 := by
    rw [natDegree_le_iff_coeff_eq_zero]
    intro n big
    by_cases e : n=8
    · subst n
      simp only [T,coeff_sub,coeff_C_mul,h8,mul_one,dc,sub_self]
    · exact coeff_eq_zero_of_natDegree_lt (t8.trans_lt (by omega))
  have tests (i : Fin 8) : (primitive ((X:K[X])^i.val*(X*T))).eval 1=0 := by
    have eq : (X:K[X])^i.val*(X*T) =
        X^i.val*(X*D)-D.leadingCoeff • (X^i.val*(X*H)) := by
      dsimp only [T]
      rw [smul_eq_C_mul]
      ring
    change (Polynomial.leval (1:K)) (primitive ((X:K[X])^i.val*(X*T)))=0
    rw [eq,map_sub,map_smul,map_sub,map_smul,
      show (Polynomial.leval (1:K)) (primitive ((X:K[X])^i.val*(X*D)))=0 from test i,
      show (Polynomial.leval (1:K)) (primitive ((X:K[X])^i.val*(X*H)))=0 from mapped_moment i,
      smul_zero,sub_zero]
  exact ⟨d8,sub_eq_zero.mp (x_moments_detect (n:=7) t7 tests)⟩

/-- With the native test budgets, a supposed first zero yields a monic
five-by-three factor window without altering its first clock or primitive. -/
theorem monic_window_of_first_zero {K : Type*} [Field K] [CharZero K]
    {Q N : K[X]} {u : K} (qn : Q≠0) (qd : Q.natDegree≤5)
    (nn : N≠0) (nd : N.natDegree=3) (root : N.eval u=0)
    (test : ∀ i : Fin 8, (primitive ((X:K[X])^i.val*(X*(Q*N)))).eval 1=0)
    (zero : (primitive (X*Q)).eval u=0) :
    ∃ Q' N' : K[X], Q'.Monic ∧ N'.Monic ∧ Q'.natDegree=5 ∧ N'.natDegree=3 ∧
      Q'*N'=rationalPolynomial.map (algebraMap ℚ K) ∧ N'.IsRoot u ∧
        (primitive (X*Q')).eval u=0 := by
  let H := rationalPolynomial.map (algebraMap ℚ K)
  have product : (Q*N).natDegree≤8 := by rw [natDegree_mul qn nn,nd]; omega
  obtain ⟨deg,id⟩ := recognise_product (mul_ne_zero qn nn) product test
  have q5 : Q.natDegree=5 := by rw [natDegree_mul qn nn,nd] at deg; omega
  have ql : Q.leadingCoeff≠0 := leadingCoeff_ne_zero.mpr qn
  have nl : N.leadingCoeff≠0 := leadingCoeff_ne_zero.mpr nn
  let Q' := C Q.leadingCoeff⁻¹ * Q
  let N' := C N.leadingCoeff⁻¹ * N
  have qm : Q'.Monic := by
    change (C Q.leadingCoeff⁻¹ * Q).leadingCoeff=1
    rw [leadingCoeff_mul,leadingCoeff_C,inv_mul_cancel₀ ql]
  have nm : N'.Monic := by
    change (C N.leadingCoeff⁻¹ * N).leadingCoeff=1
    rw [leadingCoeff_mul,leadingCoeff_C,inv_mul_cancel₀ nl]
  refine ⟨Q',N',qm,nm,?_,?_,?_,?_,?_⟩
  · rw [show Q'=C Q.leadingCoeff⁻¹*Q from rfl,natDegree_C_mul (inv_ne_zero ql),q5]
  · rw [show N'=C N.leadingCoeff⁻¹*N from rfl,natDegree_C_mul (inv_ne_zero nl),nd]
  · calc
      Q'*N' = C (Q.leadingCoeff⁻¹*N.leadingCoeff⁻¹)*(Q*N) := by
        dsimp only [Q',N']
        rw [C_mul]
        ring
      _ = H := by
        have e : (Q.leadingCoeff⁻¹*N.leadingCoeff⁻¹)*(Q*N).leadingCoeff=1 := by
          rw [leadingCoeff_mul]
          calc
            _=(Q.leadingCoeff⁻¹*Q.leadingCoeff)*(N.leadingCoeff⁻¹*N.leadingCoeff) := by ring
            _=1 := by rw [inv_mul_cancel₀ ql,inv_mul_cancel₀ nl,mul_one]
        calc
          _ = C (Q.leadingCoeff⁻¹*N.leadingCoeff⁻¹)*(C (Q*N).leadingCoeff*H) :=
            congrArg (fun P : K[X] => C (Q.leadingCoeff⁻¹*N.leadingCoeff⁻¹)*P) id
          _ = H := by rw [←mul_assoc,←C_mul,e,C_1,one_mul]
  · change (C N.leadingCoeff⁻¹*N).eval u=0
    rw [eval_mul,root,mul_zero]
  · have eq : X*Q'=Q.leadingCoeff⁻¹ • (X*Q) := by
      dsimp only [Q']
      rw [smul_eq_C_mul]
      ring
    change (Polynomial.leval u) (primitive (X*Q'))=0
    rw [eq,map_smul,map_smul,show (Polynomial.leval u) (primitive (X*Q))=0 from zero,smul_zero]

end
end RKCert.ReviewedNative.WeightXEight
