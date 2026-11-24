module
public import RKCert.OrderTwelveFactors
public import Mathlib.Algebra.Polynomial.Eval.Degree
public import Mathlib.Tactic.ComputeDegree
public import Mathlib.Tactic.FieldSimp

@[expose] public section
/-! # Direct polynomial-divisor formulation of the p12 pure endpoint gate -/
namespace RKCert.OrderTwelve
open Polynomial
variable {K : Type*} [Field K] [CharZero K]

/-- The specific integer-scaled shifted Legendre derivative of degree five. -/
noncomputable def dFivePoly : K[X] := 132*X^5-330*X^4+300*X^3-120*X^2+20*X-1

omit [CharZero K] in
@[simp] theorem eval_dFivePoly (x : K) : (dFivePoly : K[X]).eval x=dFive x := by
  simp [dFivePoly,dFive]

theorem natDegree_dFivePoly : (dFivePoly : K[X]).natDegree=5 := by
  unfold dFivePoly
  compute_degree!

/-- The coefficient formula for the formal integral of X·P, valid here because
the divisor has degree at most four. -/
def purePolynomialMoment (P : K[X]) (w : K) : K :=
  pureMoment (P.coeff 0) (P.coeff 1) (P.coeff 2) (P.coeff 3) (P.coeff 4) w

omit [CharZero K] in
theorem evalFour_of_small (P : K[X]) (hp : P.natDegree≤4) (x : K) :
    P.eval x=evalFour (P.coeff 0) (P.coeff 1) (P.coeff 2) (P.coeff 3) (P.coeff 4) x := by
  rw [Polynomial.eval_eq_sum_range' (n:=5) (by omega)]
  simp [evalFour,Finset.sum_range_succ]

/-- The 40 Appendix B pure-factor tests, without supplying any complementary
factors, root list, splitting-field embedding, or normalization of P. -/
theorem pure_divisor_moment_ne_zero (P : K[X]) (hdiv : P∣dFivePoly) (w : K)
    (hdeg : P.natDegree=3 ∨ P.natDegree=4)
    (hw : w=1 ∨ dFive w=0 ∧ P.eval w≠0) : purePolynomialMoment P w≠0 := by
  obtain ⟨T,hfit⟩ := hdiv
  have hD : (dFivePoly:K[X])≠0 := by
    intro h
    have e := congrArg (fun P:K[X] => P.eval 0) h
    simp [dFive] at e
  have hP : P≠0 := fun h => hD (by simp [hfit,h])
  have hT : T≠0 := fun h => hD (by simp [hfit,h])
  have hd := natDegree_dFivePoly (K:=K)
  rw [hfit,natDegree_mul hP hT] at hd
  let L := T.leadingCoeff
  have hL : L≠0 := leadingCoeff_ne_zero.mpr hT
  have hsmall : P.natDegree≤4 := by omega
  have raw (x:K) : dFive x=T.eval x*P.eval x := by
    rw [←eval_dFivePoly,hfit,eval_mul,mul_comm]
  have scale (x : K) :
      evalFour (L*P.coeff 0) (L*P.coeff 1) (L*P.coeff 2) (L*P.coeff 3) (L*P.coeff 4) x =
      L*P.eval x := by rw [evalFour_of_small P hsmall x]; unfold evalFour; ring
  have sW : w=1 ∨ dFive w=0 ∧
      evalFour (L*P.coeff 0) (L*P.coeff 1) (L*P.coeff 2) (L*P.coeff 3) (L*P.coeff 4) w≠0 := by
    rw [scale]
    exact hw.imp id (fun h => ⟨h.1,mul_ne_zero hL h.2⟩)
  intro hm
  have sM : pureMoment (L*P.coeff 0) (L*P.coeff 1) (L*P.coeff 2) (L*P.coeff 3)
      (L*P.coeff 4) w=0 := by
    unfold purePolynomialMoment pureMoment at hm
    unfold pureMoment
    linear_combination L*hm
  rcases hdeg with h3|h4
  · have ht : T.natDegree=2 := by omega
    have h4z : P.coeff 4=0 := coeff_eq_zero_of_natDegree_lt (by omega)
    rw [h4z,mul_zero] at scale sW sM
    apply cubic_off_factor (-(T.coeff 1)/L) (T.coeff 0/L) w _ _ _ _ _ sW sM
    intro x
    rw [scale,raw,Polynomial.eval_eq_sum_range' (p:=T) (n:=3) (by omega)]
    have hlead : T.coeff 2=L := by rw [←ht]; rfl
    simp only [Finset.sum_range_succ,Finset.range_zero,Finset.sum_empty,pow_zero,pow_one,
      mul_one,zero_add,hlead]
    field_simp
    ring
  · have ht : T.natDegree=1 := by omega
    apply quartic_off_factor (-(T.coeff 0)/L) w _ _ _ _ _ _ sW sM
    intro x
    rw [scale,raw,Polynomial.eval_eq_sum_range' (p:=T) (n:=2) (by omega)]
    have hlead : T.coeff 1=L := by rw [←ht]; rfl
    simp only [Finset.sum_range_succ,Finset.range_zero,Finset.sum_empty,pow_zero,pow_one,
      mul_one,zero_add,hlead]
    field_simp
    ring

end RKCert.OrderTwelve
