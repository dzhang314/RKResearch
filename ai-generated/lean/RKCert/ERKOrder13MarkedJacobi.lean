module
public import RKCert.ERKOrder13Packets
public import RKCert.ERKOrderedQ7Factor
public import Mathlib.FieldTheory.Separable

@[expose] public section
/-! # Exact fixed Jacobi identities for the marked order-thirteen mesh -/
namespace RKCert.Paired.FiniteMidpoint
open Polynomial RKCert.OrderTwelve
variable {K:Type*} [Field K] [CharZero K]
set_option maxHeartbeats 2000000

noncomputable def markD3 : K[X] := 14*X^3 - 21*X^2 + 9*X - 1
noncomputable def markD4 : K[X] := 42*X^4 - 84*X^3 + 56*X^2 - 14*X + 1

theorem markD3_degree : (markD3:K[X]).natDegree=3 := by
  unfold markD3
  compute_degree!
theorem markD4_degree : (markD4:K[X]).natDegree=4 := by
  unfold markD4
  compute_degree!

theorem mark_d3_d4_coprime : IsCoprime (markD3:K[X]) markD4 := by
  refine ⟨420*X^3 - 630*X^2 + 266*X - 28,-140*X^2 + 140*X - 27,?_⟩
  apply @Polynomial.funext K _ _ (Infinite.of_injective (fun n:ℕ=>(n:K)) Nat.cast_injective)
  intro x
  simp only [markD3,markD4,eval_mul,eval_add,eval_sub,eval_neg,eval_pow,eval_X,eval_ofNat,eval_one,eval_C]
  ring

theorem mark_d5_separable : (dFivePoly:K[X]).Separable := by
  change IsCoprime _ (Polynomial.derivative _)
  refine ⟨-924*X^3 + 1386*X^2 - 600*X + 69,(C ((924:K)/5))*X^4 - (C ((1848:K)/5))*X^3 + (C ((1209:K)/5))*X^2 - 57*X + (C ((7:K)/2)),?_⟩
  have eq : Polynomial.derivative (dFivePoly:K[X])=660*X^4 - 1320*X^3 + 900*X^2 - 240*X + 20 := by
    norm_num [dFivePoly,Polynomial.derivative_sub,Polynomial.derivative_add,Polynomial.derivative_mul,
      Polynomial.derivative_X_pow,Polynomial.C_ofNat]
    ring
  rw [eq]
  apply @Polynomial.funext K _ _ (Infinite.of_injective (fun n:ℕ=>(n:K)) Nat.cast_injective)
  intro x
  simp only [dFivePoly,eval_mul,eval_add,eval_sub,eval_neg,eval_pow,eval_X,eval_ofNat,eval_one,eval_C]
  ring

theorem mark_d5_recurrence :
    (dFivePoly:K[X])=C (-(4:K)/7)*markD3+(C ((22:K)/7)*(X-C ((1:K)/2)))*markD4 := by
  apply @Polynomial.funext K _ _ (Infinite.of_injective (fun n:ℕ=>(n:K)) Nat.cast_injective)
  intro x
  simp only [dFivePoly,markD3,markD4,eval_mul,eval_add,eval_sub,eval_neg,eval_pow,eval_X,eval_ofNat,eval_one,eval_C]
  ring

theorem mark_d6_recurrence :
    (dSixPoly:K[X])=C (-(5:K)/8)*markD4+(C ((13:K)/4)*(X-C ((1:K)/2)))*dFivePoly := by
  apply @Polynomial.funext K _ _ (Infinite.of_injective (fun n:ℕ=>(n:K)) Nat.cast_injective)
  intro x
  simp only [dFivePoly,dSixPoly,markD4,eval_mul,eval_add,eval_sub,eval_neg,eval_pow,eval_X,eval_ofNat,eval_one,eval_C]
  ring

theorem dx3_mark_factor : (dx3:K[X])=(20:K) • (X*markD3) := by
  apply @Polynomial.funext K _ _ (Infinite.of_injective (fun n:ℕ=>(n:K)) Nat.cast_injective)
  intro x
  classical
  rw [dx3,from11,ofFn_eq_sum_monomial,eval_finsetSum]
  norm_num [Fin.sum_univ_succ,eval_smul,markD3]
  ring

theorem dx4_mark_factor : (dx4:K[X])=(30:K) • (X*markD4) := by
  apply @Polynomial.funext K _ _ (Infinite.of_injective (fun n:ℕ=>(n:K)) Nat.cast_injective)
  intro x
  classical
  rw [dx4,from11,ofFn_eq_sum_monomial,eval_finsetSum]
  norm_num [Fin.sum_univ_succ,eval_smul,markD4]
  ring

theorem dx5_mark_factor : (dx5:K[X])=(42:K) • (X*dFivePoly) := by
  apply @Polynomial.funext K _ _ (Infinite.of_injective (fun n:ℕ=>(n:K)) Nat.cast_injective)
  intro x
  classical
  rw [dx5,from11,ofFn_eq_sum_monomial,eval_finsetSum]
  norm_num [Fin.sum_univ_succ,eval_smul,dFive]
  ring

end RKCert.Paired.FiniteMidpoint
