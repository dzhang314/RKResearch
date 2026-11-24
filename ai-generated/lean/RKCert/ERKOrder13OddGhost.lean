module
public import RKCert.ERKOrder13OddFactor
public import RKCert.PolynomialFeatureCapacity
public import Mathlib.FieldTheory.Separable

@[expose] public section
/-! # Literal scalar mesh/ghost certificates at order thirteen -/
namespace RKCert.Paired.FiniteMidpoint
open Polynomial
variable {K:Type*} [Field K] [CharZero K]
set_option maxHeartbeats 2000000

theorem odd5_as_poly : (odd5:K[X])=462*X^6 - 1260*X^5 + 1260*X^4 - 560*X^3 + 105*X^2 - 6*X := by
  apply @Polynomial.funext K _ _ (Infinite.of_injective (fun n:ℕ=>(n:K)) Nat.cast_injective)
  intro z
  classical
  rw [odd5,from11,ofFn_eq_sum_monomial,eval_finsetSum]
  norm_num [Fin.sum_univ_succ]
  ring

theorem oddSix_ghost_coprime : IsCoprime (oddSixPoly:K[X]) odd5 := by
  refine ⟨-(Polynomial.C ((19008:K)/13))*X^5 + (Polynomial.C ((42138:K)/13))*X^4 - (Polynomial.C ((31848:K)/13))*X^3 + (Polynomial.C ((9369:K)/13))*X^2 - (Polynomial.C ((4254:K)/65))*X + (Polynomial.C ((1:K)/7)),(Polynomial.C ((38016:K)/7))*X^5 - (Polynomial.C ((192060:K)/13))*X^4 + (Polynomial.C ((192720:K)/13))*X^3 - (Polynomial.C ((86868:K)/13))*X^2 + (Polynomial.C ((84312:K)/65))*X - (Polynomial.C ((5223:K)/65)),?_⟩
  apply @Polynomial.funext K _ _ (Infinite.of_injective (fun n:ℕ=>(n:K)) Nat.cast_injective)
  intro z
  rw [odd5_as_poly,oddSixPoly]
  simp only [eval_mul,eval_add,eval_sub,eval_neg,eval_pow,eval_X,eval_ofNat,eval_one,eval_C]
  ring

theorem oddSix_separable : (oddSixPoly:K[X]).Separable := by
  change IsCoprime _ (Polynomial.derivative _)
  refine ⟨-858*X^4 + (Polynomial.C ((8976:K)/5))*X^3 - (Polynomial.C ((6336:K)/5))*X^2 + (Polynomial.C ((2400:K)/7))*X - (Polynomial.C ((195:K)/7)),143*X^5 - (Polynomial.C ((1881:K)/5))*X^4 + (Polynomial.C ((715:K)/2))*X^3 - (Polynomial.C ((10321:K)/70))*X^2 + (Polynomial.C ((345:K)/14))*X - (Polynomial.C ((7:K)/6)),?_⟩
  have hd : Polynomial.derivative (oddSixPoly:K[X])=10296*X^5 - 27720*X^4 + 27720*X^3 - 12600*X^2 + 2520*X - 168 := by
    norm_num [oddSixPoly,Polynomial.derivative_sub,Polynomial.derivative_add,Polynomial.derivative_mul,
      Polynomial.derivative_X_pow,Polynomial.C_ofNat]
    ring
  apply @Polynomial.funext K _ _ (Infinite.of_injective (fun n:ℕ=>(n:K)) Nat.cast_injective)
  intro z
  rw [hd,oddSixPoly]
  simp only [eval_mul,eval_add,eval_sub,eval_neg,eval_pow,eval_X,eval_ofNat,eval_one,eval_C]
  ring

end RKCert.Paired.FiniteMidpoint
