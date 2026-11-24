module

public import RKCert.OrderedIntervalMoments

@[expose] public section

/-! # Positive exact beta moment over any ordered field -/
namespace RKCert.OrderedGram

open RKCert.Paired Polynomial

variable {K : Type*} [Field K]

/-- The formal unit-interval moment with the weight (x(1-x)). -/
noncomputable def betaIntegral : K[X] →ₗ[K] K where
  toFun P := (primitive ((X-X^2)*P)).eval 1
  map_add' P Q := by simp [mul_add,map_add,eval_add]
  map_smul' t P := by simp [eval_smul]

theorem betaIntegral_apply (P : K[X]) :
    betaIntegral P = (primitive ((X-X^2)*P)).eval 1 := rfl

theorem moment_reflect [CharZero K] (P : K[X]) :
    (primitive (P.comp (1-X))).eval 1=(primitive P).eval 1 := by
  have e := affine_substitution P 1 0
  have z : (primitive P).eval 0=0 := by rw [←coeff_zero_eq_eval_zero,primitive_coeff_zero]
  have a : C ((0:K)-1)*X+C 1=(1-X : K[X]) := by
    simp [sub_eq_add_neg,add_comm]
  rw [a,z] at e
  linear_combination e

/-- A nonzero square has strictly positive exact beta moment. The
split identity uses only the already-proved shifted Hilbert Gram. -/
theorem beta_square_pos [LinearOrder K] [IsStrictOrderedRing K]
    (P : K[X]) (hp : P≠0) : 0 < betaIntegral (P^2) := by
  let Y : K[X] := 1-X
  have hy : Y≠0 := by
    change (1-X:K[X])≠0
    rw [←neg_ne_zero,neg_sub]
    simpa only [C_1] using (X_sub_C_ne_zero (1:K))
  have yform : Y=C (-1:K)*X+C 1 := by simp [Y,sub_eq_add_neg,add_comm]
  have h1 := pow_square_pos 1 (Y*P) (mul_ne_zero hy hp)
  have ref_ne : (X*P).comp Y≠0 := by
    rw [yform]
    exact affine_comp_ne_zero (mul_ne_zero X_ne_zero hp) 1 (-1:K) (by simp)
  have h2 := pow_square_pos 1 ((X*P).comp Y) ref_ne
  have reflect_product : (Y*(X*P)^2).comp Y=X*((X*P).comp Y)^2 := by
    simp [Y,mul_comp,pow_comp,sub_comp]
  have ref_value := moment_reflect (Y*(X*P)^2)
  change (primitive ((Y*(X*P)^2).comp Y)).eval 1=(primitive (Y*(X*P)^2)).eval 1
    at ref_value
  rw [reflect_product] at ref_value
  simp only [pow_one] at h1 h2
  rw [ref_value] at h2
  have splitting : (X-X^2)*P^2=X*(Y*P)^2+Y*(X*P)^2 := by dsimp [Y]; ring
  rw [betaIntegral_apply,splitting,map_add,eval_add]
  exact add_pos h1 h2

end RKCert.OrderedGram
