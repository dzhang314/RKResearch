module

public import RKCert.ReviewedNative.PolynomialCertificateBox
public import Mathlib.Algebra.Polynomial.AlgebraMap

import Mathlib.Tactic.Ring

@[expose] public section

namespace RKCert.ReviewedNative.PolynomialCertificate

open Polynomial
open scoped BigOperators Polynomial

variable {K : Type*} [Field K]

/-- Any one-variable affine pencil in each factor is allowed; its slope
may itself be a polynomial and may depend on the label. -/
theorem separatelyAffine_polynomial_pencil {m : ℕ} (L : K[X] →ₗ[K] K)
    (body : K[X]) (g h : Fin m → K[X]) :
    SeparatelyAffine (fun r => L (body * ∏ i, (g i + C (r i) * h i))) := by
  apply separatelyAffine_linearMap_product L body (fun i y => g i + C y * h i)
  intro i a b t
  simp only [Polynomial.smul_eq_C_mul, mix, map_add, map_sub, map_mul, map_one]
  ring

/-- Includes the compactified factors (1-w)Y-w. The role of this lemma
is separate affinity, independent of any parameter table or order condition. -/
theorem separatelyAffine_normalized_linear_factors {m : ℕ} (L : K[X] →ₗ[K] K)
    (body : K[X]) (Y : Fin m → K[X]) :
    SeparatelyAffine (fun r => L (body * ∏ i, (C (1 - r i) * Y i - C (r i)))) := by
  apply separatelyAffine_linearMap_product L body (fun i w => C (1 - w) * Y i - C w)
  intro i a b t
  simp only [Polynomial.smul_eq_C_mul, mix, map_add, map_sub, map_mul, map_one]
  ring

end RKCert.ReviewedNative.PolynomialCertificate
