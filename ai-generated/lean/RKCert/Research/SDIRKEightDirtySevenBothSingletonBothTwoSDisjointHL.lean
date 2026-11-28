import Mathlib.Tactic.Ring.Basic

/-!
Scalar gates for the unequal-law disjoint seven-clock chart.
The tableau ingress and exact polynomial/number-field census are independent.
-/
namespace RKCert.Research.SDIRKEightDirtySevenBothSingletonBothTwoSDisjointHL

theorem scale_determinant {R : Type*} [CommRing R]
    (M N U V lam : R) (h₁ : M * lam = N) (h₂ : U * lam = V) :
    U * N = M * V := by
  rw [← h₁, ← h₂]
  ring

theorem zero_front_slope_nonzero {R : Type*} [CommRing R]
    (H a b eta : R) (ha : a ≠ H)
    (h : a + b - 2 * H - eta * (H - b) = 0) :
    1 + eta ≠ 0 := by
  intro hzero
  have hr : a + b - 2 * H - eta * (H - b) =
      (1 + eta) * (b - H) + (a - H) := by ring
  rw [hzero, zero_mul, zero_add] at hr
  exact ha (sub_eq_zero.mp (hr.symm.trans h))

theorem quadratic_residual_identity {R : Type*} [CommRing R]
    (j k c₀ c₁ c₂ b : R) :
    k ^ 2 * (c₀ + c₁ * b + c₂ * b ^ 2) =
      (k * b + j) * (k * c₂ * b + k * c₁ - j * c₂) +
      (k ^ 2 * c₀ - k * j * c₁ + j ^ 2 * c₂) := by
  ring

theorem quadratic_residual_root {K : Type*} [Field K]
    (j k c₀ c₁ c₂ b : K)
    (hval : c₀ + c₁ * b + c₂ * b ^ 2 = 0)
    (hbase : k ^ 2 * c₀ - k * j * c₁ + j ^ 2 * c₂ = 0)
    (hlin : k * b + j ≠ 0) :
    k * c₂ * b + k * c₁ - j * c₂ = 0 := by
  have h := quadratic_residual_identity j k c₀ c₁ c₂ b
  rw [hval, hbase, mul_zero, add_zero] at h
  exact (mul_eq_zero.mp h.symm).resolve_left hlin

end RKCert.Research.SDIRKEightDirtySevenBothSingletonBothTwoSDisjointHL
