module

public import Mathlib.Algebra.Polynomial.RingDivision
public import Mathlib.LinearAlgebra.Pi
public import RKCert.ReviewedNative.ScalarCokernelCancellation

public section

/-! # A monic scalar composite splits over the coefficient ring

The quotient map `Polynomial.divByMonicHom g` is linear over the
coefficient ring `R`, not in general over `R[X]`. No field, rank, degree
positivity, or primitivity assumption is used: the projection must be
monic. A finite free module gives the coordinate equivalence below.
-/

namespace RKCert.ReviewedNative

open Polynomial

section PolynomialCoordinates

variable {R M ι : Type*} [CommRing R] [AddCommGroup M]
    [Module R M] [Module R[X] M] [IsScalarTower R R[X] M]

/-- In polynomial coordinates, `W ∘ V = g • id` with monic `g`
exhibits an `R`-linear left inverse of `V`. In general this inverse is
not `R[X]`-linear. -/
theorem exists_linear_leftInverse_of_monic_scalar_comp
    (e : M ≃ₗ[R[X]] (ι → R[X])) {g : R[X]} (hg : g.Monic)
    (V W : M →ₗ[R] M) (hwv : ∀ x, W (V x) = g • x) :
    ∃ L : M →ₗ[R] M, Function.LeftInverse L V := by
  let eR := e.restrictScalars R
  let d := (Polynomial.divByMonicHom g).compLeft ι
  refine ⟨eR.symm.toLinearMap.comp (d.comp (eR.toLinearMap.comp W)), ?_⟩
  intro x
  change e.symm (fun i => (e (W (V x)) i) /ₘ g) = x
  apply e.injective
  rw [e.apply_symm_apply, hwv x, e.map_smul]
  funext i
  exact Polynomial.mul_divByMonic_cancel_left (e x i) hg

/-- A coefficient regular on `R` is regular on the coordinate module,
even if the coefficient is a zero divisor after a later specialization. -/
theorem isSMulRegular_of_polynomial_coordinates
    (e : M ≃ₗ[R[X]] (ι → R[X])) {a : R} (ha : IsSMulRegular R a) :
    IsSMulRegular M a := by
  let eR := e.restrictScalars R
  intro x y h
  apply eR.injective
  have he : a • eR x = a • eR y := by
    simpa only [map_smul] using congrArg eR h
  exact funext (fun i => ha.polynomial (congrFun he i))

end PolynomialCoordinates

/-- A split `R`-linear injection reflects divisibility by every scalar,
including scalars that are not regular. -/
theorem smul_range_reflected_of_linear_leftInverse
    {R M N : Type*} [Semiring R] [AddCommMonoid M] [AddCommMonoid N]
    [Module R M] [Module R N] (V : M →ₗ[R] N) (L : N →ₗ[R] M)
    (hL : Function.LeftInverse L V) (a : R) (y : M)
    (hy : V y ∈ Set.range ((a • ·) : N → N)) :
    y ∈ Set.range ((a • ·) : M → M) := by
  obtain ⟨z, hz⟩ := hy
  exact ⟨L z, (L.map_smul a z).symm.trans ((congrArg L hz).trans (hL y))⟩

/-- A coefficient regular on the base remains regular on the coefficient-
module cokernel of a map with a monic scalar composite. -/
theorem isSMulRegular_cokernel_of_monic_scalar_comp
    {R M ι : Type*} [CommRing R] [AddCommGroup M]
    [Module R M] [Module R[X] M] [IsScalarTower R R[X] M]
    (e : M ≃ₗ[R[X]] (ι → R[X])) {g : R[X]} (hg : g.Monic)
    (V W : M →ₗ[R] M) (hwv : ∀ x, W (V x) = g • x)
    {a : R} (ha : IsSMulRegular R a) :
    IsSMulRegular (M ⧸ V.range) a := by
  obtain ⟨L, hL⟩ := exists_linear_leftInverse_of_monic_scalar_comp e hg V W hwv
  exact isSMulRegular_quotient_range V (isSMulRegular_of_polynomial_coordinates e ha)
    (smul_range_reflected_of_linear_leftInverse V L hL a)

end RKCert.ReviewedNative
