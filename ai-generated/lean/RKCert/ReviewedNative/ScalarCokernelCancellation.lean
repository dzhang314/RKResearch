module

public import Mathlib.Algebra.Module.Submodule.Range
public import Mathlib.Algebra.Regular.SMul
public import Mathlib.LinearAlgebra.Quotient.Defs

public section

/-! # Scalar cancellation through a cokernel

The range formulation uses no quotient structure or commutativity of the
scalar semiring. For modules over a ring, it gives regularity of the scalar
on the quotient by the linear range.

Pinned interfaces: Lean v4.36.0, Mathlib fc4f59e577feb1a4956671bc04ac18aaaf8cd842.
-/

namespace RKCert.ReviewedNative

/-- If the image of an element is divisible by a scalar only when the
element itself is divisible, then the linear range is saturated for that
scalar, provided the scalar acts injectively on the codomain. -/
theorem mem_range_of_smul_mem_range {R M N : Type*}
    [Semiring R] [AddCommMonoid M] [AddCommMonoid N] [Module R M] [Module R N]
    (V : M →ₗ[R] N) {a : R} (ha : IsSMulRegular N a)
    (hmod : ∀ x : M, V x ∈ Set.range ((a • ·) : N → N) →
      x ∈ Set.range ((a • ·) : M → M))
    {x : N} (hx : a • x ∈ V.range) : x ∈ V.range := by
  obtain ⟨y, hy⟩ := LinearMap.mem_range.mp hx
  obtain ⟨z, hz⟩ := hmod y ⟨x, hy.symm⟩
  refine LinearMap.mem_range.mpr ⟨z, ha ?_⟩
  calc
    a • V z = V (a • z) := (V.map_smul a z).symm
    _ = V y := congrArg V hz
    _ = a • x := hy

/-- Scalar regularity descends to the cokernel of a linear map that is
injective modulo the scalar. Scalar multiples are written as set ranges
so the scalar need not be central. -/
theorem isSMulRegular_quotient_range {R M N : Type*}
    [Ring R] [AddCommGroup M] [AddCommGroup N] [Module R M] [Module R N]
    (V : M →ₗ[R] N) {a : R} (ha : IsSMulRegular N a)
    (hmod : ∀ x : M, V x ∈ Set.range ((a • ·) : N → N) →
      x ∈ Set.range ((a • ·) : M → M)) :
    IsSMulRegular (N ⧸ V.range) a := by
  intro u v h
  obtain ⟨x, rfl⟩ := V.range.mkQ_surjective u
  obtain ⟨y, rfl⟩ := V.range.mkQ_surjective v
  have hmk : (Submodule.Quotient.mk (a • x) : N ⧸ V.range) =
      Submodule.Quotient.mk (a • y) := by
    simpa only [Submodule.mkQ_apply, Submodule.Quotient.mk_smul] using h
  have hd : a • (x - y) ∈ V.range := by
    simpa only [smul_sub] using (Submodule.Quotient.eq V.range).mp hmk
  simpa only [Submodule.mkQ_apply] using
    (Submodule.Quotient.eq V.range).mpr (mem_range_of_smul_mem_range V ha hmod hd)

end RKCert.ReviewedNative
