module

public import Mathlib.LinearAlgebra.FiniteDimensional.Lemmas
import Lean.Elab.Tactic.Omega

@[expose] public section

namespace RKCert.ReviewedNative

open Module

/-- At exact row-span saturation, a vanishing multiplier and an invertible
comparison map pay the same number of restricted support coordinates.
The inputs are the two actual maps into the same saturated row space:
the first is supported off the named sites, and the second is injective
on the kernel of the first after restriction. -/
theorem twoSidedSupportRank {K V Z U : Type*} [Field K]
    [AddCommGroup V] [Module K V] [FiniteDimensional K V]
    [AddCommGroup Z] [Module K Z] [FiniteDimensional K Z]
    [AddCommGroup U] [Module K U]
    (f : V →ₗ[K] Z) (e : V ≃ₗ[K] Z) (r : Z →ₗ[K] U)
    (hquiet : r.comp f = 0)
    (hguard : Function.Injective ((r.comp e.toLinearMap).comp f.ker.subtype)) :
    finrank K f.ker = finrank K r.range := by
  have hsub : f.range ≤ r.ker := by
    rintro _ ⟨x,rfl⟩
    exact LinearMap.congr_fun hquiet x
  have h₁ := Submodule.finrank_mono hsub
  have hf := f.finrank_range_add_finrank_ker
  have hr := r.finrank_range_add_finrank_ker
  have he := e.finrank_eq
  let m := (r.comp e.toLinearMap).comp f.ker.subtype
  have hrange : m.range ≤ r.range := by
    rintro _ ⟨x,rfl⟩
    exact ⟨e (x : V),rfl⟩
  have h₂ := Submodule.finrank_mono hrange
  rw [LinearMap.finrank_range_of_inj hguard] at h₂
  omega

end RKCert.ReviewedNative
