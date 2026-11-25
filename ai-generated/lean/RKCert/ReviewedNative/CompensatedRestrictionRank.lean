module

public import Mathlib.LinearAlgebra.FiniteDimensional.Lemmas

@[expose] public section

/-! # Exact compensated restriction rank
A scalar mass functional and one direction give the update v ↦ v − f(v) • a.
The exceptional coefficient is detected by f(a) = 1. This module is independent
of tableaux, coordinates on any particular tableau, and ordered-field positivity. -/
namespace RKCert.ReviewedNative.CompensatedRestrictionRank

open Module
open scoped BigOperators

noncomputable section

variable {K : Type*} [Field K]

section RankOne

variable {V : Type*} [AddCommGroup V] [Module K V]
variable (f : V →ₗ[K] K) (a : V)

/-- Identity minus the rank-one map with functional f and direction a. -/
def subtractMass : V →ₗ[K] V :=
  LinearMap.id - f.smulRight a

@[simp] theorem subtractMass_apply (v : V) :
    subtractMass f a v = v - f v • a := rfl

theorem ker_eq_bot_of_eval_ne_one (h : f a ≠ 1) :
    LinearMap.ker (subtractMass f a) = ⊥ := by
  refine le_antisymm ?_ bot_le
  intro v hv
  rw [LinearMap.mem_ker, subtractMass_apply, sub_eq_zero] at hv
  have e : f v = f v * f a := by
    calc
      f v = f (f v • a) := congrArg (fun w : V => f w) hv
      _ = f v * f a := by rw [map_smul, smul_eq_mul]
  have z : f v * (1 - f a) = 0 := by
    rw [mul_sub, mul_one, ← e, sub_self]
  have nz : 1 - f a ≠ 0 := by
    intro he
    exact h (sub_eq_zero.mp he).symm
  have fv : f v = 0 := (mul_eq_zero.mp z).resolve_right nz
  rw [fv, zero_smul] at hv
  exact (Submodule.mem_bot K).mpr hv

theorem ker_eq_span_of_eval_eq_one (h : f a = 1) :
    LinearMap.ker (subtractMass f a) = K ∙ a := by
  ext v
  rw [LinearMap.mem_ker, subtractMass_apply, sub_eq_zero, Submodule.mem_span_singleton]
  constructor
  · intro hv
    exact ⟨f v, hv.symm⟩
  · rintro ⟨k, hk⟩
    rw [← hk, map_smul, smul_eq_mul, h, mul_one]

theorem finrank_range_of_eval_ne_one [FiniteDimensional K V] (h : f a ≠ 1) :
    finrank K (LinearMap.range (subtractMass f a)) = finrank K V := by
  have e := (subtractMass f a).finrank_range_add_finrank_ker
  rwa [ker_eq_bot_of_eval_ne_one f a h, finrank_bot, add_zero] at e

/-- Additive form of rank = dim V − 1, avoiding truncated subtraction. -/
theorem finrank_range_add_one_of_eval_eq_one [FiniteDimensional K V] (h : f a = 1) :
    finrank K (LinearMap.range (subtractMass f a)) + 1 = finrank K V := by
  have na : a ≠ 0 := by
    intro hz
    have e := h
    rw [hz, map_zero] at e
    exact zero_ne_one e
  have e := (subtractMass f a).finrank_range_add_finrank_ker
  rwa [ker_eq_span_of_eval_eq_one f a h, finrank_span_singleton (K := K) na] at e

end RankOne

section Coordinates

variable {ι : Type*} [Fintype ι]

/-- Signed mass on a finite original index set; repetitions in any external label
have no bearing on this functional. -/
def coordinateMass (b : ι → K) : (ι → K) →ₗ[K] K :=
  ∑ i, b i • (LinearMap.proj i : (ι → K) →ₗ[K] K)

@[simp] theorem coordinateMass_apply (b v : ι → K) :
    coordinateMass b v = ∑ i, b i * v i := by
  simp only [coordinateMass, LinearMap.sum_apply, LinearMap.smul_apply,
    LinearMap.proj_apply, smul_eq_mul]

theorem coordinateMass_scale_one (b : ι → K) (κ : K) :
    coordinateMass b (κ • (1 : ι → K)) = κ * ∑ i, b i := by
  rw [map_smul, smul_eq_mul, coordinateMass_apply]
  simp only [Pi.one_apply, mul_one]

/-- Subtract a common multiple of the total signed mass at every coordinate. -/
def coordinateUpdate (b : ι → K) (κ : K) : (ι → K) →ₗ[K] (ι → K) :=
  subtractMass (coordinateMass b) (κ • (1 : ι → K))

@[simp] theorem coordinateUpdate_apply (b v : ι → K) (κ : K) (i : ι) :
    coordinateUpdate b κ v i = v i - κ * ∑ j, b j * v j := by
  change (v - coordinateMass b v • (κ • (1 : ι → K))) i = _
  simp only [Pi.sub_apply, Pi.smul_apply, Pi.one_apply, coordinateMass_apply, smul_eq_mul,
    mul_one]
  rw [mul_comm (∑ j, b j * v j) κ]

theorem coordinate_finrank_of_ne_one (b : ι → K) (κ : K)
    (h : κ * (∑ i, b i) ≠ 1) :
    finrank K (LinearMap.range (coordinateUpdate b κ)) = Fintype.card ι := by
  have h' : coordinateMass b (κ • (1 : ι → K)) ≠ 1 := by
    simpa only [coordinateMass_scale_one] using h
  calc
    _ = finrank K (ι → K) :=
      finrank_range_of_eval_ne_one (coordinateMass b) (κ • (1 : ι → K)) h'
    _ = Fintype.card ι := by simp

theorem coordinate_finrank_add_one_of_eq_one (b : ι → K) (κ : K)
    (h : κ * (∑ i, b i) = 1) :
    finrank K (LinearMap.range (coordinateUpdate b κ)) + 1 = Fintype.card ι := by
  have h' : coordinateMass b (κ • (1 : ι → K)) = 1 := by
    simpa only [coordinateMass_scale_one] using h
  calc
    _ = finrank K (ι → K) :=
      finrank_range_add_one_of_eval_eq_one (coordinateMass b) (κ • (1 : ι → K)) h'
    _ = Fintype.card ι := by simp

end Coordinates

section Restriction

variable {V W : Type*} [AddCommGroup V] [Module K V] [FiniteDimensional K V]
  [AddCommGroup W] [Module K W] [FiniteDimensional K W]

/-- A witnessed image in the restricted upper space is a real dimension debit
over any lower space vanishing under the same restriction. -/
theorem finrank_debit_of_in_range (ρ : V →ₗ[K] W)
    {U F : Submodule K V} (inc : U ≤ F) (killed : U ≤ LinearMap.ker ρ)
    {M : Submodule K W} (fit : M ≤ LinearMap.range (ρ.domRestrict F)) :
    finrank K U + finrank K M ≤ finrank K F := by
  have kin : U.comap F.subtype ≤ LinearMap.ker (ρ.domRestrict F) := by
    rw [LinearMap.ker_domRestrict]
    exact Submodule.comap_mono killed
  have ku : finrank K (U.comap F.subtype) = finrank K U := by
    rw [← Submodule.finrank_map_subtype_eq F (U.comap F.subtype),
      Submodule.map_comap_subtype, inf_eq_right.mpr inc]
  have ul := Submodule.finrank_mono kin
  rw [ku] at ul
  have ml := Submodule.finrank_mono fit
  have sum := (ρ.domRestrict F).finrank_range_add_finrank_ker
  calc
    finrank K U + finrank K M
        ≤ finrank K (LinearMap.ker (ρ.domRestrict F)) +
          finrank K (LinearMap.range (ρ.domRestrict F)) := Nat.add_le_add ul ml
    _ = finrank K F := (Nat.add_comm _ _).trans sum

end Restriction

end
end RKCert.ReviewedNative.CompensatedRestrictionRank
