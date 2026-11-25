module

public import RKCert.ReviewedNative.DefectFiltrationOrder
public import Mathlib.Algebra.Algebra.Bilinear

import Mathlib.Tactic.LinearCombination

@[expose] public section

/-! # Division-free moment cuts for a sufficient reviewed defect certificate -/
namespace RKResearch.Certified.Graded

open scoped Matrix

variable {ι R : Type*} [Fintype ι] [CommRing R]

/-- The scaled pure clock equations through the requested budget. -/
def ScaledClockMoments (B : Matrix ι ι R) (b : ι → R) (z : R) (p : ℕ) : Prop :=
  ∀ j, j < p → ((j + 1 : ℕ) : R) * row b ((nodes B)^j) = z^j

/-- The actual scaled adjoint equation, without dividing by the scale. -/
def ScaledD1 (B : Matrix ι ι R) (b : ι → R) (z : R) : Prop :=
  b ᵥ* B = z • b - b * nodes B

/-- The joint kernel of the first q+1 weighted clock moments. -/
def probeCut (B : Matrix ι ι R) (b : ι → R) (q : ℕ) : Submodule R (ι → R) :=
  ⨅ j : Fin (q + 1), (probe B b j.val).ker

theorem mem_probeCut {B : Matrix ι ι R} {b v : ι → R} {q : ℕ} :
    v ∈ probeCut B b q ↔ ∀ j, j ≤ q → probe B b j v = 0 := by
  simp only [probeCut, Submodule.mem_iInf, LinearMap.mem_ker]
  constructor
  · intro h j hj
    exact h ⟨j, Nat.lt_succ_of_le hj⟩
  · intro h j
    exact h j.val (Nat.le_of_lt_succ j.isLt)

theorem probe_zero_eq_row (B : Matrix ι ι R) (b v : ι → R) :
    probe B b 0 v = row b v := by simp only [probe, pow_zero, mul_one]

theorem probe_clock_mul (B : Matrix ι ι R) (b : ι → R) (j : ℕ) (v : ι → R) :
    probe B b j (nodes B * v) = probe B b (j + 1) v := by
  simp only [probe, row_apply, dotProduct, Pi.mul_apply, pow_succ, mul_assoc]

theorem probe_pow_eq_row (B : Matrix ι ι R) (b : ι → R) (j k : ℕ) :
    probe B b j ((nodes B)^k) = row b ((nodes B)^(j + k)) := by
  simp only [probe, row_apply, dotProduct, Pi.mul_apply, Pi.pow_apply, pow_add, mul_assoc]

theorem probeCut_zero (B : Matrix ι ι R) (b : ι → R) :
    probeCut B b 0 = (row b).ker := by
  ext v
  rw [mem_probeCut, LinearMap.mem_ker]
  constructor
  · intro h
    simpa only [probe_zero_eq_row] using h 0 le_rfl
  · intro h j hj
    have e : j = 0 := by omega
    subst j
    simpa only [probe_zero_eq_row] using h

theorem probeCut_anti (B : Matrix ι ι R) (b : ι → R) {q r : ℕ} (h : q ≤ r) :
    probeCut B b r ≤ probeCut B b q := by
  intro v hv
  exact mem_probeCut.mpr fun j hj => mem_probeCut.mp hv j (hj.trans h)

theorem probeCut_clock (B : Matrix ι ι R) (b : ι → R) (q : ℕ) :
    probeCut B b (q + 1) ≤ (probeCut B b q).comap (diag (nodes B)) := by
  intro v hv
  change nodes B * v ∈ probeCut B b q
  apply mem_probeCut.mpr
  intro j hj
  rw [probe_clock_mul]
  exact mem_probeCut.mp hv (j + 1) (by omega)

namespace ScaledD1

variable {B : Matrix ι ι R} {b : ι → R} {z : R}

theorem on_column (h : ScaledD1 B b z) (v : ι → R) :
    row b (mat B v) = z * row b v - probe B b 1 v := by
  change b ᵥ* B = z • b - b * nodes B at h
  simp only [row_apply, mat_apply, Matrix.dotProduct_mulVec, h, sub_dotProduct,
    smul_dotProduct, smul_eq_mul, probe, pow_one]
  rfl

theorem advance_cut (h : ScaledD1 B b z) :
    probeCut B b 1 ≤ (probeCut B b 0).comap (mat B) := by
  intro v hv
  change mat B v ∈ probeCut B b 0
  rw [probeCut_zero, LinearMap.mem_ker, h.on_column]
  have h0 : row b v = 0 := by
    simpa only [probe_zero_eq_row] using mem_probeCut.mp hv 0 (by decide)
  have h1 : probe B b 1 v = 0 := mem_probeCut.mp hv 1 le_rfl
  rw [h0, h1, mul_zero, sub_zero]

/-- D1 pays the raw primitive mass from the two scalar clock moments. -/
theorem primitive_mass (h : ScaledD1 B b z) {p : ℕ}
    (quad : ScaledClockMoments B b z p) (j : ℕ) (hj : j + 1 < p) :
    row b (monomialStageDefect B j) = 0 := by
  have h0 := quad j (by omega)
  have h1 := quad (j + 1) hj
  have he : probe B b 1 ((nodes B)^j) = row b ((nodes B)^(j + 1)) := by
    simpa only [Nat.add_comm 1 j] using probe_pow_eq_row B b 1 j
  rw [monomialStageDefect_as_map, map_sub, map_smul, smul_eq_mul, h.on_column, he]
  simp only [Nat.cast_add, Nat.cast_one] at h0 h1 ⊢
  rw [show z^(j + 1) = z^j * z from pow_succ z j] at h1
  linear_combination z * h0 - h1

end ScaledD1

theorem monomialStageDefect_at_zero (B : Matrix ι ι R) :
    monomialStageDefect B 0 = 0 := by
  rw [monomialStageDefect_as_map]
  simp [mat_apply]

/-- The product of two submodules fits into the given target. This asks
only about the actual pointwise product, with no algebra-closure premise. -/
def ProductsIn (U V W : Submodule R (ι → R)) : Prop :=
  ∀ ⦃u v⦄, u ∈ U → v ∈ V → u * v ∈ W

namespace ProductsIn

variable {U V W W' : Submodule R (ι → R)}

theorem swap (h : ProductsIn U V W) : ProductsIn V U W := by
  intro v u hv hu
  rw [mul_comm]
  exact h hu hv

theorem mono (h : ProductsIn U V W) (hle : W ≤ W') : ProductsIn U V W' :=
  fun _ _ hu hv => hle (h hu hv)

theorem span {a c : Set (ι → R)} (h : ∀ u ∈ a, ∀ v ∈ c, u * v ∈ W) :
    ProductsIn (Submodule.span R a) (Submodule.span R c) W := by
  intro u v hu hv
  rw [← LinearMap.mul_apply' (R := R)]
  exact LinearMap.BilinMap.apply_apply_mem_of_mem_span W a c (LinearMap.mul R (ι → R))
    h u v hu hv

theorem singleton_left (s : ι → R) (h : U ≤ W.comap (diag s)) :
    ProductsIn (Submodule.span R ({s} : Set (ι → R))) U W := by
  intro u v hu hv
  obtain ⟨a, rfl⟩ := Submodule.mem_span_singleton.mp hu
  have hh : s * v ∈ W := h hv
  simpa only [smul_mul_assoc] using W.smul_mem a hh

theorem singleton_pair {s t : ι → R} (h : s * t ∈ W) :
    ProductsIn (Submodule.span R ({s} : Set (ι → R)))
      (Submodule.span R ({t} : Set (ι → R))) W := by
  apply span
  intro u hu v hv
  simp only [Set.mem_singleton_iff] at hu hv
  simpa only [hu, hv] using h

end ProductsIn
end RKResearch.Certified.Graded
