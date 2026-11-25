module

public import RKCert.ReviewedNative.DefectFiltrationOrder
public import Mathlib.Algebra.Algebra.Bilinear

import Mathlib.Tactic.IntervalCases
import Mathlib.Tactic.LinearCombination

@[expose] public section

/-! # A low-defect sufficient certificate for reviewed order six -/
namespace RKResearch.Certified.Graded

open scoped Matrix

variable {ι R : Type*} [Fintype ι] [CommRing R]

abbrev quadraticSeed (B : Matrix ι ι R) : ι → R := monomialStageDefect B 1

abbrev clockSeed (B : Matrix ι ι R) : ι → R := nodes B * quadraticSeed B

/-- The two accounted-for genuine cubic defect directions. -/
abbrev cubicDefects (B : Matrix ι ι R) : Submodule R (ι → R) :=
  Submodule.span R ({quadraticSeed B, clockSeed B} : Set (ι → R))

/-- All tests are on the actual normalized matrix, weights, and clocks.
No division, distinctness of nodes, common diagonal, or order hypothesis
is used in this certificate. -/
structure DefectTestsSix (B : Matrix ι ι R) (b : ι → R) (z : R) : Prop where
  quadrature : ∀ j, j < 6 → ((j + 1 : ℕ) : R) * row b ((nodes B) ^ j) = z ^ j
  adjoint : b ᵥ* B = z • b - b * nodes B
  seed_moments : ∀ j, j < 4 → probe B b j (quadraticSeed B) = 0
  square_mass : probe B b 0 ((quadraticSeed B) ^ 2) = 0
  square_clock : probe B b 1 ((quadraticSeed B) ^ 2) = 0
  seed_advance : mat B (quadraticSeed B) ∈ cubicDefects B
  cubic : monomialStageDefect B 2 ∈ cubicDefects B
  clock_seed_advance : probe B b 1 (mat B (clockSeed B)) = 0
  quartic : probe B b 1 (monomialStageDefect B 3) = 0

namespace DefectTestsSix

variable {B : Matrix ι ι R} {b : ι → R} {z : R}

private theorem probe_zero (B : Matrix ι ι R) (b v : ι → R) :
    probe B b 0 v = row b v := by
  simp only [probe, pow_zero, mul_one]

private theorem probe_pow_mul (B : Matrix ι ι R) (b : ι → R) (j n : ℕ) (v : ι → R) :
    probe B b j ((nodes B) ^ n * v) = probe B b (j + n) v := by
  simp only [probe, row_apply, dotProduct, Pi.mul_apply, Pi.pow_apply, pow_add, mul_assoc]

private theorem probe_clock (B : Matrix ι ι R) (b : ι → R) (j : ℕ) (v : ι → R) :
    probe B b j (nodes B * v) = probe B b (j + 1) v := by
  simpa only [pow_one] using probe_pow_mul B b j 1 v

private theorem probe_pow (B : Matrix ι ι R) (b : ι → R) (j n : ℕ) :
    probe B b j ((nodes B) ^ n) = row b ((nodes B) ^ (j + n)) := by
  simp only [probe, row_apply, dotProduct, Pi.mul_apply, Pi.pow_apply, pow_add, mul_assoc]

private def twoSilent (B : Matrix ι ι R) (b : ι → R) : Submodule R (ι → R) :=
  (row b).ker ⊓ (probe B b 1).ker

private def sixSpace (B : Matrix ι ι R) (b : ι → R) : ℕ → Submodule R (ι → R)
  | 0 => ⊥
  | 1 => ⊥
  | 2 => Submodule.span R {quadraticSeed B}
  | 3 => cubicDefects B
  | 4 => twoSilent B b
  | _ => (row b).ker

private theorem pair_le {S : Submodule R (ι → R)} {x y : ι → R}
    (hx : x ∈ S) (hy : y ∈ S) : Submodule.span R ({x, y} : Set (ι → R)) ≤ S := by
  apply Submodule.span_le.mpr
  intro v hv
  simp only [Set.mem_insert_iff, Set.mem_singleton_iff] at hv
  rcases hv with rfl | rfl
  · exact hx
  · exact hy

private theorem clock_mem_cubic (B : Matrix ι ι R) :
    clockSeed B ∈ cubicDefects B :=
  Submodule.subset_span (by simp)

private theorem singleton_le_cubic (B : Matrix ι ι R) :
    Submodule.span R ({quadraticSeed B} : Set (ι → R)) ≤ cubicDefects B := by
  apply (Submodule.span_singleton_le_iff_mem _ _).mpr
  exact Submodule.subset_span (by simp)

private theorem adjoint_apply (h : DefectTestsSix B b z) (v : ι → R) :
    row b (mat B v) = z * row b v - probe B b 1 v := by
  simp only [row_apply, mat_apply, Matrix.dotProduct_mulVec, h.adjoint, sub_dotProduct,
    smul_dotProduct, smul_eq_mul, probe, pow_one]
  rfl

private theorem clock_power_silent (h : DefectTestsSix B b z) (n : ℕ) (hn : n < 3) :
    (nodes B) ^ n * quadraticSeed B ∈ twoSilent B b := by
  constructor
  · change row b ((nodes B) ^ n * quadraticSeed B) = 0
    rw [← probe_zero B b, probe_pow_mul, zero_add]
    exact h.seed_moments n (by omega)
  · change probe B b 1 ((nodes B) ^ n * quadraticSeed B) = 0
    rw [probe_pow_mul]
    exact h.seed_moments (1 + n) (by omega)

private theorem cubic_silent (h : DefectTestsSix B b z) :
    cubicDefects B ≤ twoSilent B b := by
  apply pair_le
  · simpa only [pow_zero, one_mul] using h.clock_power_silent 0 (by decide)
  · simpa only [pow_one] using h.clock_power_silent 1 (by decide)

private theorem advance_silent (h : DefectTestsSix B b z) {v : ι → R}
    (hv : v ∈ twoSilent B b) : mat B v ∈ (row b).ker := by
  change row b (mat B v) = 0
  have h0 : row b v = 0 := hv.1
  have h1 : probe B b 1 v = 0 := hv.2
  rw [h.adjoint_apply, h0, h1, mul_zero, sub_zero]

private theorem clock_silent {v : ι → R} (hv : v ∈ twoSilent B b) :
    diag (nodes B) v ∈ (row b).ker := by
  change row b (nodes B * v) = 0
  rw [← probe_zero B b, probe_clock]
  exact hv.2

private theorem clock_mem (h : DefectTestsSix B b z) (j : ℕ) (hj : j + 1 < 6) :
    sixSpace B b j ≤ (sixSpace B b (j + 1)).comap (diag (nodes B)) := by
  have hbound : j ≤ 4 := by omega
  interval_cases j <;> simp only [sixSpace]
  · exact bot_le
  · exact bot_le
  · apply (Submodule.span_singleton_le_iff_mem _ _).mpr
    exact clock_mem_cubic B
  · apply pair_le
    · change nodes B * quadraticSeed B ∈ twoSilent B b
      simpa only [pow_one] using h.clock_power_silent 1 (by decide)
    · change nodes B * (nodes B * quadraticSeed B) ∈ twoSilent B b
      simpa only [pow_two, mul_assoc] using h.clock_power_silent 2 (by decide)
  · intro v hv
    exact clock_silent hv

private theorem advance_mem (h : DefectTestsSix B b z) (j : ℕ) (hj : j + 1 < 6) :
    sixSpace B b j ≤ (sixSpace B b (j + 1)).comap (mat B) := by
  have hbound : j ≤ 4 := by omega
  interval_cases j <;> simp only [sixSpace]
  · exact bot_le
  · exact bot_le
  · apply (Submodule.span_singleton_le_iff_mem _ _).mpr
    exact h.seed_advance
  · apply pair_le
    · exact h.cubic_silent h.seed_advance
    · change mat B (clockSeed B) ∈ twoSilent B b
      exact ⟨h.advance_silent (h.cubic_silent (clock_mem_cubic B)), h.clock_seed_advance⟩
  · intro v hv
    exact h.advance_silent hv

private theorem defect_mass (h : DefectTestsSix B b z) (j : ℕ) (hj : j < 5) :
    row b (monomialStageDefect B j) = 0 := by
  have h0 := h.quadrature j (by omega)
  have h1 := h.quadrature (j + 1) (by omega)
  have he : probe B b 1 ((nodes B) ^ j) = row b ((nodes B) ^ (j + 1)) := by
    simpa only [Nat.add_comm 1 j] using probe_pow B b 1 j
  rw [monomialStageDefect_as_map, map_sub, map_smul, smul_eq_mul, h.adjoint_apply, he]
  simp only [Nat.cast_add, Nat.cast_one] at h0 h1 ⊢
  rw [show z ^ (j + 1) = z ^ j * z from pow_succ z j] at h1
  linear_combination z * h0 - h1

private theorem defect_mem (h : DefectTestsSix B b z) (j : ℕ) (hj : j + 1 < 6) :
    monomialStageDefect B j ∈ sixSpace B b (j + 1) := by
  have hbound : j ≤ 4 := by omega
  interval_cases j
  · have hzero : monomialStageDefect B 0 = 0 := by
      rw [monomialStageDefect_as_map]
      simp [mat_apply]
    rw [hzero]
    exact (sixSpace B b 1).zero_mem
  · exact Submodule.mem_span_singleton_self _
  · exact h.cubic
  · exact ⟨h.defect_mass 3 (by decide), h.quartic⟩
  · exact h.defect_mass 4 (by decide)

private theorem span_mul_mem {S : Submodule R (ι → R)} {x y : ι → R}
    {U V : Set (ι → R)} (h : ∀ v ∈ U, ∀ w ∈ V, v * w ∈ S)
    (hx : x ∈ Submodule.span R U) (hy : y ∈ Submodule.span R V) : x * y ∈ S := by
  rw [← LinearMap.mul_apply' (R := R)]
  exact LinearMap.BilinMap.apply_apply_mem_of_mem_span S U V (LinearMap.mul R (ι → R))
    h x y hx hy

private theorem square_silent (h : DefectTestsSix B b z) :
    quadraticSeed B * quadraticSeed B ∈ twoSilent B b := by
  constructor
  · change row b (quadraticSeed B * quadraticSeed B) = 0
    simpa only [probe_zero, pow_two] using h.square_mass
  · change probe B b 1 (quadraticSeed B * quadraticSeed B) = 0
    simpa only [pow_two] using h.square_clock

private theorem seed_clock_product_silent (h : DefectTestsSix B b z) :
    quadraticSeed B * clockSeed B ∈ (row b).ker := by
  change row b (quadraticSeed B * (nodes B * quadraticSeed B)) = 0
  have e : quadraticSeed B * (nodes B * quadraticSeed B) =
      nodes B * (quadraticSeed B) ^ 2 := by
    rw [pow_two]
    ac_rfl
  rw [e, ← probe_zero B b, probe_clock]
  exact h.square_clock

private theorem product_mem (h : DefectTestsSix B b z) (j k : ℕ) (hjk : j + k < 6)
    {v w : ι → R} (hv : v ∈ sixSpace B b j) (hw : w ∈ sixSpace B b k) :
    v * w ∈ sixSpace B b (j + k) := by
  by_cases hj : j < 2
  · have hz : v = 0 := by
      interval_cases j <;> exact (Submodule.mem_bot R).mp hv
    subst v
    rw [zero_mul]
    exact (sixSpace B b (j + k)).zero_mem
  by_cases hk : k < 2
  · have hz : w = 0 := by
      interval_cases k <;> exact (Submodule.mem_bot R).mp hw
    subst w
    rw [mul_zero]
    exact (sixSpace B b (j + k)).zero_mem
  have hjlo : 2 ≤ j := by omega
  have hklo : 2 ≤ k := by omega
  have hjhi : j ≤ 3 := by omega
  have hkhi : k ≤ 3 := by omega
  have prod22 {x y : ι → R}
      (hx : x ∈ sixSpace B b 2) (hy : y ∈ sixSpace B b 2) :
      x * y ∈ sixSpace B b 4 := by
    simp only [sixSpace] at hx hy ⊢
    apply span_mul_mem _ hx hy
    intro a ha c hc
    simp only [Set.mem_singleton_iff] at ha hc
    subst a
    subst c
    exact h.square_silent
  have prod23 {x y : ι → R}
      (hx : x ∈ sixSpace B b 2) (hy : y ∈ sixSpace B b 3) :
      x * y ∈ sixSpace B b 5 := by
    simp only [sixSpace] at hx hy ⊢
    apply span_mul_mem _ hx hy
    intro a ha c hc
    simp only [Set.mem_singleton_iff] at ha
    simp only [Set.mem_insert_iff, Set.mem_singleton_iff] at hc
    subst a
    rcases hc with rfl | rfl
    · exact h.square_silent.1
    · exact h.seed_clock_product_silent
  interval_cases j <;> interval_cases k <;>
    first | exact prod22 hv hw | exact prod23 hv hw |
      (rw [mul_comm]; exact prod23 hw hv) | omega

private theorem silent_mem (h : DefectTestsSix B b z) (j : ℕ) (hj : j < 6) :
    sixSpace B b j ≤ (row b).ker := by
  interval_cases j <;> simp only [sixSpace]
  · exact bot_le
  · exact bot_le
  · intro v hv
    exact (h.cubic_silent (singleton_le_cubic B hv)).1
  · intro v hv
    exact (h.cubic_silent hv).1
  · intro v hv
    exact hv.1
  · exact le_rfl

/-- J₀=J₁=0, J₂=span(s), J₃=span(s,Cs), J₄=ker(M₀)∩ker(M₁),
and J₅=ker(M₀) certify the full genuine reviewed recursion. -/
private def filtration (h : DefectTestsSix B b z) : DefectFiltration B b 6 where
  space := sixSpace B b
  clock := h.clock_mem
  advance := h.advance_mem
  primitive := h.defect_mem
  product := h.product_mem
  silent := h.silent_mem

/-- Main certificate. Over any field the regularity hypothesis is just
nonzeroness of the chosen normalization scale. There is no hidden
characteristic-zero requirement, and all payment is denominator-cleared. -/
theorem hasOrder_of_scale {A : Matrix ι ι R} (hz : IsLeftRegular z)
    (h : DefectTestsSix (z • A) b z) : RKResearch.HasOrder 6 A b :=
  h.filtration.hasOrder_of_smul hz h.quadrature

theorem hasOrder_of_unit_scale {A : Matrix ι ι R} (hz : IsUnit z)
    (h : DefectTestsSix (z • A) b z) : RKResearch.HasOrder 6 A b :=
  hasOrder_of_scale hz.isRegular.left h

end DefectTestsSix
end RKResearch.Certified.Graded
