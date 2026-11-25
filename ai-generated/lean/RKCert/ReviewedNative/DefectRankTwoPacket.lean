module

public import RKCert.ReviewedNative.DefectLowGrades

import Mathlib.Tactic.Abel
import Mathlib.Tactic.FinCases
import Mathlib.Tactic.NormNum

@[expose] public section

/-! # The four- and ten-generator receipts for a two-column cubic chart -/
namespace RKResearch.Certified.Graded.LowDefects

variable {ι R : Type*} [Fintype ι] [CommRing R]

/-- The actual Volterra commutator on one clock column. This definition
is kept here to avoid importing a stage-floor or characteristic theorem. -/
def cubicTap (B : Matrix ι ι R) : ι → R :=
  diag (nodes B) (mat B (nodes B)) - mat B (diag (nodes B) (nodes B)) -
    mat B (mat B (nodes B))

/-- The cubic primitive is accounted for by the two stage moves and the
genuine Volterra column. The integer 2 is not divided out. -/
theorem cubic_primitive_formula (B : Matrix ι ι R) :
    monomialStageDefect B 2 =
      diag (nodes B) (seed B) - mat B (seed B) - (2 : R) • cubicTap B := by
  have es : seed B = (2 : R) • mat B (nodes B) - (nodes B)^2 := by
    have h := monomialStageDefect_as_map B 1
    rw [show (1 + 1 : ℕ) = 2 from by decide, pow_one] at h
    simpa only [Nat.cast_ofNat] using h
  have he : monomialStageDefect B 2 = (3 : R) • mat B ((nodes B)^2) - (nodes B)^3 := by
    have h := monomialStageDefect_as_map B 2
    rw [show (2 + 1 : ℕ) = 3 from by decide] at h
    simpa only [Nat.cast_ofNat] using h
  have hx : diag (nodes B) (nodes B) = (nodes B)^2 := by
    change nodes B * nodes B = (nodes B)^2
    rw [pow_two]
  have hxx : diag (nodes B) ((nodes B)^2) = (nodes B)^3 := by
    change nodes B * (nodes B)^2 = (nodes B)^3
    exact (pow_succ' (nodes B) 2).symm
  have three (v : ι → R) : (3 : R) • v = v + v + v := by
    rw [show (3 : R) = 2 + 1 from by norm_num, add_smul, one_smul, two_smul]
  simp only [he, es, cubicTap, hx, map_sub, map_add, smul_sub, hxx, two_smul, three] <;> abel

abbrev cubicPair (B : Matrix ι ι R) : Submodule R (ι → R) :=
  Submodule.span R ({seed B, cubicTap B} : Set (ι → R))

theorem seed_mem_pair (B : Matrix ι ι R) : seed B ∈ cubicPair B :=
  Submodule.subset_span (by simp)

theorem tap_mem_pair (B : Matrix ι ι R) : cubicTap B ∈ cubicPair B :=
  Submodule.subset_span (by simp)

structure CubicPairChart (B : Matrix ι ι R) : Prop where
  clock_seed : diag (nodes B) (seed B) ∈ cubicPair B
  advance_seed : mat B (seed B) ∈ cubicPair B

theorem CubicPairChart.cover {B : Matrix ι ι R} (h : CubicPairChart B) :
    CubicCover B (cubicPair B) where
  seed_mem := seed_mem_pair B
  clock_seed := h.clock_seed
  advance_seed := h.advance_seed
  primitive := by
    rw [cubic_primitive_formula]
    exact (cubicPair B).sub_mem ((cubicPair B).sub_mem h.clock_seed h.advance_seed)
      ((cubicPair B).smul_mem _ (tap_mem_pair B))

/-- The four genuinely new grade-four entries after the cubic chart. -/
def quarticAtom (B : Matrix ι ι R) (j : Fin 4) : ι → R :=
  match j.val with
  | 0 => diag (nodes B) (cubicTap B)
  | 1 => mat B (cubicTap B)
  | 2 => seed B * seed B
  | _ => monomialStageDefect B 3

variable {B : Matrix ι ι R}

theorem quartic_four (h : CubicPairChart B) (W : Submodule R (ι → R)) :
    quartic B (cubicPair B) ≤ W ↔
      cubicPair B ≤ W ∧ ∀ j : Fin 4, quarticAtom B j ∈ W := by
  rw [quartic_le_iff]
  constructor
  · rintro ⟨h₀, hC, hA, hs, he⟩
    refine ⟨h₀, ?_⟩
    intro j
    fin_cases j
    · exact hC (tap_mem_pair B)
    · exact hA (tap_mem_pair B)
    · exact hs
    · exact he
  · rintro ⟨h₀, hv⟩
    refine ⟨h₀, ?_, ?_, hv 2, hv 3⟩
    · exact span_pair_le_iff.mpr ⟨h₀ h.clock_seed, hv 0⟩
    · exact span_pair_le_iff.mpr ⟨h₀ h.advance_seed, hv 1⟩

theorem quartic_atom_mem (h : CubicPairChart B) (j : Fin 4) :
    quarticAtom B j ∈ quartic B (cubicPair B) :=
  ((quartic_four h _).mp le_rfl).2 j

/-- The exact ten new generator tests in a quintic inclusion:
four clock images, four matrix images, one seed product, and e₅. -/
theorem quintic_ten (h : CubicPairChart B) (W : Submodule R (ι → R)) :
    quintic B (cubicPair B) ≤ W ↔
      quartic B (cubicPair B) ≤ W ∧
      (∀ j : Fin 4, diag (nodes B) (quarticAtom B j) ∈ W) ∧
      (∀ j : Fin 4, mat B (quarticAtom B j) ∈ W) ∧
      seed B * cubicTap B ∈ W ∧ monomialStageDefect B 4 ∈ W := by
  rw [quintic_le_iff]
  constructor
  · rintro ⟨h₀, hC, hA, hs, he⟩
    exact ⟨h₀, fun j => hC (quartic_atom_mem h j), fun j => hA (quartic_atom_mem h j),
      hs (tap_mem_pair B), he⟩
  · rintro ⟨h₀, hC, hA, hs, he⟩
    refine ⟨h₀, (quartic_four h _).mpr ⟨?_, hC⟩,
      (quartic_four h _).mpr ⟨?_, hA⟩, ?_, he⟩
    · intro v hv
      exact h₀ (quartic_clock (B := B) (U := cubicPair B) hv)
    · intro v hv
      exact h₀ (quartic_advance (B := B) (U := cubicPair B) hv)
    · apply span_pair_le_iff.mpr
      exact ⟨h₀ (quartic_square (B := B) (U := cubicPair B)), hs⟩

theorem products_singleton_left_iff {s : ι → R} {U W : Submodule R (ι → R)} :
    ProductsIn (Submodule.span R ({s} : Set (ι → R))) U W ↔ U ≤ W.comap (diag s) := by
  constructor
  · intro h v hv
    exact h (Submodule.mem_span_singleton_self s) hv
  · exact ProductsIn.singleton_left s

theorem products_pair_left_iff {s t : ι → R} {U W : Submodule R (ι → R)} :
    ProductsIn (Submodule.span R ({s, t} : Set (ι → R))) U W ↔
      U ≤ W.comap (diag s) ∧ U ≤ W.comap (diag t) := by
  constructor
  · intro h
    exact ⟨fun _ hv => h (Submodule.subset_span (by simp)) hv,
      fun _ hv => h (Submodule.subset_span (by simp)) hv⟩
  · rintro ⟨hs, ht⟩ u v hu hv
    obtain ⟨a, c, rfl⟩ := Submodule.mem_span_pair.mp hu
    simp only [add_mul, smul_mul_assoc]
    exact W.add_mem (W.smul_mem a (hs hv)) (W.smul_mem c (ht hv))

theorem seed_quartic_four (h : CubicPairChart B) (W : Submodule R (ι → R)) :
    ProductsIn (seedSpace B) (quartic B (cubicPair B)) W ↔
      seed B * seed B ∈ W ∧ seed B * cubicTap B ∈ W ∧
      ∀ j : Fin 4, seed B * quarticAtom B j ∈ W := by
  simp only [products_singleton_left_iff, quartic_four h, span_pair_le_iff, and_assoc] <;> rfl

theorem cubic_square_three (B : Matrix ι ι R) (W : Submodule R (ι → R)) :
    ProductsIn (cubicPair B) (cubicPair B) W ↔
      seed B * seed B ∈ W ∧ seed B * cubicTap B ∈ W ∧ cubicTap B * cubicTap B ∈ W := by
  simp only [products_pair_left_iff, span_pair_le_iff]
  change ((seed B * seed B ∈ W ∧ seed B * cubicTap B ∈ W) ∧
      (cubicTap B * seed B ∈ W ∧ cubicTap B * cubicTap B ∈ W)) ↔ _
  constructor
  · rintro ⟨⟨hs, hst⟩, _, ht⟩
    exact ⟨hs, hst, ht⟩
  · rintro ⟨hs, hst, ht⟩
    exact ⟨⟨hs, hst⟩, ⟨by simpa only [mul_comm] using hst, ht⟩⟩

theorem seed_quintic_ten (h : CubicPairChart B) (W : Submodule R (ι → R)) :
    ProductsIn (seedSpace B) (quintic B (cubicPair B)) W ↔
      ProductsIn (seedSpace B) (quartic B (cubicPair B)) W ∧
      (∀ j : Fin 4, seed B * diag (nodes B) (quarticAtom B j) ∈ W) ∧
      (∀ j : Fin 4, seed B * mat B (quarticAtom B j) ∈ W) ∧
      seed B * (seed B * cubicTap B) ∈ W ∧ seed B * monomialStageDefect B 4 ∈ W := by
  simp only [products_singleton_left_iff, quintic_ten h] <;> rfl

theorem cubic_quartic_four (h : CubicPairChart B) (W : Submodule R (ι → R)) :
    ProductsIn (cubicPair B) (quartic B (cubicPair B)) W ↔
      ProductsIn (seedSpace B) (quartic B (cubicPair B)) W ∧
      cubicTap B * seed B ∈ W ∧ cubicTap B * cubicTap B ∈ W ∧
      ∀ j : Fin 4, cubicTap B * quarticAtom B j ∈ W := by
  rw [products_pair_left_iff, products_singleton_left_iff, quartic_four h (W.comap (diag (cubicTap B)))]
  simp only [span_pair_le_iff, and_assoc] <;> rfl

end RKResearch.Certified.Graded.LowDefects
