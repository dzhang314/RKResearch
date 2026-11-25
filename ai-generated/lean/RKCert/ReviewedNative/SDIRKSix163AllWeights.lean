module

public import RKCert.ReviewedNative.DefectTestsSix
public import Mathlib.Data.ZMod.Basic
public import Mathlib.LinearAlgebra.Matrix.Block

@[expose] public section

/-!
# The all-nonzero-weight member of the characteristic-163 paired family

Only the explicit low-degree scalar tests are evaluated below. The
positive full order uses the generic defect filtration, not a tree scan.
-/
namespace RKResearch.Certified.SDIRKSix163AllWeights

open FiniteRootedTree
open RKResearch.Certified.Graded
open scoped Matrix

abbrev F := ZMod 163

def gamma : F := 46
def scale : F := 39

def A : Matrix (Fin 6) (Fin 6) F := Matrix.of fun i j =>
  if i = j then gamma else
    match i.val, j.val with
    | 1, 0 => 36
    | 2, 0 => 84
    | 2, 1 => 151
    | 3, 0 => 89
    | 3, 1 => 3
    | 3, 2 => 71
    | 4, 0 => 148
    | 4, 1 => 82
    | 4, 2 => 119
    | 4, 3 => 13
    | 5, 0 => 112
    | 5, 1 => 73
    | 5, 2 => 142
    | 5, 3 => 156
    | 5, 4 => 78
    | _, _ => 0

def b (i : Fin 6) : F :=
  match i.val with
  | 0 => 33
  | 1 => 19
  | 2 => 160
  | 3 => 85
  | 4 => 72
  | _ => 121

abbrev B : Matrix (Fin 6) (Fin 6) F := scale • A

def c (i : Fin 6) : F :=
  match i.val with
  | 0 | 3 => 46
  | 1 | 4 => 82
  | _ => 118

theorem lowerTriangular : A.IsLowerTriangular := by
  change ∀ i j : Fin 6, i < j → A i j = 0
  simp only [A, Matrix.of_apply]
  decide +kernel

theorem diagonal (i : Fin 6) : A i i = gamma := by simp [A]

theorem diagonal_ne_zero : gamma ≠ 0 := by decide +kernel

theorem weights_ne_zero : ∀ i, b i ≠ 0 := by decide +kernel

theorem row_sums : A *ᵥ 1 = c := by
  funext i
  exact (by decide +kernel : ∀ i : Fin 6, (A *ᵥ 1) i = c i) i

theorem scale_unit : IsUnit scale :=
  IsUnit.of_mul_eq_one _ (by decide +kernel : scale * (46 : F) = 1)

set_option maxHeartbeats 2000000 in
theorem low_defect_tests : DefectTestsSix B b scale := by
  refine ⟨?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_⟩
  · intro j hj
    exact (by decide +kernel : ∀ j : Fin 6,
      ((j.val + 1 : ℕ) : F) * row b ((nodes B) ^ j.val) = scale ^ j.val) ⟨j, hj⟩
  · funext i
    exact (by decide +kernel : ∀ i : Fin 6, (b ᵥ* B) i =
      (scale • b - b * nodes B) i) i
  · intro j hj
    exact (by decide +kernel : ∀ j : Fin 4,
      probe B b j.val (quadraticSeed B) = 0) ⟨j, hj⟩
  · decide +kernel
  · decide +kernel
  · apply Submodule.mem_span_pair.mpr
    refine ⟨104, 60, ?_⟩
    funext i
    exact (by decide +kernel : ∀ i : Fin 6,
      ((104 : F) • quadraticSeed B + (60 : F) • clockSeed B) i =
        mat B (quadraticSeed B) i) i
  · apply Submodule.mem_span_pair.mpr
    refine ⟨104, 61, ?_⟩
    funext i
    exact (by decide +kernel : ∀ i : Fin 6,
      ((104 : F) • quadraticSeed B + (61 : F) • clockSeed B) i =
        monomialStageDefect B 2 i) i
  · decide +kernel
  · decide +kernel

theorem order_six : HasOrder 6 A b :=
  DefectTestsSix.hasOrder_of_unit_scale scale_unit low_defect_tests

theorem seventh_bush_value :
    ((bushyTree 7).factorial : F) * (b ⬝ᵥ Φ (bushyTree 7) A) = 12 := by
  rw [factorial_bushyTree, Φ_bushyTree, row_sums]
  decide +kernel

theorem not_order_seven : ¬ HasOrder 7 A b := by
  intro ho
  have hp := ho (bushyTree 7) (by rw [order_bushyTree]; decide)
  rw [seventh_bush_value] at hp
  exact (by decide +kernel : (12 : F) ≠ 1) hp

theorem exists_exact_with_all_weights :
    ∃ (A : Matrix (Fin 6) (Fin 6) F) (b : Fin 6 → F) (γ : F),
      A.IsLowerTriangular ∧ (∀ i, A i i = γ) ∧ γ ≠ 0 ∧
      (∀ i, b i ≠ 0) ∧ HasOrder 6 A b ∧ ¬ HasOrder 7 A b :=
  ⟨A, b, gamma, lowerTriangular, diagonal, diagonal_ne_zero, weights_ne_zero,
    order_six, not_order_seven⟩

end RKResearch.Certified.SDIRKSix163AllWeights
