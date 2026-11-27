module

public import RKCert.ReviewedNative.FiniteOrderCheck
public import Mathlib.Data.ZMod.Basic
public import Mathlib.LinearAlgebra.Matrix.Block

@[expose] public section

/-! A six-stage strict SDIRK tableau of exact order six in characteristic 263. -/
namespace RKResearch.Certified.SDIRKSix263

open FiniteRootedTree
open scoped Matrix

abbrev F := ZMod 263

def gamma : F := 231

def A : Matrix (Fin 6) (Fin 6) F := Matrix.of fun i j =>
  if i = j then gamma else
    match i.val, j.val with
    | 1, 0 => 130
    | 2, 0 => 33
    | 2, 1 => 227
    | 3, 0 => 98
    | 3, 1 => 139
    | 3, 2 => 10
    | 4, 0 => 235
    | 4, 1 => 53
    | 4, 2 => 224
    | 4, 3 => 170
    | 5, 0 => 21
    | 5, 1 => 46
    | 5, 2 => 256
    | 5, 3 => 135
    | 5, 4 => 133
    | _, _ => 0

def b (i : Fin 6) : F :=
  match i.val with
  | 0 => 0
  | 1 => 6
  | 2 => 81
  | 3 => 236
  | 4 => 120
  | _ => 84

def c (i : Fin 6) : F :=
  match i.val with
  | 0 => 231
  | 1 => 98
  | 2 => 228
  | 3 => 215
  | 4 => 124
  | _ => 33

theorem lowerTriangular : A.IsLowerTriangular := by
  change ∀ i j : Fin 6, i < j → A i j = 0
  simp only [A, Matrix.of_apply]
  decide +kernel

theorem diagonal (i : Fin 6) : A i i = gamma := by simp [A]

theorem diagonal_ne_zero : gamma ≠ 0 := by decide +kernel

theorem row_sums : A *ᵥ 1 = c := by
  funext i
  exact (by decide +kernel : ∀ i : Fin 6, (A *ᵥ 1) i = c i) i

set_option maxHeartbeats 4000000 in
set_option maxRecDepth 8192 in
theorem order_six : HasOrder 6 A b := by
  apply (checkOrder_iff A b 6).mp
  decide +kernel

theorem seventh_bush_value :
    ((bushyTree 7).factorial : F) * (b ⬝ᵥ Φ (bushyTree 7) A) = 161 := by
  rw [factorial_bushyTree, Φ_bushyTree, row_sums]
  decide +kernel

theorem not_order_seven : ¬ HasOrder 7 A b := by
  intro ho
  have hp := ho (bushyTree 7) (by rw [order_bushyTree]; decide)
  rw [seventh_bush_value] at hp
  exact (by decide +kernel : (161 : F) ≠ 1) hp

theorem clocks_distinct : ∀ i j : Fin 6, c i = c j → i = j := by decide +kernel

theorem exists_exact :
    ∃ (M : Matrix (Fin 6) (Fin 6) F) (w : Fin 6 → F) (γ : F),
      M.IsLowerTriangular ∧ (∀ i, M i i = γ) ∧ γ ≠ 0 ∧
      HasOrder 6 M w ∧ ¬ HasOrder 7 M w :=
  ⟨A, b, gamma, lowerTriangular, diagonal, diagonal_ne_zero, order_six, not_order_seven⟩

/-- The witness applies to every nontrivial commutative ring of this
characteristic. The common diagonal is a unit in the target. -/
theorem exists_exact_of_char (R : Type*) [CommRing R] [Nontrivial R] [CharP R 263] :
    ∃ (T : Matrix (Fin 6) (Fin 6) R) (w : Fin 6 → R) (d : R),
      T.IsLowerTriangular ∧ (∀ i, T i i = d) ∧ IsUnit d ∧
      HasOrder 6 T w ∧ ¬ HasOrder 7 T w := by
  let f : F →+* R := ZMod.castHom (dvd_refl 263) R
  have hu : IsUnit gamma := IsUnit.of_mul_eq_one _ (by decide +kernel : gamma * 189 = 1)
  refine ⟨A.map f, f ∘ b, f gamma, lowerTriangular.map f,
    fun i => congrArg f (diagonal i), hu.map f, order_six.map f, ?_⟩
  intro h
  exact not_order_seven ((hasOrder_map_iff (f := f) (ZMod.castHom_injective R)).mp h)

end RKResearch.Certified.SDIRKSix263

#print axioms RKResearch.Certified.SDIRKSix263.exists_exact_of_char
