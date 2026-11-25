module

public import RKCert.ReviewedNative.FiniteOrderCheck
public import Mathlib.Data.ZMod.Basic
public import Mathlib.LinearAlgebra.Matrix.Block

@[expose] public section

/-!
# An exact six-stage SDIRK method of order six in characteristic 163

The three physical abscissae occur twice, in order:
`46, 82, 118, 46, 82, 118`. The common diagonal is nonzero.
The positive order certificate uses the existing complete checker on
the reviewed rooted trees.
-/
namespace RKResearch.Certified.SDIRKSix163

open FiniteRootedTree
open scoped Matrix

abbrev F := ZMod 163

def gamma : F := 46

def A : Matrix (Fin 6) (Fin 6) F := Matrix.of fun i j =>
  if i = j then gamma else
    match i.val, j.val with
    | 1, 0 => 36
    | 2, 0 => 84
    | 2, 1 => 151
    | 3, 0 => 13
    | 3, 1 => 103
    | 3, 2 => 47
    | 4, 1 => 81
    | 4, 2 => 44
    | 4, 3 => 74
    | 5, 0 => 150
    | 5, 1 => 126
    | 5, 2 => 13
    | 5, 3 => 84
    | 5, 4 => 25
    | _, _ => 0

def b (i : Fin 6) : F :=
  match i.val with
  | 3 => 118
  | 4 => 91
  | 5 => 118
  | _ => 0

def c (i : Fin 6) : F :=
  match i.val with
  | 0 | 3 => 46
  | 1 | 4 => 82
  | _ => 118

theorem lowerTriangular : A.IsLowerTriangular := by
  change ∀ i j : Fin 6, i < j → A i j = 0
  simp only [A, Matrix.of_apply]
  decide +kernel

theorem diagonal (i : Fin 6) : A i i = gamma := by
  simp [A]

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
    ((bushyTree 7).factorial : F) * (b ⬝ᵥ Φ (bushyTree 7) A) = 12 := by
  rw [factorial_bushyTree, Φ_bushyTree, row_sums]
  decide +kernel

theorem not_order_seven : ¬ HasOrder 7 A b := by
  intro ho
  have hp := ho (bushyTree 7) (by rw [order_bushyTree]; decide)
  rw [seventh_bush_value] at hp
  exact (by decide +kernel : (12 : F) ≠ 1) hp

theorem exists_exact :
    ∃ (A : Matrix (Fin 6) (Fin 6) F) (b : Fin 6 → F) (γ : F),
      A.IsLowerTriangular ∧ (∀ i, A i i = γ) ∧ γ ≠ 0 ∧
      HasOrder 6 A b ∧ ¬ HasOrder 7 A b :=
  ⟨A, b, gamma, lowerTriangular, diagonal, diagonal_ne_zero, order_six, not_order_seven⟩

end RKResearch.Certified.SDIRKSix163
