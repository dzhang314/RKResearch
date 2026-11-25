module

public import RKCert.ReviewedNative.FiniteScaledOrderCheck
public import Mathlib.Algebra.Field.Rat
public import Mathlib.Data.Rat.Cast.CharZero
public import Mathlib.LinearAlgebra.Matrix.Block

import Mathlib.LinearAlgebra.Matrix.Notation
import Mathlib.Tactic.FinCases
import Mathlib.Tactic.Ring

@[expose] public section

/-! # Exact small rational strict SDIRK constructions

The full positive-order proof runs on integer numerator tableaux in the
reviewed finite tree checker. A single next-order tall tree makes each
displayed witness exact. These are upper constructions only. -/

namespace RKResearch.Certified

open RKResearch FiniteRootedTree
open scoped Matrix

namespace RationalStrictSDIRKNumerators

/-- The stage denominator is 18 for both tableaux. -/
def stages {s : ℕ} (M : Matrix (Fin s) (Fin s) ℤ) : Matrix (Fin s) (Fin s) ℚ :=
  Matrix.of fun i j => (M i j : ℚ)/18

/-- The output denominator is 8 for both tableaux. -/
def weights {s : ℕ} (w : Fin s → ℤ) : Fin s → ℚ := fun i => (w i : ℚ)/8

theorem order_of_check {s p : ℕ} (M : Matrix (Fin s) (Fin s) ℤ) (w : Fin s → ℤ)
    (h : checkScaledOrder (fun v => M *ᵥ v) (fun v => w ⬝ᵥ v) 18 8 p = true) :
    HasOrder p (stages M) (weights w) := by
  have m :
      M.map (Int.castRingHom ℚ) = (Int.castRingHom ℚ) 18 • stages M := by
    funext i j
    change (M i j : ℚ) = (18 : ℚ)*((M i j : ℚ)/18)
    ring
  have b :
      (Int.castRingHom ℚ) ∘ w = (Int.castRingHom ℚ) 8 • weights w := by
    funext i
    change (w i : ℚ) = (8 : ℚ)*((w i : ℚ)/8)
    ring
  exact hasOrder_of_scaled_check (A := M) (b := w) (d := 18) (e := 8) (p := p)
    (Int.castRingHom ℚ) (fun _ => rfl) (fun _ => rfl) m b
    (isUnit_iff_ne_zero.mpr (by decide +kernel))
    (isUnit_iff_ne_zero.mpr (by decide +kernel)) h

end RationalStrictSDIRKNumerators

namespace RationalStrictSDIRK3

def AInt : Matrix (Fin 3) (Fin 3) ℤ :=
  !![3,0,0;
     6,3,0;
     8,4,3]

def bInt : Fin 3 → ℤ := ![3,2,3]

def A : Matrix (Fin 3) (Fin 3) ℚ := RationalStrictSDIRKNumerators.stages AInt
def b : Fin 3 → ℚ := RationalStrictSDIRKNumerators.weights bInt

theorem lowerTriangular : A.IsLowerTriangular := by
  change ∀ i j : Fin 3, i < j → A i j = 0
  intro i j
  fin_cases i <;> fin_cases j <;> decide +kernel

theorem common_diagonal : ∀ i, A i i = 1/6 := by decide +kernel
theorem positive_weights : ∀ i, 0 < b i := by decide +kernel

private theorem checked :
    checkScaledOrder (fun v => AInt *ᵥ v) (fun v => bInt ⬝ᵥ v) 18 8 3 = true := by
  decide +kernel

theorem order_three : HasOrder 3 A b :=
  RationalStrictSDIRKNumerators.order_of_check AInt bInt checked

theorem fourth_tall_weight : b ⬝ᵥ Φ (tallTree 4) A = 5/108 := by decide +kernel

theorem not_order_four : ¬ HasOrder 4 A b := by
  intro h
  have paid := h (tallTree 4) (by rw [order_tallTree]; decide)
  rw [fourth_tall_weight] at paid
  exact (by decide +kernel : ((tallTree 4).factorial : ℚ) * (5/108) ≠ 1) paid

end RationalStrictSDIRK3

namespace RationalStrictSDIRK4

def AInt : Matrix (Fin 4) (Fin 4) ℤ :=
  !![3,0,0,0;
     6,3,0,0;
     12,-6,3,0;
     6,4,2,3]

def bInt : Fin 4 → ℤ := ![3,1,1,3]

def A : Matrix (Fin 4) (Fin 4) ℚ := RationalStrictSDIRKNumerators.stages AInt
def b : Fin 4 → ℚ := RationalStrictSDIRKNumerators.weights bInt

theorem lowerTriangular : A.IsLowerTriangular := by
  change ∀ i j : Fin 4, i < j → A i j = 0
  intro i j
  fin_cases i <;> fin_cases j <;> decide +kernel

theorem common_diagonal : ∀ i, A i i = 1/6 := by decide +kernel
theorem positive_weights : ∀ i, 0 < b i := by decide +kernel

private theorem checked :
    checkScaledOrder (fun v => AInt *ᵥ v) (fun v => bInt ⬝ᵥ v) 18 8 4 = true := by
  decide +kernel

theorem order_four : HasOrder 4 A b :=
  RationalStrictSDIRKNumerators.order_of_check AInt bInt checked

theorem fifth_tall_weight : b ⬝ᵥ Φ (tallTree 5) A = 11/1296 := by decide +kernel

theorem not_order_five : ¬ HasOrder 5 A b := by
  intro h
  have paid := h (tallTree 5) (by rw [order_tallTree]; decide)
  rw [fifth_tall_weight] at paid
  exact (by decide +kernel : ((tallTree 5).factorial : ℚ) * (11/1296) ≠ 1) paid

end RationalStrictSDIRK4

theorem exists_rational_strictSDIRK_exact_three :
    ∃ (A : Matrix (Fin 3) (Fin 3) ℚ) (b : Fin 3 → ℚ),
      A.IsLowerTriangular ∧ (∀ i, A i i = 1/6) ∧ (1/6 : ℚ) ≠ 0 ∧
        (∀ i, 0 < b i) ∧ HasOrder 3 A b ∧ ¬ HasOrder 4 A b :=
  ⟨RationalStrictSDIRK3.A, RationalStrictSDIRK3.b, RationalStrictSDIRK3.lowerTriangular,
    RationalStrictSDIRK3.common_diagonal, by decide +kernel, RationalStrictSDIRK3.positive_weights,
    RationalStrictSDIRK3.order_three, RationalStrictSDIRK3.not_order_four⟩

theorem exists_rational_strictSDIRK_exact_four :
    ∃ (A : Matrix (Fin 4) (Fin 4) ℚ) (b : Fin 4 → ℚ),
      A.IsLowerTriangular ∧ (∀ i, A i i = 1/6) ∧ (1/6 : ℚ) ≠ 0 ∧
        (∀ i, 0 < b i) ∧ HasOrder 4 A b ∧ ¬ HasOrder 5 A b :=
  ⟨RationalStrictSDIRK4.A, RationalStrictSDIRK4.b, RationalStrictSDIRK4.lowerTriangular,
    RationalStrictSDIRK4.common_diagonal, by decide +kernel, RationalStrictSDIRK4.positive_weights,
    RationalStrictSDIRK4.order_four, RationalStrictSDIRK4.not_order_five⟩

private theorem lift_rational_exact_strictSDIRK {s p : ℕ}
    {A : Matrix (Fin s) (Fin s) ℚ} {b : Fin s → ℚ}
    (tri : A.IsLowerTriangular) (diag : ∀ i, A i i = 1/6)
    (ho : HasOrder p A b) (fail : ¬ HasOrder (p+1) A b)
    (K : Type*) [Field K] [CharZero K] :
    ∃ (T : Matrix (Fin s) (Fin s) K) (w : Fin s → K) (γ : K),
      T.IsLowerTriangular ∧ (∀ i, T i i = γ) ∧ γ ≠ 0 ∧
        HasOrder p T w ∧ ¬ HasOrder (p+1) T w := by
  let f := Rat.castHom K
  refine ⟨A.map f, f ∘ b, f (1/6), tri.map f, fun i => congrArg f (diag i), ?_, ho.map f,
    fun h => fail ((hasOrder_map_iff f.injective).mp h)⟩
  intro h
  exact (by decide +kernel : (1/6 : ℚ) ≠ 0) (f.injective (h.trans (map_zero f).symm))

theorem exists_strictSDIRK_exact_three_via_rational (K : Type*) [Field K] [CharZero K] :
    ∃ (T : Matrix (Fin 3) (Fin 3) K) (w : Fin 3 → K) (γ : K),
      T.IsLowerTriangular ∧ (∀ i, T i i = γ) ∧ γ ≠ 0 ∧
        HasOrder 3 T w ∧ ¬ HasOrder 4 T w :=
  lift_rational_exact_strictSDIRK RationalStrictSDIRK3.lowerTriangular RationalStrictSDIRK3.common_diagonal
    RationalStrictSDIRK3.order_three RationalStrictSDIRK3.not_order_four K

theorem exists_strictSDIRK_exact_four_via_rational (K : Type*) [Field K] [CharZero K] :
    ∃ (T : Matrix (Fin 4) (Fin 4) K) (w : Fin 4 → K) (γ : K),
      T.IsLowerTriangular ∧ (∀ i, T i i = γ) ∧ γ ≠ 0 ∧
        HasOrder 4 T w ∧ ¬ HasOrder 5 T w :=
  lift_rational_exact_strictSDIRK RationalStrictSDIRK4.lowerTriangular RationalStrictSDIRK4.common_diagonal
    RationalStrictSDIRK4.order_four RationalStrictSDIRK4.not_order_five K

end RKResearch.Certified
