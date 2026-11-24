module

public import RKCert.ReviewedNative.FiniteScaledOrderCheck
public import RKCert.ReviewedNative.DIRKOrderSix

import Mathlib.LinearAlgebra.Matrix.Notation
import Mathlib.Tactic.FinCases
import Mathlib.Tactic.FieldSimp

@[expose] public section

/-! # A rational five-stage, sixth-order Boole-grid DIRK

The order conditions are checked in the reviewed finite tree catalogue.
The ordinary matrix is lower triangular, not strict SDIRK: its first and
last diagonals are zero while the second is nonzero. -/

namespace RKResearch.Certified.BooleDIRK56

open FiniteRootedTree
open scoped Matrix

/-- The exact stage matrix with common denominator 168 cleared. -/
def AInt : Matrix (Fin 5) (Fin 5) ℤ :=
  !![0,0,0,0,0;
    21,21,0,0,0;
    -14,112,-14,0,0;
    21,42,42,21,0;
    0,96,-24,96,0]

def bInt : Fin 5 → ℤ := ![7,32,12,32,7]

def A : Matrix (Fin 5) (Fin 5) ℚ := Matrix.of fun i j => (AInt i j : ℚ)/168
def b (i : Fin 5) : ℚ := (bInt i : ℚ)/90

def c : Fin 5 → ℚ := ![0,1/4,1/2,3/4,1]

/-- Multiplication considers only the actual nonzero entries. -/
def act (x : Fin 5 → ℤ) : Fin 5 → ℤ :=
  ![0,21*x 0+21*x 1,-14*x 0+112*x 1-14*x 2,
    21*x 0+42*x 1+42*x 2+21*x 3,96*x 1-24*x 2+96*x 3]

def weigh (x : Fin 5 → ℤ) : ℤ := 7*x 0+32*x 1+12*x 2+32*x 3+7*x 4

theorem act_eq (x : Fin 5 → ℤ) : act x = AInt *ᵥ x := by
  funext i
  fin_cases i <;> simp [act,AInt,Matrix.mulVec,dotProduct,Fin.sum_univ_succ] <;> ring

theorem weigh_eq (x : Fin 5 → ℤ) : weigh x = bInt ⬝ᵥ x := by
  simp [weigh,bInt,dotProduct,Fin.sum_univ_succ]
  ring

theorem lowerTriangular : A.IsLowerTriangular := by
  intro i j hij
  change i.val < j.val at hij
  fin_cases i <;> fin_cases j <;> first | (norm_num [A,AInt]; done) | norm_num at hij

theorem diagonal_not_constant : ¬ ∃ γ : ℚ, ∀ i, A i i = γ := by
  rintro ⟨γ,hγ⟩
  have h := (hγ (0 : Fin 5)).trans (hγ (1 : Fin 5)).symm
  norm_num [A,AInt] at h

theorem row_sums : A *ᵥ 1 = c := by
  exact funext (by decide +kernel : ∀ i : Fin 5, (A *ᵥ 1) i = c i)

private theorem scale_A :
    AInt.map (Int.castRingHom ℚ) = (Int.castRingHom ℚ) 168 • A := by
  funext i j
  change (AInt i j:ℚ) = (168:ℚ)*((AInt i j:ℚ)/168)
  ring

private theorem scale_b : (Int.castRingHom ℚ) ∘ bInt = (Int.castRingHom ℚ) 90 • b := by
  funext i
  change (bInt i:ℚ) = (90:ℚ)*((bInt i:ℚ)/90)
  ring

set_option maxHeartbeats 5000000 in
set_option maxRecDepth 5000 in
private theorem checked : checkScaledOrder act weigh 168 90 6 = true := by
  decide +kernel

theorem order_six : HasOrder 6 A b :=
  hasOrder_of_scaled_check (Int.castRingHom ℚ) act_eq weigh_eq scale_A scale_b
    (by norm_num) (by norm_num) checked

/-- The order-seven bush has factorial-scaled weight 385/384. -/
theorem seventh_bush_scaled :
    384 * (((bushyTree 7).factorial : ℚ) * (b ⬝ᵥ Φ (bushyTree 7) A)) = 385 := by
  rw [factorial_bushyTree,Φ_bushyTree,row_sums]
  decide +kernel

section Specialization

variable {K : Type*} [Field K] [CharZero K]

/-- The rational seventh-order failure survives in every characteristic-zero field. -/
theorem not_order_seven_map (f : ℚ →+* K) : ¬ HasOrder 7 (A.map f) (f ∘ b) := by
  intro h
  have ht := h (bushyTree 7) (by rw [order_bushyTree]; decide)
  have hh : (384:K) * (((bushyTree 7).factorial : K) *
      ((f ∘ b) ⬝ᵥ Φ (bushyTree 7) (A.map f))) = 385 := by
    simpa only [map_mul,map_ofNat,map_natCast,RingHom.map_dotProduct,map_Φ_coefficients]
      using congrArg f seventh_bush_scaled
  rw [ht,mul_one] at hh
  norm_num at hh

theorem exists_exact_order_six :
    ∃ (U : Matrix (Fin 5) (Fin 5) K) (w : Fin 5 → K),
      U.IsLowerTriangular ∧ HasOrder 6 U w ∧ ¬ HasOrder 7 U w := by
  let f := Rat.castHom K
  exact ⟨A.map f,f ∘ b,lowerTriangular.map f,order_six.map_coefficients f,not_order_seven_map f⟩

end Specialization

end RKResearch.Certified.BooleDIRK56

namespace RKResearch.Certified

/-- Five is the minimum number of physical stages of a lower triangular
classical order-six tableau over any characteristic-zero field. -/
theorem dirk_order_six_isLeast_charZero_field (K : Type*) [Field K] [CharZero K] :
    IsLeast {s : ℕ | ∃ (A : Matrix (Fin s) (Fin s) K) (b : Fin s → K),
      A.IsLowerTriangular ∧ HasOrder 6 A b} 5 := by
  obtain ⟨A,b,ht,ho,_⟩ := BooleDIRK56.exists_exact_order_six (K := K)
  refine ⟨⟨A,b,ht,ho⟩,?_⟩
  rintro s ⟨U,w,hu,hw⟩
  exact hw.dirk_order_six_stages_field hu

end RKResearch.Certified
