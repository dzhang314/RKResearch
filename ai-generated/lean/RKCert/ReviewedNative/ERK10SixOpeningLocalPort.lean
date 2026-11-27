module

public import RKCert.ReviewedNative.FiniteScaledOrderCheck
public import Mathlib.Algebra.Field.Rat
public import Mathlib.LinearAlgebra.Matrix.Block

import Mathlib.LinearAlgebra.Matrix.Notation
import Mathlib.Tactic.FinCases
import Mathlib.Tactic.Ring

@[expose] public section

namespace RKResearch.Certified.ERK10SixOpeningLocalPort

open RKResearch FiniteRootedTree
open scoped Matrix FiniteRootedTree

def AInt : Matrix (Fin 6) (Fin 6) ℤ :=
  !![0,0,0,0,0,0;
     648,0,0,0,0,0;
     0,1296,0,0,0,0;
     486,0,1458,0,0,0;
     4860,0,-18225,18225,0,0;
     -21480,0,91800,-72800,8960,0]

def bInt : Fin 6 → ℤ := ![105,0,0,500,448,81]
def A : Matrix (Fin 6) (Fin 6) ℚ := Matrix.of fun i j => (AInt i j : ℚ) / 6480
def b : Fin 6 → ℚ := fun i => (bInt i : ℚ) / 1134

theorem strict : ∀ i j : Fin 6, i ≤ j → A i j = 0 := by
  intro i j
  fin_cases i <;> fin_cases j <;> decide +kernel

set_option maxHeartbeats 4000000 in
private theorem checked :
    checkScaledOrder (fun v => AInt *ᵥ v) (fun v => bInt ⬝ᵥ v) 6480 1134 5 = true := by
  decide +kernel

theorem orderFive : HasOrder 5 A b := by
  refine hasOrder_of_scaled_check (A := AInt) (b := bInt)
    (d := 6480) (e := 1134) (p := 5)
    (Int.castRingHom ℚ) (fun _ => rfl) (fun _ => rfl) ?_ ?_
    (isUnit_iff_ne_zero.mpr (by decide +kernel))
    (isUnit_iff_ne_zero.mpr (by decide +kernel)) checked
  · funext i j
    change (AInt i j : ℚ) = (6480 : ℚ) * ((AInt i j : ℚ) / 6480)
    exact (mul_div_cancel₀ (AInt i j : ℚ) (by decide +kernel : (6480 : ℚ) ≠ 0)).symm
  · funext i
    change (bInt i : ℚ) = (1134 : ℚ) * ((bInt i : ℚ) / 1134)
    exact (mul_div_cancel₀ (bInt i : ℚ) (by decide +kernel : (1134 : ℚ) ≠ 0)).symm

set_option maxHeartbeats 4000000 in
theorem sixthTall :
    b ⬝ᵥ Φ (tallTree 6) A = (1 / 800 : ℚ) := by decide +kernel

theorem notOrderSix : ¬ HasOrder 6 A b := by
  intro h
  have hh := h (tallTree 6) (by rw [order_tallTree]; decide)
  rw [sixthTall] at hh
  exact (by decide +kernel : ((tallTree 6).factorial : ℚ) * (1/800 : ℚ) ≠ 1) hh

/-- The seventh physical stage is simply the already checked six-stage
output; its own strict row is b with no self tap. -/
def A7 : Matrix (Fin 6 ⊕ Unit) (Fin 6 ⊕ Unit) ℚ :=
  Matrix.fromBlocks A 0 (fun _ j => b j) 0

theorem phiPrefix (t : FiniteRootedTree) :
    Φ t A7 ∘ Sum.inl = Φ t A := by
  induction t with
  | leaf => rfl
  | butcherProduct u v hu hv =>
    funext i
    have hᵤ : Φ u A7 (.inl i) = Φ u A i := congrFun hu i
    change Φ u A7 (.inl i) * (A7 *ᵥ Φ v A7) (.inl i) =
      Φ u A i * (A *ᵥ Φ v A) i
    rw [hᵤ]
    congr 1
    have hᵥ : ∀ j, Φ v A7 (.inl j) = Φ v A j := congrFun hv
    simp only [Matrix.mulVec, dotProduct, Fintype.sum_sum_type]
    have hzero (a : Unit) : A7 (.inl i) (.inr a) = 0 := by
      rfl
    simp only [hᵥ, hzero, zero_mul, Finset.sum_const_zero, add_zero]
    apply Finset.sum_congr rfl
    intro j _
    rw [show A7 (.inl i) (.inl j) = A i j by rfl]

theorem portPrimitive (t : FiniteRootedTree) :
    (A7 *ᵥ Φ t A7) (.inr Unit.unit) = b ⬝ᵥ Φ t A := by
  have hh : ∀ j, Φ t A7 (.inl j) = Φ t A j := congrFun (phiPrefix t)
  simp only [Matrix.mulVec, dotProduct, Fintype.sum_sum_type]
  have hzero (a : Unit) : A7 (.inr Unit.unit) (.inr a) = 0 := by
    rfl
  simp only [hh, hzero, zero_mul, Finset.sum_const_zero, add_zero]
  rfl

/-- Every actual derivative at the newly appended unit-clock stage has
its correctly normalized local value through size six. -/
theorem localThroughSix (t : FiniteRootedTree) (ht : (t.order : ℕ) ≤ 6) :
    (t.forestFactorial : ℚ) * Φ t A7 (.inr Unit.unit) = 1 := by
  induction t with
  | leaf => simp [FiniteRootedTree.forestFactorial, Φ]
  | butcherProduct u v hu _ =>
    have hs : ((u ◂ v).order : ℕ) = (u.order : ℕ) + (v.order : ℕ) := by
      simp only [FiniteRootedTree.order, PNat.add_coe]
    have hp₁ := u.order.pos
    have hp₂ := v.order.pos
    have h₁ : (u.order : ℕ) ≤ 6 := by omega
    have h₂ : (v.order : ℕ) ≤ 5 := by omega
    have e₁ := hu h₁
    have e₂ := orderFive v h₂
    have hf : ((u ◂ v).forestFactorial : ℚ) =
        (u.forestFactorial : ℚ) * (v.factorial : ℚ) := by
      simp [FiniteRootedTree.forestFactorial, FiniteRootedTree.factorial, PNat.mul_coe]
    rw [hf]
    simp only [Φ, Pi.mul_apply, portPrimitive]
    calc
      (u.forestFactorial : ℚ) * (v.factorial : ℚ) *
          (Φ u A7 (.inr Unit.unit) * (b ⬝ᵥ Φ v A)) =
        ((u.forestFactorial : ℚ) * Φ u A7 (.inr Unit.unit)) *
          ((v.factorial : ℚ) * (b ⬝ᵥ Φ v A)) := by ring
      _ = 1 := by rw [e₁, e₂, one_mul]

end RKResearch.Certified.ERK10SixOpeningLocalPort
