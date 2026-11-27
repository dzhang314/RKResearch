module

public import RKCert.ReviewedNative.FiniteOrderCheck
public import RKCert.ReviewedNative.GradedProducts
public import RKCert.Research.SDIRKSevenChristoffelCentered
public import RKCert.Research.SDIRKSevenChristoffelScalar
public import Mathlib.Algebra.Field.ZMod
public import Mathlib.LinearAlgebra.Matrix.Notation
public import Mathlib.LinearAlgebra.Matrix.Block
import Mathlib.Tactic.FinCases
import Mathlib.Tactic.FieldSimp
import Mathlib.Tactic.LinearCombination
import Mathlib.Tactic.Ring

@[expose] public section

/-! # Two alternative rational first-clock schedules and exact F19 controls -/

namespace RKResearch.Certified.SDIRKSevenChristoffelAlternativeF19

open RKResearch Graded FiniteRootedTree
open scoped Matrix
abbrev K := ZMod 19

def qTap (x : ℚ) : ℚ := 2*(x^2-3*x+1)/(x^2-4*x+2)
def qFirst (x : ℚ) : ℚ := x*(x-2)/(2*(x-1))

theorem q_profile_schedule {x : ℚ} (h₁ : x≠1) (hM : x^2-4*x+2≠0) :
    (2-qTap x)*qFirst x+qTap x-1=0 ∧
      x^2-3*x+1-qTap x*(x^2-4*x+2)/2=0 := by
  have g₁ := sub_ne_zero.mpr h₁
  let M := x^2-4*x+2
  have hh : M≠0 := hM
  have hT : qTap x*M=2*(x^2-3*x+1) := by
    unfold qTap
    exact div_mul_cancel₀ _ hM
  have h₂ : (2-qTap x)*M=2*(1-x) := by
    simp only [M] at hT ⊢
    linear_combination -hT
  have hF : 2*(1-x)*qFirst x = -x*(x-2) := by
    unfold qFirst
    field_simp [g₁]
    ring
  constructor
  · apply mul_left_cancel₀ (a:=M) hh
    calc
      M*((2-qTap x)*qFirst x+qTap x-1) =
          ((2-qTap x)*M)*qFirst x+(qTap x*M-M) := by ring
      _ = M*0 := by rw [h₂,hT,hF]; dsimp [M]; ring
  · change x^2-3*x+1-qTap x*M/2=0
    rw [hT]
    ring

namespace H2

def A : Matrix (Fin 9) (Fin 9) K := !![15,0,0,0,0,0,0,0,0;
     11,15,0,0,0,0,0,0,0;
     10,1,15,0,0,0,0,0,0;
     7,12,12,15,0,0,0,0,0;
     12,6,8,8,15,0,0,0,0;
     12,3,1,0,7,15,0,0,0;
     12,16,4,9,15,4,15,0,0;
     8,6,8,17,17,8,18,15,0;
     10,1,4,1,14,17,13,6,15]
def b : Fin 9→K := ![0,0,8,8,3,2,16,14,7]
def y (i : Fin 9) : K := 14*(1-(A *ᵥ 1) i)
def t : K := 14*A 1 0

theorem lower_triangular : A.IsLowerTriangular := by
  intro i j h
  change i.val < j.val at h
  fin_cases i <;> fin_cases j <;> first | (norm_num at h; done) | decide +kernel

theorem diagonal : ∀ i : Fin 9,A i i=(15:K) := by decide +kernel
theorem mask : ∀ i : Fin 9,b i=0 ↔ i=0 ∨ i=1 := by decide +kernel

theorem distinct_active (i j : Fin 9) :
    (2 : ℕ) ≤ i.val → (2 : ℕ) ≤ j.val → y i=y j → i=j := by
  exact (by decide +kernel :
    ∀ i j : Fin 9,(2 : ℕ) ≤ i.val → (2 : ℕ) ≤ j.val → y i=y j → i=j) i j

theorem schedule :
    y 3=16 ∧ t=2 ∧ y 5=14 ∧ 14-y 2=1+t ∧
    b 3*SDIRKSevenChristoffelScalar.kernelFour (11*y 3-1) (11*y 3-1)=4 := by
  decide +kernel

set_option maxHeartbeats 6000000 in
set_option maxRecDepth 30000 in
theorem order_seven : HasOrder 7 A b := by
  apply (checkOrder_iff A b 7).mp
  decide +kernel

def bad := bushyTree 8

theorem bad_size : bad.order=8 := by decide +kernel
theorem bad_value : (bad.factorial:K)*(b ⬝ᵥ Φ bad A)=(7:K) := by decide +kernel

theorem not_order_eight : ¬HasOrder 8 A b := by
  intro h
  have e := h bad (by rw [bad_size]; decide)
  rw [bad_value] at e
  exact (by decide +kernel : (7:K)≠1) e

theorem strict_unit : IsUnit (15:K) := by
  let : Fact (Nat.Prime 19) := ⟨by decide⟩
  exact isUnit_iff_ne_zero.mpr (by decide +kernel)

end H2

namespace QProfile

def A : Matrix (Fin 9) (Fin 9) K := !![14,0,0,0,0,0,0,0,0;
     10,14,0,0,0,0,0,0,0;
     11,14,14,0,0,0,0,0,0;
     6,9,16,14,0,0,0,0,0;
     13,13,4,17,14,0,0,0,0;
     0,12,15,12,6,14,0,0,0;
     16,16,10,12,12,5,14,0,0;
     11,5,9,11,14,11,18,14,0;
     13,7,17,5,6,6,12,2,14]
def b : Fin 9→K := ![0,0,1,7,10,15,10,3,12]
def y (i : Fin 9) : K := 15*(1-(A *ᵥ 1) i)
def t : K := 15*A 1 0

theorem lower_triangular : A.IsLowerTriangular := by
  intro i j h
  change i.val < j.val at h
  fin_cases i <;> fin_cases j <;> first | (norm_num at h; done) | decide +kernel

theorem diagonal : ∀ i : Fin 9,A i i=(14:K) := by decide +kernel
theorem mask : ∀ i : Fin 9,b i=0 ↔ i=0 ∨ i=1 := by decide +kernel

theorem distinct_active (i j : Fin 9) :
    (2 : ℕ) ≤ i.val → (2 : ℕ) ≤ j.val → y i=y j → i=j := by
  exact (by decide +kernel :
    ∀ i j : Fin 9,(2 : ℕ) ≤ i.val → (2 : ℕ) ≤ j.val → y i=y j → i=j) i j

theorem schedule :
    y 3=5 ∧ t=17 ∧ y 2=0 ∧ (2-t)*(15-y 2)=1-t ∧
    b 3*SDIRKSevenChristoffelScalar.kernelFour (9*y 3-1) (9*y 3-1)=4 := by
  decide +kernel

set_option maxHeartbeats 6000000 in
set_option maxRecDepth 30000 in
theorem order_seven : HasOrder 7 A b := by
  apply (checkOrder_iff A b 7).mp
  decide +kernel

def bad := bushyTree 8

theorem bad_size : bad.order=8 := by decide +kernel
theorem bad_value : (bad.factorial:K)*(b ⬝ᵥ Φ bad A)=(7:K) := by decide +kernel

theorem not_order_eight : ¬HasOrder 8 A b := by
  intro h
  have e := h bad (by rw [bad_size]; decide)
  rw [bad_value] at e
  exact (by decide +kernel : (7:K)≠1) e

theorem strict_unit : IsUnit (14:K) := by
  let : Fact (Nat.Prime 19) := ⟨by decide⟩
  exact isUnit_iff_ne_zero.mpr (by decide +kernel)

end QProfile

end RKResearch.Certified.SDIRKSevenChristoffelAlternativeF19
