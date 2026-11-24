module

public import RKResearch.OrderConditions

public section

/-! # Native root-cut payment

All tree terms below are the reviewed `FiniteRootedTree`. Replacing one
branch by the same number of leaves preserves the root order and removes
exactly that branch's tree factorial. The comparison works without
division, even with zero divisors. -/

namespace RKResearch

open FiniteRootedTree
open scoped Matrix

namespace FiniteRootedTree

/-- Attach a batch of leaf children to an existing root. -/
@[expose] def appendLeafBranches : ℕ → FiniteRootedTree → FiniteRootedTree
  | 0, t => t
  | n + 1, t => appendLeafBranches n t ◂ leaf

@[simp] theorem order_appendLeafBranches (n : ℕ) (t : FiniteRootedTree) :
    ((appendLeafBranches n t).order : ℕ) = (t.order : ℕ) + n := by
  induction n with
  | zero => simp [appendLeafBranches]
  | succ n ih =>
    simp only [appendLeafBranches, order, PNat.add_coe, PNat.one_coe, ih]
    rfl

@[simp] theorem forestFactorial_appendLeafBranches (n : ℕ) (t : FiniteRootedTree) :
    (appendLeafBranches n t).forestFactorial = t.forestFactorial := by
  induction n with
  | zero => rfl
  | succ n ih => simp only [appendLeafBranches, forestFactorial, order, mul_one, ih]

/-- Cutting the branch contributes exactly the branch's complete factorial. -/
theorem factorial_butcherProduct_cut (t u : FiniteRootedTree) :
    (((u ◂ t).factorial : ℕ+) : ℕ) =
      ((appendLeafBranches (t.order : ℕ) u).factorial : ℕ) * (t.factorial : ℕ) := by
  simp only [factorial, forestFactorial, order, PNat.add_coe, PNat.mul_coe,
    order_appendLeafBranches, forestFactorial_appendLeafBranches, mul_assoc]

end FiniteRootedTree

variable {ι R : Type*} [Fintype ι] [CommSemiring R]

/-- Leaf attachment is multiplication by the reviewed matrix row-sum. -/
theorem Φ_appendLeafBranches (A : Matrix ι ι R) (n : ℕ) (t : FiniteRootedTree) :
    Φ (appendLeafBranches n t) A = Φ t A * (A *ᵥ (1 : ι → R)) ^ n := by
  induction n with
  | zero => simp [appendLeafBranches]
  | succ n ih => simp only [appendLeafBranches, Φ, ih, pow_succ, mul_assoc]

namespace HasOrder

variable {A : Matrix ι ι R} {b : ι → R} {p : ℕ}

/-- Tree order supplies its own factorial unit: its inverse is the tree weight. -/
theorem factorial_isUnit (h : HasOrder A b p) (t : FiniteRootedTree)
    (ht : (t.order : ℕ) ≤ p) : IsUnit (t.factorial : R) :=
  IsUnit.of_mul_eq_one _ (h t ht)

/-- Replace a branch by its order-many leaves. No field or unit assumptions
are added to the original order conditions. -/
theorem balanced_root_cut (h : HasOrder A b p) (t u : FiniteRootedTree)
    (hp : (u.order : ℕ) + (t.order : ℕ) ≤ p) :
    (t.factorial : R) * (b ⬝ᵥ Φ (u ◂ t) A) =
      b ⬝ᵥ Φ (appendLeafBranches (t.order : ℕ) u) A := by
  let v := appendLeafBranches (t.order : ℕ) u
  have hv : (v.order : ℕ) ≤ p := by simpa [v] using hp
  have hu : (((u ◂ t).order : ℕ+) : ℕ) ≤ p := by
    simpa only [order, PNat.add_coe] using hp
  have hfac :
      ((u ◂ t).factorial : R) = (v.factorial : R) * (t.factorial : R) := by
    rw [factorial_butcherProduct_cut, Nat.cast_mul]
  apply (h.factorial_isUnit v hv).mul_left_cancel
  rw [← mul_assoc, ← hfac, h (u ◂ t) hu, h v hv]

end HasOrder

section Ring

variable {ι R : Type*} [Fintype ι] [CommRing R]

/-- Denominator-cleared residual of precisely the stage integral represented
by a branch of the reviewed tree. -/
@[expose] def rootStageResidual (A : Matrix ι ι R) (t : FiniteRootedTree) : ι → R :=
  fun i => (t.factorial : R) * (A *ᵥ Φ t A) i - (A *ᵥ (1 : ι → R)) i ^ (t.order : ℕ)

variable {A : Matrix ι ι R} {b : ι → R} {p : ℕ}

/-- Exact paired residual payment against any partner rooted tree. -/
theorem HasOrder.rootStageResidual_pairing (h : HasOrder A b p) (t u : FiniteRootedTree)
    (hp : (u.order : ℕ) + (t.order : ℕ) ≤ p) :
    b ⬝ᵥ (rootStageResidual A t * Φ u A) = 0 := by
  have hcut := h.balanced_root_cut t u hp
  rw [Φ_appendLeafBranches, Φ] at hcut
  rw [dotProduct, dotProduct, Finset.mul_sum] at hcut
  rw [← sub_eq_zero, ← Finset.sum_sub_distrib] at hcut
  change (∑ i, b i * (rootStageResidual A t i * Φ u A i)) = 0
  rw [← hcut]
  apply Finset.sum_congr rfl
  intro i _
  simp only [rootStageResidual, Pi.mul_apply, Pi.pow_apply, sub_mul, mul_sub]
  ac_rfl

end Ring

end RKResearch
