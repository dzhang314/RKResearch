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

/-- Cutting the branch contributes exactly the branch's complete factorial. -/
theorem factorial_butcherProduct_cut (t u : FiniteRootedTree) :
    (((u ◂ t).factorial : ℕ+) : ℕ) =
      ((u.addBush (t.order : ℕ)).factorial : ℕ) * (t.factorial : ℕ) := by
  rw [factorial_addBush]
  simp only [factorial, forestFactorial, order, PNat.add_coe, PNat.mul_coe, mul_assoc]

end FiniteRootedTree

variable {ι R : Type*} [Fintype ι] [CommSemiring R]

namespace HasOrder

variable {A : Matrix ι ι R} {b : ι → R} {p : ℕ}

/-- Tree order supplies its own factorial unit: its inverse is the tree weight. -/
theorem factorial_isUnit (h : HasOrder p A b) (t : FiniteRootedTree)
    (ht : (t.order : ℕ) ≤ p) : IsUnit (t.factorial : R) :=
  IsUnit.of_mul_eq_one _ (h t ht)

/-- Replace a branch by its order-many leaves. No field or unit assumptions
are added to the original order conditions. -/
theorem balanced_root_cut (h : HasOrder p A b) (t u : FiniteRootedTree)
    (hp : (u.order : ℕ) + (t.order : ℕ) ≤ p) :
    (t.factorial : R) * (b ⬝ᵥ Φ (u ◂ t) A) =
      b ⬝ᵥ Φ (u.addBush (t.order : ℕ)) A := by
  let v := u.addBush (t.order : ℕ)
  have hv : (v.order : ℕ) ≤ p := by simpa only [v, order_addBush] using hp
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
theorem HasOrder.rootStageResidual_pairing (h : HasOrder p A b) (t u : FiniteRootedTree)
    (hp : (u.order : ℕ) + (t.order : ℕ) ≤ p) :
    b ⬝ᵥ (rootStageResidual A t * Φ u A) = 0 := by
  have hcut := h.balanced_root_cut t u hp
  rw [Φ_addBush, Φ] at hcut
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
