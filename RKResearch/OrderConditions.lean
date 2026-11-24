module

public import Mathlib.Data.Matrix.Mul
public import RKResearch.FiniteRootedTree

public section

namespace RKResearch

open FiniteRootedTree
open scoped Matrix

variable {ι R : Type _} [Fintype ι] [CommSemiring R]

@[expose, simp] def Φ : FiniteRootedTree → Matrix ι ι R → ι → R
  | leaf, _ => 1
  | base ◂ branch, A => Φ base A * (A *ᵥ Φ branch A)

theorem Φ_branch_swap (t u v : FiniteRootedTree) (A : Matrix ι ι R) :
    Φ ((t ◂ u) ◂ v) A = Φ ((t ◂ v) ◂ u) A := by apply mul_right_comm

theorem Φ_addBush (t : FiniteRootedTree) (k : ℕ) (A : Matrix ι ι R) :
    Φ (t.addBush k) A = Φ t A * (A *ᵥ 1) ^ k := by
  induction k with
  | zero => simp only [addBush, pow_zero, mul_one]
  | succ k ih => simp only [addBush, Φ, ih, pow_succ, mul_assoc]

theorem Φ_bushyTree (n : ℕ+) (A : Matrix ι ι R) :
    Φ (bushyTree n) A = (A *ᵥ 1) ^ ((n : ℕ) - 1) := by
  simp only [bushyTree, PNat.natPred, Φ_addBush, Φ, one_mul]

theorem Φ_tallTree [DecidableEq ι] (n : ℕ+) (A : Matrix ι ι R) :
    Φ (tallTree n) A = A ^ ((n : ℕ) - 1) *ᵥ 1 := by
  unfold tallTree
  induction n <;> (dsimp; simp [*, mul_pow_sub_one])

@[expose] def HasOrder (p : ℕ) (A : Matrix ι ι R) (b : ι → R) : Prop :=
  ∀ t : FiniteRootedTree, t.order ≤ p → (t.factorial : R) * (b ⬝ᵥ Φ t A) = 1

@[expose] def HasQuadratureOrder (p : ℕ) (b c : ι → R) : Prop :=
  ∀ k < p, k.succ * (b ⬝ᵥ c ^ k) = 1

theorem HasOrder.hasQuadratureOrder {p : ℕ} {A : Matrix ι ι R} {b : ι → R}
    (h : HasOrder p A b) : HasQuadratureOrder p b (A *ᵥ 1) := by
  intro k
  specialize h (bushyTree k.succPNat)
  simp only [order_bushyTree, factorial_bushyTree, Φ_bushyTree] at h
  assumption

end RKResearch
