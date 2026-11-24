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
  Φ ((t ◂ u) ◂ v) A = Φ ((t ◂ v) ◂ u) A := mul_right_comm _ _ _

theorem Φ_tallTree [DecidableEq ι] (n : ℕ+) (A : Matrix ι ι R) :
    Φ (tallTree n) A = A ^ ((n : ℕ) - 1) *ᵥ 1 := by
  induction n <;> simp_all [mul_pow_sub_one]

theorem Φ_bushyTree (n : ℕ+) (A : Matrix ι ι R) :
    Φ (bushyTree n) A = (A *ᵥ 1) ^ ((n : ℕ) - 1) := by
  induction n <;> simp_all [pow_sub_one_mul]

@[expose] def HasOrder (A : Matrix ι ι R) (b : ι → R) (p : ℕ) : Prop :=
  ∀ t : FiniteRootedTree, t.order ≤ p → (t.factorial : R) * (b ⬝ᵥ Φ t A) = 1

end RKResearch
