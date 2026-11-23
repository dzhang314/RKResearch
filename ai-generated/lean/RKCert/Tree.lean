module

public import Mathlib.Algebra.BigOperators.Ring.Finset
public import Mathlib.Data.Nat.Factorial.Basic
public import Mathlib.Data.Fintype.Basic
public import Mathlib.Data.Fintype.Fin

@[expose] public section

/-!
# Algebraic Runge–Kutta order conditions

`Tree` is an ordered presentation of finite, nonempty rooted trees. `attach c r`
adds `c` as the first child of the root of `r`; it does **not** add a new vertex.
The child order is immaterial for the commutative coefficient types used here.
`HasTreeOrderAtLeast A b p` is the full set of tree identities through `p`, not
only the conditions from the linear test equation. No ODE theorem is assumed.
-/

namespace RKCert

inductive Tree where
  | leaf : Tree
  | attach : Tree → Tree → Tree
  deriving DecidableEq, Repr

namespace Tree

/-- Number of vertices. -/
def order : Tree → ℕ
  | .leaf => 1
  | .attach c r => c.order + r.order

/-- Product of the densities of the trees hanging immediately below the root. -/
def childDensityProduct : Tree → ℕ
  | .leaf => 1
  | .attach c r => (c.order * c.childDensityProduct) * r.childDensityProduct

/-- Butcher's tree factorial: `γ(t) = |t| * ∏ γ(child)`. -/
def density (t : Tree) : ℕ := t.order * t.childDensityProduct

theorem order_pos (t : Tree) : 0 < t.order := by
  induction t with
  | leaf => decide
  | attach c r hc hr => unfold order; omega

theorem childDensityProduct_pos (t : Tree) : 0 < t.childDensityProduct := by
  induction t with
  | leaf => decide
  | attach c r hc hr => exact Nat.mul_pos (Nat.mul_pos c.order_pos hc) hr

theorem density_pos (t : Tree) : 0 < t.density :=
  Nat.mul_pos t.order_pos t.childDensityProduct_pos

/-- A chain with `n` edges and `n+1` vertices. -/
def chain : ℕ → Tree
  | 0 => .leaf
  | n + 1 => .attach (chain n) .leaf

@[simp] theorem order_chain (n : ℕ) : (chain n).order = n + 1 := by
  induction n with
  | zero => rfl
  | succ n ih => simp only [chain, order, ih]

@[simp] theorem density_chain (n : ℕ) : (chain n).density = (n + 1).factorial := by
  induction n with
  | zero => rfl
  | succ n ih =>
    calc
      (chain (n + 1)).density = ((chain n).order + 1) * (chain n).density := by
        simp only [chain, density, order, childDensityProduct, mul_one]
      _ = (n + 1 + 1) * (n + 1).factorial := by rw [order_chain, ih]
      _ = (n + 1 + 1).factorial := (Nat.factorial_succ (n + 1)).symm

end Tree

variable {K : Type*} {s : ℕ}

/-- The explicitness hypothesis alone, with stages indexed from zero. -/
def StrictLower [Zero K] (A : Fin s → Fin s → K) : Prop :=
  ∀ i j, i.val ≤ j.val → A i j = 0

section Weights
variable [CommSemiring K]

/-- Elementary stage weight. Each child first contributes a multiplication by `A`. -/
def stageWeight (A : Fin s → Fin s → K) : Tree → Fin s → K
  | .leaf => fun _ => 1
  | .attach c r => fun i => (∑ j, A i j * stageWeight A c j) * stageWeight A r i

/-- Elementary output weight `Φ(t)` (no symmetry factor). -/
def weight (A : Fin s → Fin s → K) (b : Fin s → K) (t : Tree) : K :=
  ∑ i, b i * stageWeight A t i

/-- Denominator-cleared classical rooted-tree order conditions. Over a field of
characteristic zero these are exactly `Φ(t) = 1 / γ(t)`. -/
def HasTreeOrderAtLeast (A : Fin s → Fin s → K) (b : Fin s → K) (p : ℕ) : Prop :=
  ∀ t : Tree, t.order ≤ p → (t.density : K) * weight A b t = 1

/-- On a unary chain the stage recursion reduces to ordinary matrix-vector multiplication. -/
theorem stageWeight_chain_succ (A : Fin s → Fin s → K) (n : ℕ) (i : Fin s) :
    stageWeight A (Tree.chain (n + 1)) i = ∑ j, A i j * stageWeight A (Tree.chain n) j := by
  simp only [Tree.chain, stageWeight, mul_one]

/-- The familiar linear test equation identity as a consequence, not an assumption. -/
theorem chain_condition {A : Fin s → Fin s → K} {b : Fin s → K} {n p : ℕ}
    (h : HasTreeOrderAtLeast A b p) (hn : n + 1 ≤ p) :
    ((n + 1).factorial : K) * weight A b (Tree.chain n) = 1 := by
  simpa only [Tree.density_chain] using h (Tree.chain n) (by simpa only [Tree.order_chain] using hn)

end Weights
end RKCert
