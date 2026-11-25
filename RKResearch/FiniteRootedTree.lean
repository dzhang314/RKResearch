module

public import Mathlib.Data.Nat.Factorial.Basic
public import Mathlib.Data.PNat.Basic

public section

namespace RKResearch

inductive FiniteRootedTree where
  | leaf
  | butcherProduct (base branch : FiniteRootedTree)

namespace FiniteRootedTree

scoped infix:70 " ◂ " => butcherProduct

@[expose, simp] def rootedSum (t : FiniteRootedTree) :
    FiniteRootedTree → FiniteRootedTree
  | leaf => t
  | base ◂ branch => rootedSum t base ◂ branch

scoped infixl:65 " # " => rootedSum

@[expose, simp] def order : FiniteRootedTree → ℕ+
  | leaf => 1
  | base ◂ branch => base.order + branch.order

@[simp↓] theorem order_rootedSum (t u : FiniteRootedTree) :
    (t # u).order = t.order + u.order - 1 := by
  have h : (t # u).order + 1 = t.order + u.order := by
    induction u with
    | leaf => rfl
    | butcherProduct base branch ih _ =>
      simp only [rootedSum, order, ← add_assoc]
      rw [← ih, add_right_comm]
  rw [← h, PNat.add_sub]

@[expose, simp] def forestFactorial : FiniteRootedTree → ℕ+
  | leaf => 1
  | base ◂ branch => base.forestFactorial * (branch.order * branch.forestFactorial)

@[simp↓] theorem forestFactorial_rootedSum (t u : FiniteRootedTree) :
    (t # u).forestFactorial = t.forestFactorial * u.forestFactorial := by
  induction u with
  | leaf => simp
  | butcherProduct base branch ih _ =>
    simp only [rootedSum, forestFactorial, ih, mul_assoc]

@[expose, simp] def factorial (t : FiniteRootedTree) : ℕ+ :=
  t.order * t.forestFactorial

@[expose, simp] def addBush (t : FiniteRootedTree) : ℕ → FiniteRootedTree
  | 0 => t
  | k + 1 => t.addBush k ◂ leaf

@[simp↓] theorem order_addBush (t : FiniteRootedTree) (k : ℕ) :
    (t.addBush k).order = t.order + k := by
  induction k with
  | zero => rfl
  | succ _ ih => exact congrArg Nat.succ ih

@[simp↓] theorem forestFactorial_addBush (t : FiniteRootedTree) (k : ℕ) :
    (t.addBush k).forestFactorial = t.forestFactorial := by
  induction k <;> simp [*]

@[simp↓] theorem factorial_addBush (t : FiniteRootedTree) (k : ℕ) :
    (t.addBush k).factorial = (t.order + k) * t.forestFactorial := by
  simp only [factorial, PNat.mul_coe, order_addBush, forestFactorial_addBush]

@[expose, simp] def bushyTree (n : ℕ+) : FiniteRootedTree :=
  leaf.addBush n.natPred

@[simp↓] theorem order_bushyTree (n : ℕ+) : (bushyTree n).order = n :=
  PNat.eq ((order_addBush leaf n.natPred).trans n.one_add_natPred)

@[simp↓] theorem forestFactorial_bushyTree (n : ℕ+) :
    (bushyTree n).forestFactorial = 1 := by apply forestFactorial_addBush

@[simp↓] theorem factorial_bushyTree (n : ℕ+) :
    (bushyTree n).factorial = n := by simp

@[expose, simp] def tallTree (n : ℕ+) : FiniteRootedTree := by
  induction n with
  | one => exact leaf
  | succ _ t => exact leaf ◂ t

@[simp↓] theorem order_tallTree (n : ℕ+) : (tallTree n).order = n := by
  unfold tallTree
  induction n with
  | one => rfl
  | succ n ih => simp only [PNat.recOn_succ, order, ih, add_comm 1 n]

@[simp↓] theorem factorial_tallTree (n : ℕ+) :
    (tallTree n).factorial = Nat.factorial n := by
  induction n with
  | one => rfl
  | succ n ih => simp [Nat.factorial_succ, ← ih, dsimp% order_tallTree n]

end FiniteRootedTree

end RKResearch
