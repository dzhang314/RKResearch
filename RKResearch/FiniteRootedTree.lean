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

@[expose, simp] def order : FiniteRootedTree → ℕ+
  | leaf => 1
  | base ◂ branch => base.order + branch.order

@[expose, simp] def forestFactorial : FiniteRootedTree → ℕ+
  | leaf => 1
  | base ◂ branch => base.forestFactorial * (branch.order * branch.forestFactorial)

@[expose, simp] def factorial (t : FiniteRootedTree) : ℕ+ :=
  t.order * t.forestFactorial

@[expose, simp] def tallTree (n : ℕ+) : FiniteRootedTree :=
  n.recOn leaf (fun _ t => leaf ◂ t)

@[simp↓] theorem order_tallTree (n : ℕ+) : (tallTree n).order = n := by
  induction n <;> simp_all [add_comm]

@[simp↓] theorem factorial_tallTree (n : ℕ+) : (tallTree n).factorial = Nat.factorial n := by
  induction n <;> simp_all [Nat.factorial, dsimp% order_tallTree]

@[expose, simp] def bushyTree (n : ℕ+) : FiniteRootedTree :=
  n.recOn leaf (fun _ t => t ◂ leaf)

@[simp↓] theorem order_bushyTree (n : ℕ+) : (bushyTree n).order = n := by
  induction n <;> simp_all

@[simp↓] theorem forestFactorial_bushyTree (n : ℕ+) : (bushyTree n).forestFactorial = 1 := by
  induction n <;> simp_all

@[simp↓] theorem factorial_bushyTree (n : ℕ+) : (bushyTree n).factorial = n := by simp

end FiniteRootedTree

end RKResearch
