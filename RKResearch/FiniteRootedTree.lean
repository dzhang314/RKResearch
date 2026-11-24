module

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

@[expose, simp] def bushyTree (n : ℕ+) : FiniteRootedTree :=
  n.recOn leaf (fun _ t => t ◂ leaf)

end FiniteRootedTree

end RKResearch
