module

public import RKCert.ResidualProducts
public import RKCert.Enumeration
public import Mathlib.Algebra.Field.Rat

@[expose] public section

/-!
# Negative control: one residual against monomials is not sufficient

Start with six rows of a fifth-order formula. At the zero node, take the
second difference of output evaluations at the rows `0,v,2v`, where
`v=(1,-1,0,…,0)`. The zero row already exists. This change annihilates
every affine function of the added rows, but it need not annihilate a
quadratic one. The complete tableau is checked here, without assuming any
order statement about the original formula.
-/

namespace RKCert.MonomialOnly

/-- Eight-stage rational perturbation, in chronological order. -/
def A (i j : Fin 8) : ℚ :=
  match i.val, j.val with
  | 1, 0 => 1 / 4
  | 2, 0 => 1 / 8
  | 2, 1 => 1 / 8
  | 3, 1 => -1 / 2
  | 3, 2 => 1
  | 4, 0 => 3 / 16
  | 4, 3 => 9 / 16
  | 5, 0 => -3 / 7
  | 5, 1 => 2 / 7
  | 5, 2 => 12 / 7
  | 5, 3 => -12 / 7
  | 5, 4 => 8 / 7
  | 6, 0 => 1
  | 6, 1 => -1
  | 7, 0 => 2
  | 7, 1 => -2
  | _, _ => 0

def b (i : Fin 8) : ℚ :=
  match i.val with
  | 0 => 97 / 90
  | 2 => 32 / 90
  | 3 => 12 / 90
  | 4 => 32 / 90
  | 5 => 7 / 90
  | 6 => -2
  | 7 => 1
  | _ => 0

theorem explicit : StrictLower A := by unfold StrictLower; decide +kernel

theorem moments : HasMomentsThrough A b 5 := by
  have checked : ∀ k : Fin 5, ((k.val + 1 : ℕ) : ℚ) * (∑ i, b i * nodes A i ^ k.val) = 1 := by
    decide +kernel
  intro k hk
  exact checked ⟨k, by omega⟩

set_option maxHeartbeats 2000000 in
/-- Every test with just one residual and a monomial partner passes at order five,
including the full admissible range of indices. -/
theorem monomial_tests (t : Tree) (k : ℕ) (hk : t.order + k + 1 ≤ 5) :
    rootCutPair A b t (Tree.bush k) = 0 := by
  have checked : (Tree.through 4).all (fun u =>
      decide (∀ m : Fin 5, u.order + m.val + 1 ≤ 5 → rootCutPair A b u (Tree.bush m.val) = 0)) =
      true := by decide +kernel
  have ht := (Tree.mem_through 4 t).mpr (by omega)
  exact (of_decide_eq_true (List.all_eq_true.mp checked t ht)) ⟨k, by omega⟩ hk

/-- Two copies of the two-vertex branch: a quadratic residual test of total cost five. -/
theorem quadratic_failure :
    (∑ i, b i * (stageResidual A (Tree.chain 1) i) ^ 2) = 1 / 8 := by decide +kernel

/-- The tree with two two-vertex branches has weight 7/40 rather than 1/20. -/
def doubleBranch : Tree := .attach (Tree.chain 1) (.attach (Tree.chain 1) .leaf)

theorem doubleBranch_weight : weight A b doubleBranch = 7 / 40 := by decide +kernel

theorem not_order_five : ¬ HasTreeOrderAtLeast A b 5 := by
  intro h
  exact (by decide +kernel : ¬ ((doubleBranch.density : ℚ) * weight A b doubleBranch = 1))
    (h doubleBranch (by decide +kernel))

end RKCert.MonomialOnly
