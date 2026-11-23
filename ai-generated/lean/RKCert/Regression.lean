module

public import RKCert.RK4

@[expose] public section

/-!
# A negative control: the linear test equation misses branching

This explicit three-stage example has the correct chain weights `1, 1/2, 1/6`.
Its two-leaf fork has weight `1/2` instead of `1/3`, so it is *not* order three.
-/

namespace RKCert.ChainOnly

/-- Two subdiagonal ones. -/
def A (i j : Fin 3) : ℚ := if i.val = j.val + 1 then 1 else 0

/-- Output row `(1/2, 1/3, 1/6)`. -/
def b (i : Fin 3) : ℚ :=
  match i.val with
  | 0 => 1 / 2
  | 1 => 1 / 3
  | _ => 1 / 6

def fork : Tree := .attach .leaf (.attach .leaf .leaf)

theorem explicit : StrictLower A := by unfold StrictLower; decide +kernel

theorem chains_pass : weight A b (Tree.chain 0) = 1 ∧
    weight A b (Tree.chain 1) = 1 / 2 ∧ weight A b (Tree.chain 2) = 1 / 6 := by decide +kernel

theorem fork_weight : weight A b fork = 1 / 2 := by decide +kernel

theorem not_order_three : ¬ HasTreeOrderAtLeast A b 3 := by
  intro h
  have hFork := h fork (by decide +kernel)
  exact (by decide +kernel : ¬ ((fork.density : ℚ) * weight A b fork = 1)) hFork

end RKCert.ChainOnly
