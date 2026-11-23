module

public import RKCert.Tree

@[expose] public section

/-!
# A finite certificate for all tree conditions

`Tree.through p` constructs precisely the ordered rooted trees of orders `1,…,p`.
The Boolean checker and the abstract all-trees order statement are proved equivalent.
No external list of trees or unchecked enumeration enters the certificate.
-/

namespace RKCert
namespace Tree

/-- Complete (plane) tree list up to a vertex bound, intended for small exact certificates. -/
def through : ℕ → List Tree
  | 0 => []
  | p + 1 =>
    let prev := through p
    .leaf :: ((prev.flatMap fun c => prev.map (.attach c)).filter fun t => decide (t.order ≤ p + 1))

/-- The enumeration neither omits a tree in range nor includes one out of range. -/
theorem mem_through (p : ℕ) : ∀ t : Tree, t ∈ through p ↔ t.order ≤ p := by
  induction p with
  | zero =>
    intro t
    have ht := t.order_pos
    simp only [through, List.not_mem_nil, false_iff]
    omega
  | succ p ih =>
    intro t
    cases t with
    | leaf => simp [through, order]
    | attach c r =>
      simp only [through, List.mem_cons, reduceCtorEq, false_or, List.mem_filter,
        decide_eq_true_eq]
      constructor
      · exact And.right
      · intro h
        have hsum : c.order + r.order ≤ p + 1 := h
        have hc := c.order_pos
        have hr := r.order_pos
        refine ⟨List.mem_flatMap.mpr ⟨c, (ih c).mpr (by omega), ?_⟩, h⟩
        exact List.mem_map.mpr ⟨r, (ih r).mpr (by omega), rfl⟩

end Tree

variable {K : Type*} [CommSemiring K] [DecidableEq K] {s : ℕ}

/-- Exact, executable test for the entire order predicate, not just the chains. -/
def checkTreeOrder (A : Fin s → Fin s → K) (b : Fin s → K) (p : ℕ) : Bool :=
  (Tree.through p).all fun t => decide ((t.density : K) * weight A b t = 1)

theorem checkTreeOrder_iff (A : Fin s → Fin s → K) (b : Fin s → K) (p : ℕ) :
    checkTreeOrder A b p = true ↔ HasTreeOrderAtLeast A b p := by
  unfold checkTreeOrder
  rw [List.all_eq_true]
  constructor
  · intro h t ht
    exact of_decide_eq_true (h t ((Tree.mem_through p t).mpr ht))
  · intro h t ht
    exact decide_eq_true (h t ((Tree.mem_through p t).mp ht))

end RKCert
