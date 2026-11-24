module

public import RKResearch.OrderConditions

@[expose] public section

/-!
# Finite certificates for the reviewed order conditions

Enumerate the reviewed trees on exactly `n + 1` vertices by splitting the
order between the two arguments of the reviewed `butcherProduct`. We keep
the constructor order, so no quotient or symmetry convention enters soundness.
-/

namespace RKResearch.Certified
open RKResearch RKResearch.FiniteRootedTree
open scoped Matrix

/-- All reviewed trees of order `n + 1`. Every pair produced has the right
size; no Cartesian square of the trees at all smaller orders is filtered. -/
def treesOfOrderSucc : (n : ℕ) → List FiniteRootedTree
  | 0 => [leaf]
  | n + 1 => (List.finRange (n + 1)).flatMap fun i =>
      (treesOfOrderSucc i.val).flatMap fun u =>
        (treesOfOrderSucc (n - i.val)).map (butcherProduct u)
termination_by n => n
decreasing_by all_goals omega

theorem mem_treesOfOrderSucc (n : ℕ) (t : FiniteRootedTree) :
    t ∈ treesOfOrderSucc n ↔ (t.order : ℕ) = n + 1 := by
  induction n using Nat.strong_induction_on generalizing t with
  | ind n ih =>
    cases n with
    | zero =>
      cases t with
      | leaf => simp [treesOfOrderSucc]
      | butcherProduct u v =>
        have hu := u.order.pos
        have hv := v.order.pos
        simp only [treesOfOrderSucc, List.mem_singleton, reduceCtorEq, order, PNat.add_coe,
          false_iff]
        omega
    | succ n =>
      rw [treesOfOrderSucc, List.mem_flatMap]
      constructor
      · rintro ⟨i, -, hi⟩
        obtain ⟨u, hu, hmap⟩ := List.mem_flatMap.mp hi
        obtain ⟨v, hv, rfl⟩ := List.mem_map.mp hmap
        have hu' := (ih i.val i.isLt u).mp hu
        have hv' := (ih (n - i.val) (by omega) v).mp hv
        simp only [order, PNat.add_coe]
        omega
      · intro ht
        cases t with
        | leaf => simp at ht
        | butcherProduct u v =>
          simp only [order, PNat.add_coe] at ht
          have hu := u.order.pos
          have hv := v.order.pos
          let i : Fin (n + 1) := ⟨(u.order : ℕ) - 1, by omega⟩
          refine ⟨i, List.mem_finRange i, List.mem_flatMap.mpr ⟨u, ?_, ?_⟩⟩
          · apply (ih i.val i.isLt u).mpr
            dsimp [i]
            omega
          · refine List.mem_map.mpr ⟨v, ?_, rfl⟩
            apply (ih (n - i.val) (by omega) v).mpr
            dsimp [i]
            omega

variable {ι R : Type*} [Fintype ι] [CommSemiring R] [DecidableEq R]

/-- Check the reviewed factorial/weight identity for every reviewed tree through order `p`. -/
def checkOrder (A : Matrix ι ι R) (b : ι → R) (p : ℕ) : Bool :=
  (List.range p).all fun n => (treesOfOrderSucc n).all fun t =>
    decide ((t.factorial : R) * (b ⬝ᵥ Φ t A) = 1)

theorem checkOrder_iff (A : Matrix ι ι R) (b : ι → R) (p : ℕ) :
    checkOrder A b p = true ↔ HasOrder p A b := by
  simp only [checkOrder, List.all_eq_true, List.mem_range, mem_treesOfOrderSucc,
    decide_eq_true_eq]
  constructor
  · intro h t ht
    have hpos := t.order.pos
    exact h ((t.order : ℕ) - 1) (by omega) t (by omega)
  · intro h n hn t ht
    exact h t (by omega)

end RKResearch.Certified
