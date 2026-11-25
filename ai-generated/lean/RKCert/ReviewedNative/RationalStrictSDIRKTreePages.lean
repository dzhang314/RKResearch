module

public import RKCert.ReviewedNative.FiniteOrderCheck

@[expose] public section

/-! Bounds the tiles of the reviewed enumeration without changing that
enumeration, tree representation, or paid predicate. -/

namespace RKResearch.Certified.RationalStrictSDIRKTreePages

open RKResearch.FiniteRootedTree

def rootPage (xs ys : List FiniteRootedTree) : List FiniteRootedTree :=
  xs.flatMap fun u => ys.map (butcherProduct u)

theorem rootPage_all_iff (p : FiniteRootedTree → Bool) (xs ys : List FiniteRootedTree) :
    (rootPage xs ys).all p = true ↔
      ∀ u ∈ xs, ∀ v ∈ ys, p (butcherProduct u v) = true := by
  rw [List.all_eq_true]
  constructor
  · intro h u hu v hv
    apply h
    change butcherProduct u v ∈ xs.flatMap (fun t => ys.map (butcherProduct t))
    exact List.mem_flatMap.mpr ⟨u, hu, List.mem_map.mpr ⟨v, hv, rfl⟩⟩
  · intro h t ht
    change t ∈ xs.flatMap (fun u => ys.map (butcherProduct u)) at ht
    obtain ⟨u, hu, hu'⟩ := List.mem_flatMap.mp ht
    obtain ⟨v, hv, rfl⟩ := List.mem_map.mp hu'
    exact h u hu v hv

theorem split_left {p : FiniteRootedTree → Bool} (k : ℕ) (xs ys : List FiniteRootedTree)
    (hl : (rootPage (xs.take k) ys).all p = true)
    (hr : (rootPage (xs.drop k) ys).all p = true) :
    (rootPage xs ys).all p = true := by
  apply (rootPage_all_iff p xs ys).mpr
  intro u hu v hv
  have hb : u ∈ xs.take k ++ xs.drop k := by simpa only [List.take_append_drop] using hu
  rcases List.mem_append.mp hb with h | h
  · exact (rootPage_all_iff p _ _).mp hl u h v hv
  · exact (rootPage_all_iff p _ _).mp hr u h v hv

theorem split_right {p : FiniteRootedTree → Bool} (k : ℕ) (xs ys : List FiniteRootedTree)
    (hl : (rootPage xs (ys.take k)).all p = true)
    (hr : (rootPage xs (ys.drop k)).all p = true) :
    (rootPage xs ys).all p = true := by
  apply (rootPage_all_iff p xs ys).mpr
  intro u hu v hv
  have hb : v ∈ ys.take k ++ ys.drop k := by simpa only [List.take_append_drop] using hv
  rcases List.mem_append.mp hb with h | h
  · exact (rootPage_all_iff p _ _).mp hl u hu v h
  · exact (rootPage_all_iff p _ _).mp hr u hu v h

theorem all_trees_succ_of_bands (p : FiniteRootedTree → Bool) (n : ℕ)
    (h : ∀ i : Fin (n + 1), (rootPage (treesOfOrderSucc i.val)
      (treesOfOrderSucc (n - i.val))).all p = true) :
    (treesOfOrderSucc (n + 1)).all p = true := by
  rw [treesOfOrderSucc, List.all_eq_true]
  intro t ht
  obtain ⟨i, _, hi⟩ := List.mem_flatMap.mp ht
  exact List.all_eq_true.mp (h i) t hi

end RKResearch.Certified.RationalStrictSDIRKTreePages
