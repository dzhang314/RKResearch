module

public import RKCert.ReviewedNative.HyperplaneReverseActivation

@[expose] public section

/-! # The original grade-sixteen hyperplane, without an abstract row input

The compressed hyperplane is the range of actual restriction on the old
tree grade.  Its rank is computed, not supplied, and the only exclusion
takes place in that original tree space.
-/
namespace RKResearch.Certified.Graded.HyperplaneTerminal

open RKResearch Reverse Module
open scoped Classical Matrix
noncomputable section
variable {K : Type*} [Field K] [CharZero K] {s n j p : ℕ}

theorem physical_class_grade_impossible {A : Matrix (Fin s) (Fin s) K} {b : Fin s→K}
    (ha : ∀ i j, i≤j → A i j=0) (ho : HasOrder p A b)
    (e : Fin n→Fin s) (r : Fin s→Fin n)
    (ordered : Monotone e) (earlier : ∀i,e (r i) ≤ i)
    (cy : ∀i,reflectedClock A (e (r i))=reflectedClock A i)
    (rank : finrank K (treeSpace A j)+1=n)
    (same : ∀v∈treeSpace A (j+1), ∀i,v (e (r i))=v i)
    (pay : j+4≤p)
    (excluded : ∀h,folded r b h≠0 → reflectedClock A (e h)=0 →
      (fun i=>coordinate (K:=K) h (r i))∉treeSpace A j) : False := by
  let V := treeSpace A j
  let R : V →ₗ[K] (Fin n→K) := {
    toFun:=fun v h=>v.val (e h)
    map_add':=fun _ _=>rfl
    map_smul':=fun _ _=>rfl }
  have get (v : V) (i : Fin s) : R v (r i)=v.val i :=
    same v.val (treeSpace_mono A (Nat.le_succ j) v.property) i
  have inj : Function.Injective R := by
    intro x z eq
    apply Subtype.ext
    funext i
    exact (get x i).symm.trans ((congrFun eq (r i)).trans (get z i))
  have rankR : finrank K R.range=finrank K V := LinearMap.finrank_range_of_inj inj
  have before (x : Fin n→K) (hx : x∈R.range) : (fun i=>x (r i))∈treeSpace A j := by
    obtain ⟨v,rfl⟩:=hx
    have eq : (fun i=>R v (r i))=v.val := funext (get v)
    rw [eq]
    exact v.property
  apply folded_singleton_impossible ha ho e r ordered earlier
    (fun h=>reflectedClock A (e h)) cy R.range (by rw [rankR]; exact rank)
    before same pay
  intro h active late hit
  exact excluded h active late (before _ hit)

end
end RKResearch.Certified.Graded.HyperplaneTerminal
