module

import RKCert.ReviewedNative.CommonDiagonalHeight

/-! Typed clients of the native mixed height and literal order cutoff.
Sharpness examples are outside this certificate. -/
open RKResearch RKResearch.FiniteSeries
open scoped Matrix FiniteRootedTree

section

variable {ι κ R : Type*} [Fintype ι] [Fintype κ] [CommRing R]
variable {A : Matrix ι ι R} {B : Matrix κ κ R}
variable {b : ι → R} {d : κ → R}
variable {δA : ι → ℕ} {δB : κ → ℕ} {D h p : ℕ} {γ : R}

example (t u : FiniteRootedTree) :
    treeHeight (t # (.leaf ◂ u)) = max (treeHeight t) (treeHeight u + 1) := by
  rw [treeHeight_rootedSum, treeHeight_unary]

example (hA : ShallowCommonDiagonal A δA D γ) (hh : h ≤ D) (t : FiniteRootedTree) :
    ∃ v ∈ heightOrderSpace A h (t.order : ℕ), ∀ i, δA i ≤ h → v i = Φ t A i :=
  heightOrderSpace_matches_shallow hA hh t

example (hA : ShallowCommonDiagonal A δA D γ) (sb : ∀ i, b i ≠ 0 → δA i ≤ D)
    (paid : ∀ t : FiniteRootedTree, treeHeight t ≤ D → (t.order : ℕ) ≤ p → b ⬝ᵥ Φ t A = 0) :
    ∀ t : FiniteRootedTree, (t.order : ℕ) ≤ p → b ⬝ᵥ Φ t A = 0 :=
  (series_zero_through_order_iff_height hA sb p).mpr paid

example (hA : ShallowCommonDiagonal A δA D γ) (hB : ShallowCommonDiagonal B δB D γ)
    (sb : ∀ i, b i ≠ 0 → δA i ≤ D) (sd : ∀ j, d j ≠ 0 → δB j ≤ D) :
    (∀ t : FiniteRootedTree, (t.order : ℕ) ≤ p → b ⬝ᵥ Φ t A = d ⬝ᵥ Φ t B) ↔
      (∀ t : FiniteRootedTree, treeHeight t ≤ D → (t.order : ℕ) ≤ p →
        b ⬝ᵥ Φ t A = d ⬝ᵥ Φ t B) :=
  series_equal_through_order_iff_height hA hB sb sd p

end

#check @RKResearch.FiniteSeries.treeHeight_rootedSum
#check @RKResearch.FiniteSeries.ShallowCommonDiagonal
#check @RKResearch.FiniteSeries.heightOrderSpace_matches_shallow
#check @RKResearch.FiniteSeries.series_zero_through_order_iff_height
#check @RKResearch.FiniteSeries.series_equal_through_order_iff_height

#print axioms RKResearch.FiniteSeries.heightOrderSpace_matches_shallow
#print axioms RKResearch.FiniteSeries.series_zero_through_order_iff_height
#print axioms RKResearch.FiniteSeries.series_equal_through_order_iff_height
