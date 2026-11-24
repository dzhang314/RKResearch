module

public import RKCert.ReviewedNative.LocalLinearCleanFourForward
import Mathlib.Data.Finset.Sort

@[expose] public section

/-! # Chronology of the actual feed clocks

The clocks are ordered by their first original row, not by the field
order. Every occurrence of a clock still belongs to its whole block. -/
namespace RKResearch.Certified.Graded.Reverse.LocalLinear.CleanFour

open RKResearch RKCert.Endpoint RKCert.Endpoint.WeightedClock
open scoped Classical Matrix
noncomputable section

variable {K : Type*} [Field K] {s m : ℕ}

/-- An exhaustive chronological enumeration of the supported clocks.
The ordering is on each clock's first original feed row. -/
structure FeedChronology (c θ : Fin s → K) (m : ℕ) where
  clock : Fin m → K
  site : ∀ i, clock i ∈ weightedSites c θ
  covers : ∀ x ∈ weightedSites c θ, ∃ i, clock i = x
  ordered : StrictMono (fun i => firstRow c θ (clock i) (site i))

/-- Sort the image of the first-row map and pull it back to the actual
clocks. This uses no order on the scalar field. -/
def feedChronology {c θ : Fin s → K}
    (hcard : (weightedSites c θ).card = m) : FeedChronology c θ m := by
  classical
  let D := weightedSites c θ
  let f : D → Fin s := fun x => firstRow c θ x.val x.property
  have injective : Function.Injective f := by
    intro x z same
    exact Subtype.ext (firstRow_eq_implies_clock_eq x.property z.property same)
  let T := D.attach.image f
  have count : T.card = m := by
    change (D.attach.image f).card = m
    rw [Finset.card_image_of_injective _ injective, Finset.card_attach]
    exact hcard
  let O : Fin m ≃o T := T.orderIsoOfFin count
  have lookup (i : Fin m) : ∃ x : D, f x = (O i).val := by
    have seen : (O i).val ∈ D.attach.image f := (O i).property
    obtain ⟨x, _, row⟩ := Finset.mem_image.mp seen
    exact ⟨x, row⟩
  choose source hs using lookup
  refine ⟨fun i => (source i).val, fun i => (source i).property, ?_, ?_⟩
  · intro x hx
    let z : D := ⟨x, hx⟩
    have on : f z ∈ T := Finset.mem_image.mpr ⟨z, Finset.mem_attach _ z, rfl⟩
    let row : T := ⟨f z, on⟩
    let i : Fin m := O.symm row
    have eq : (O i).val = f z :=
      congrArg (fun a : T => a.val) (O.apply_symm_apply row)
    exact ⟨i, congrArg (fun a : D => a.val) (injective ((hs i).trans eq))⟩
  · intro i j lt
    change f (source i) < f (source j)
    rw [hs i, hs j]
    exact O.strictMono lt

theorem FeedChronology.clock_injective {c θ : Fin s → K} (E : FeedChronology c θ m) :
    Function.Injective E.clock := by
  intro i j eq
  have same :
      (⟨E.clock i, E.site i⟩ : weightedSites c θ) = ⟨E.clock j, E.site j⟩ :=
    Subtype.ext eq
  exact E.ordered.injective
    (congrArg (fun x : weightedSites c θ => firstRow c θ x.val x.property) same)

theorem FeedChronology.clock_ne {c θ : Fin s → K} (E : FeedChronology c θ m)
    {i j : Fin m} (ne : i ≠ j) : E.clock i ≠ E.clock j :=
  fun eq => ne (E.clock_injective eq)

theorem FeedChronology.clock_zero_of_origin {n : ℕ}
    {A : Matrix (Fin (n+1)) (Fin (n+1)) K}
    {b τ h W k θ : Fin (n+1) → K} {U : Submodule K (Fin (n+1) → K)} {P : Polynomial K}
    (E : FeedChronology (nodes A) θ (m+1))
    (ha : ∀ i j, i ≤ j → A i j = 0) (G : UnitCleanFourFeed A b τ h W k θ U P)
    (inside : hiddenKernel b τ U ≤ zeroSpace A 8)
    (origin : (0 : K) ∈ weightedSites (nodes A) θ) : E.clock 0 = 0 := by
  obtain ⟨i, eq⟩ := E.covers 0 origin
  have same : (⟨E.clock i, E.site i⟩ : weightedSites (nodes A) θ) = ⟨0, origin⟩ :=
    Subtype.ext eq
  have row := congrArg
    (fun x : weightedSites (nodes A) θ => firstRow (nodes A) θ x.val x.property) same
  have first : firstRow (nodes A) θ (E.clock i) (E.site i) = 0 :=
    row.trans (firstRow_origin ha G inside origin)
  have eqi : i = 0 := by
    apply le_antisymm _ (Fin.zero_le i)
    apply le_of_not_gt
    intro lt
    have before := E.ordered lt
    change firstRow (nodes A) θ (E.clock 0) (E.site 0) < firstRow (nodes A) θ (E.clock i) (E.site i) at before
    rw [first] at before
    exact (not_lt_of_ge (Fin.zero_le _)) before
  simpa only [eqi] using eq

end
end RKResearch.Certified.Graded.Reverse.LocalLinear.CleanFour
