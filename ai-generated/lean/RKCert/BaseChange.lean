module

public import RKCert.Tree

@[expose] public section

/-!
# Change of coefficient semiring

The denominator-cleared tree conditions are polynomial identities in the
tableau entries, so a unital semiring homomorphism takes any solution to a
solution in the target. The transfer of a nonvanishing condition requires
separate justification. In particular, a nonzero common diagonal may die in
a residue field; an invertible common diagonal cannot die in a nontrivial target.
-/

namespace RKCert

variable {R S : Type*} [CommSemiring R] [CommSemiring S] {s p : ℕ}

/-- Elementary stage weights commute with coefficient maps. -/
theorem map_stageWeight (f : R →+* S) (A : Fin s → Fin s → R) (t : Tree) (i : Fin s) :
    f (stageWeight A t i) = stageWeight (fun i j => f (A i j)) t i := by
  induction t generalizing i with
  | leaf => simp only [stageWeight, map_one]
  | attach t u iht ihu => simp only [stageWeight, map_mul, map_sum, iht, ihu]

/-- Elementary output weights commute with coefficient maps. -/
theorem map_weight (f : R →+* S) (A : Fin s → Fin s → R) (b : Fin s → R) (t : Tree) :
    f (weight A b t) = weight (fun i j => f (A i j)) (fun i => f (b i)) t := by
  simp only [weight, map_sum, map_mul, map_stageWeight]

/-- A solution of the full order conditions specializes to every target semiring. -/
theorem HasTreeOrderAtLeast.map {A : Fin s → Fin s → R} {b : Fin s → R}
    (h : HasTreeOrderAtLeast A b p) (f : R →+* S) :
    HasTreeOrderAtLeast (fun i j => f (A i j)) (fun i => f (b i)) p := by
  intro t ht
  simpa only [map_mul, map_natCast, map_weight, map_one] using congrArg f (h t ht)

theorem StrictLower.map {A : Fin s → Fin s → R} (h : StrictLower A) (f : R →+* S) :
    StrictLower (fun i j => f (A i j)) := by
  intro i j hij
  change f (A i j) = 0
  rw [h i j hij, map_zero]

/-- Lower triangularity (allowing explicit stages) is likewise preserved. -/
theorem lowerTriangular_map {A : Fin s → Fin s → R}
    (h : ∀ i j, i.val < j.val → A i j = 0) (f : R →+* S) :
    ∀ i j, i.val < j.val → f (A i j) = 0 := by
  intro i j hij; rw [h i j hij, map_zero]

/-- A common diagonal specializes to a common diagonal; a unit remains nonzero. -/
theorem map_unit_diagonal [Nontrivial S] {A : Fin s → Fin s → R} {d : R}
    (h : ∀ i, A i i = d) (hd : IsUnit d) (f : R →+* S) :
    (∀ i, f (A i i) = f d) ∧ f d ≠ 0 :=
  ⟨fun i => congrArg f (h i), (hd.map f).ne_zero⟩

/-- Any ERK lower-bound contradiction in the target pulls back along the
specified coefficient map. Existence of such a map is a separate hypothesis. -/
theorem no_explicit_of_no_explicit_after_map (f : R →+* S)
    (hS : ∀ (A : Fin s → Fin s → S) (b : Fin s → S),
      StrictLower A → ¬ HasTreeOrderAtLeast A b p) :
    ∀ (A : Fin s → Fin s → R) (b : Fin s → R),
      StrictLower A → ¬ HasTreeOrderAtLeast A b p := by
  intro A b hA hb
  exact hS _ _ (hA.map f) (hb.map f)

end RKCert
