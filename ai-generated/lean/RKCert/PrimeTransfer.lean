module

public import RKCert.ResidueTransfer
public import Mathlib.RingTheory.Localization.FractionRing
public import Mathlib.RingTheory.Nilpotent.Lemmas

@[expose] public section

/-! # Precisely which strict inequalities can survive in a field?

A unit survives every residue field. A nonnilpotent element survives in some
field: first quotient by a prime avoiding it, then embed that domain into its
field of fractions. A nonzero nilpotent, in contrast, dies under every map to
a field. These distinctions matter for lower bounds that assume a nonzero
common diagonal or require several diagonal entries to survive simultaneously.
-/
namespace RKCert
universe u

variable {R : Type u} [CommRing R] {s p : ℕ} {Q : Prop}

/-- A single nonnilpotent marker can be kept nonzero in a field image. -/
theorem specialize_nonnilpotent {d : R} (hd : ¬ IsNilpotent d)
    (action : ∀ (K : Type u) [Field K] (f : R →+* K), f d ≠ 0 → Q) : Q := by
  classical
  rw [nilpotent_iff_mem_prime] at hd
  push Not at hd
  obtain ⟨I,hI,hmem⟩ := hd
  let := hI
  let F := FractionRing (R ⧸ I)
  let f : R →+* F := (algebraMap (R ⧸ I) F).comp (Ideal.Quotient.mk I)
  apply action F f
  intro hzero
  apply hmem
  apply Ideal.Quotient.eq_zero_iff_mem.mp
  apply IsFractionRing.injective (R ⧸ I) F
  simpa [f] using hzero

/-- Exact criterion, including the converse for nonzero nilpotents. -/
theorem nilpotent_iff_all_field_images_zero (d : R) :
    IsNilpotent d ↔ ∀ (K : Type u) [Field K] (f : R →+* K), f d = 0 := by
  constructor
  · intro h K _ f
    exact isNilpotent_iff_eq_zero.mp (h.map f)
  · intro h
    by_contra hn
    exact specialize_nonnilpotent hn (fun K _ f hf => hf (h K f))

/-- Uniform strict SDIRK field bounds extend to a possibly nonunit common
diagonal exactly under the nonnilpotence condition needed by this transfer. -/
theorem nonnilpotentCommonDiagonal_of_all_fields
    (hfield : ∀ (K : Type u) [Field K] (A : Fin s → Fin s → K) (b : Fin s → K) (d : K),
      (∀ i j, i.val < j.val → A i j=0) → (∀ i, A i i=d) → d≠0 →
      HasTreeOrderAtLeast A b p → Q)
    {A : Fin s → Fin s → R} {b : Fin s → R} {d : R}
    (ha : ∀ i j, i.val < j.val → A i j=0)
    (he : ∀ i, A i i=d) (hd : ¬ IsNilpotent d) (ho : HasTreeOrderAtLeast A b p) : Q :=
  specialize_nonnilpotent hd (fun K _ f hf =>
    hfield K _ _ (f d) (lowerTriangular_map ha f) (fun i => congrArg f (he i)) hf (ho.map f))

/-- All diagonal entries survive in a single field when their product is not
nilpotent. Separate nonnilpotence of each entry would not suffice. -/
theorem nonnilpotentDiagonalProduct_of_all_fields
    (hfield : ∀ (K : Type u) [Field K] (A : Fin s → Fin s → K) (b : Fin s → K),
      (∀ i j, i.val < j.val → A i j=0) → (∀ i, A i i≠0) →
      HasTreeOrderAtLeast A b p → Q)
    {A : Fin s → Fin s → R} {b : Fin s → R}
    (ha : ∀ i j, i.val < j.val → A i j=0)
    (hd : ¬ IsNilpotent (∏ i, A i i)) (ho : HasTreeOrderAtLeast A b p) : Q := by
  apply specialize_nonnilpotent hd
  intro K _ f hf
  apply hfield K _ _ (lowerTriangular_map ha f) _ (ho.map f)
  rw [map_prod] at hf
  exact fun i => Finset.prod_ne_zero_iff.mp hf i (Finset.mem_univ _)

/-- Without any nonnilpotence assumption a common ring diagonal may disappear:
one may use any conclusion shared by the strict SDIRK and ERK field cases. -/
theorem commonDiagonal_by_field_cases [Nontrivial R]
    (hexp : ∀ (K : Type u) [Field K] (A : Fin s → Fin s → K) (b : Fin s → K),
      StrictLower A → HasTreeOrderAtLeast A b p → Q)
    (hstr : ∀ (K : Type u) [Field K] (A : Fin s → Fin s → K) (b : Fin s → K) (d : K),
      (∀ i j, i.val < j.val → A i j=0) → (∀ i, A i i=d) → d≠0 →
      HasTreeOrderAtLeast A b p → Q)
    {A : Fin s → Fin s → R} {b : Fin s → R} {d : R}
    (ha : ∀ i j, i.val < j.val → A i j=0) (he : ∀ i, A i i=d)
    (ho : HasTreeOrderAtLeast A b p) : Q := by
  obtain ⟨I,hI⟩ := Ideal.exists_maximal R
  let := hI
  let := Ideal.Quotient.field I
  let f := Ideal.Quotient.mk I
  by_cases hz : f d=0
  · apply hexp (R ⧸ I) _ _ _ (ho.map f)
    intro i j hij
    rcases lt_or_eq_of_le hij with h|h
    · exact lowerTriangular_map ha f i j h
    · obtain rfl := Fin.ext h
      exact (congrArg f (he i)).trans hz
  · exact hstr (R ⧸ I) _ _ (f d) (lowerTriangular_map ha f)
      (fun i => congrArg f (he i)) hz (ho.map f)

end RKCert
