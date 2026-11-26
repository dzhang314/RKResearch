module

public import Mathlib.Data.Nat.Factorial.Basic
public import Mathlib.RingTheory.Ideal.Quotient.Basic

@[expose] public section

/-! Specializing cleared finite moment equations on the original index type.
No indices are removed or identified; only scalar values are mapped. -/
namespace RKResearch.Certified.Graded.IndexedResidueMoments

open scoped BigOperators

universe u v w

variable {ι : Type v} [Fintype ι]
variable {R : Type u} {S : Type w}

/-- The denominator-free beta moment equations through exponent qMax. -/
def ClearedMoments [CommSemiring R] (x w : ι → R) (κ : R) (d qMax : ℕ) : Prop :=
  ∀ q : ℕ, q ≤ qMax →
    κ * ((d + q : ℕ) : R) * ((d + q + 1 : ℕ) : R) *
      (∑ i : ι, w i * x i ^ q) = 1

/-- A unital scalar map preserves the literal equations, with precisely
the same finite index type and exponent range. -/
theorem ClearedMoments.map [CommSemiring R] [CommSemiring S]
    (f : R →+* S) {x w : ι → R} {κ : R} {d qMax : ℕ}
    (h : ClearedMoments x w κ d qMax) :
    ClearedMoments (f ∘ x) (f ∘ w) (f κ) d qMax := by
  unfold ClearedMoments at h ⊢
  intro q hq
  simpa only [Function.comp_apply, map_mul, map_natCast, map_sum, map_pow, map_one] using
    congrArg (fun z : R => f z) (h q hq)

/-- Under a scalar map a factorial normalizer is the identical natural
factorial cast in the target, not an independent parameter. -/
theorem ClearedMoments.map_factorial_normalizer [CommSemiring R] [CommSemiring S]
    (f : R →+* S) {x w : ι → R} {k d qMax : ℕ}
    (h : ClearedMoments x w (k.factorial : R) d qMax) :
    ClearedMoments (f ∘ x) (f ∘ w) (k.factorial : S) d qMax := by
  simpa only [map_natCast] using ClearedMoments.map f h

/-- A top factorial is a unit exactly when the entire positive natural
cast window below it consists of units. -/
theorem factorial_cast_isUnit_iff [CommSemiring R] (p : ℕ) :
    IsUnit (p.factorial : R) ↔ ∀ n : ℕ, 0 < n → n ≤ p → IsUnit (n : R) := by
  constructor
  · intro hp n hn hnp
    exact isUnit_of_dvd_unit (Nat.cast_dvd_cast (Nat.dvd_factorial hn hnp)) hp
  · induction p with
    | zero =>
        intro _
        simpa only [Nat.factorial_zero, Nat.cast_one] using (isUnit_one : IsUnit (1 : R))
    | succ p ih =>
        intro paid
        have hp := ih (fun n hn hnp => paid n hn (hnp.trans (Nat.le_succ p)))
        have hs : IsUnit (p.succ : R) := paid p.succ (Nat.succ_pos p) le_rfl
        simpa only [Nat.factorial_succ, Nat.cast_mul] using hs.mul hp

/-- Every maximal residue field carries the same indexed cleared equations,
all the paid factorial units, and the paid positive nonzero casts. -/
theorem ClearedMoments.in_maximal_residue [CommRing R]
    (I : Ideal R) [I.IsMaximal] {x w : ι → R} {κ : R} {d qMax p : ℕ}
    (h : ClearedMoments x w κ d qMax) (hfac : IsUnit (p.factorial : R)) :
    ClearedMoments (Ideal.Quotient.mk I ∘ x) (Ideal.Quotient.mk I ∘ w)
        (Ideal.Quotient.mk I κ) d qMax ∧
      (∀ n : ℕ, n ≤ p → IsUnit (n.factorial : R ⧸ I)) ∧
      (∀ n : ℕ, 0 < n → n ≤ p → (n : R ⧸ I) ≠ 0) := by
  let f : R →+* R ⧸ I := Ideal.Quotient.mk I
  have topUnit : IsUnit (p.factorial : R ⧸ I) := by
    simpa only [map_natCast] using IsUnit.map f hfac
  refine ⟨ClearedMoments.map f h, ?_, ?_⟩
  · intro n hn
    exact isUnit_of_dvd_unit (Nat.cast_dvd_cast (Nat.factorial_dvd_factorial hn)) topUnit
  · intro n hn hnp
    have hunit : IsUnit (n : R ⧸ I) :=
      (factorial_cast_isUnit_iff (R := R ⧸ I) p).1 topUnit n hn hnp
    letI : Field (R ⧸ I) := Ideal.Quotient.field I
    exact hunit.ne_zero

/-- Choose a maximal residue field without modifying the original indices.
To use its field instance, install the returned maximality proof and
then the stock field on the quotient. -/
theorem ClearedMoments.exists_maximal_residue [CommRing R] [Nontrivial R]
    {x w : ι → R} {κ : R} {d qMax p : ℕ}
    (h : ClearedMoments x w κ d qMax) (hfac : IsUnit (p.factorial : R)) :
    ∃ I : Ideal R, I.IsMaximal ∧
      ClearedMoments (Ideal.Quotient.mk I ∘ x) (Ideal.Quotient.mk I ∘ w)
        (Ideal.Quotient.mk I κ) d qMax ∧
      (∀ n : ℕ, n ≤ p → IsUnit (n.factorial : R ⧸ I)) ∧
      (∀ n : ℕ, 0 < n → n ≤ p → (n : R ⧸ I) ≠ 0) := by
  obtain ⟨I, hI⟩ := Ideal.exists_maximal R
  letI : I.IsMaximal := hI
  exact ⟨I, hI, ClearedMoments.in_maximal_residue I h hfac⟩

end RKResearch.Certified.Graded.IndexedResidueMoments
