module

public import Mathlib.RingTheory.Ideal.Maximal
public import Mathlib.RingTheory.Ideal.Quotient.Basic
public import Mathlib.RingTheory.Localization.FractionRing

public section

/-! # A characteristic-zero field image even with zero divisors

A maximal ideal on the original ring cannot in general be used: it can
kill a nonzero integer. Use the image of the nonzero natural scalars as
the prescribed multiplicative set, then choose a disjoint prime and pass
to the fraction field. The coefficient map need not be injective. -/
namespace RKCert.ReviewedNative
universe u

/-- Continue into some characteristic-zero field via a unital coefficient
homomorphism. Neither a domain hypothesis nor a chosen map is required. -/
theorem with_charZero_field {R : Type u} [CommRing R] [CharZero R] {Q : Prop}
    (action : ∀ (K : Type u) [Field K] [CharZero K] (_f : R →+* K), Q) : Q := by
  classical
  let M : Submonoid R := (nonZeroDivisors ℕ).map (Nat.castRingHom R).toMonoidHom
  have disjoint : Disjoint ((⊥ : Ideal R) : Set R) (M : Set R) := by
    refine Set.disjoint_left.mpr ?_
    rintro _ h ⟨n, hn, rfl⟩
    exact (mem_nonZeroDivisors_iff_ne_zero.mp hn)
      (Nat.cast_eq_zero.mp ((Submodule.mem_bot R).mp h))
  obtain ⟨I, prime, _, avoids⟩ := (⊥ : Ideal R).exists_le_prime_disjoint M disjoint
  let := prime
  let K := FractionRing (R ⧸ I)
  let f : R →+* K := (algebraMap (R ⧸ I) K).comp (Ideal.Quotient.mk I)
  let : CharZero K := charZero_of_inj_zero fun n h => by
    by_contra hn
    have hM : (n : R) ∈ M := ⟨n, mem_nonZeroDivisors_iff_ne_zero.mpr hn, rfl⟩
    have hI : (n : R) ∈ I := by
      apply Ideal.Quotient.eq_zero_iff_mem.mp
      apply IsFractionRing.injective (R ⧸ I) K
      rw [map_zero]
      change f (n : R) = 0
      rw [map_natCast, h]
    exact Set.disjoint_left.mp avoids hI hM
  exact action K f

end RKCert.ReviewedNative
