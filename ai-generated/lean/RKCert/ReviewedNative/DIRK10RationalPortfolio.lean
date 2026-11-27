module

public import RKCert.ReviewedNative.DIRK10RationalTwelve
public import RKCert.ReviewedNative.DIRK10RationalTwelveAlternate
public import RKCert.ReviewedNative.DIRK10RationalPortfolioArithmetic
public import Mathlib.RingTheory.LocalRing.Basic

@[expose] public section

/-! A local coefficient ring can always choose the better of the two
literal rational twelve-stage tableaux. The chosen witness has a unit
eleventh-bush defect, not merely a certificate in its residue field. -/

namespace RKResearch.Certified.DIRK10RationalPortfolio

open RKResearch FiniteRootedTree
open scoped Matrix

variable {R : Type*} [CommRing R]

def UnitBush (A : Matrix (Fin 12) (Fin 12) R) (b : Fin 12 → R) : Prop :=
  IsUnit (((bushyTree 11).factorial:R)*(b ⬝ᵥ Φ (bushyTree 11) A)-1)

def Paid (R : Type*) [CommRing R] : Prop :=
  ∃ (A : Matrix (Fin 12) (Fin 12) R) (b : Fin 12 → R),
    A.IsLowerTriangular ∧ HasOrder 10 A b ∧ UnitBush A b

theorem not_order_eleven [Nontrivial R] {A : Matrix (Fin 12) (Fin 12) R}
    {b : Fin 12 → R} (h : UnitBush A b) : ¬ HasOrder 11 A b := by
  intro ho
  unfold UnitBush at h
  rw [ho (bushyTree 11) (by decide), sub_self] at h
  exact h.ne_zero rfl

theorem paid_base (hD : IsUnit (DIRK10RationalTwelve.D:R)) : Paid R := by
  obtain ⟨d,hd⟩ := hD.exists_right_inv
  refine ⟨DIRK10RationalTwelve.A d, DIRK10RationalTwelve.b d, DIRK10RationalTwelve.lower d,
    DIRK10RationalTwelve.order_ten d hd, ?_⟩
  have hu : IsUnit ((2488320:R) *
      (((bushyTree 11).factorial:R)*(DIRK10RationalTwelve.b d ⬝ᵥ
        Φ (bushyTree 11) (DIRK10RationalTwelve.A d))-1)) := by
    change IsUnit ((2488320:R)*((DIRK10RationalTwelve.bush11.factorial:R)*
      (DIRK10RationalTwelve.b d ⬝ᵥ Φ DIRK10RationalTwelve.bush11
        (DIRK10RationalTwelve.A d))-1))
    rw [DIRK10RationalTwelve.bush_defect d hd]
    exact isUnit_one
  exact (IsUnit.mul_iff.mp hu).2

theorem paid_alternate (hD : IsUnit (DIRK10RationalTwelveAlternateFlagReplay.denominator:R))
    (h19891 : IsUnit (19891:R)) : Paid R := by
  obtain ⟨d,hd⟩ := hD.exists_right_inv
  exact ⟨DIRK10RationalTwelveAlternateFlagReplay.A d,
    DIRK10RationalTwelveAlternateFlagReplay.weights d,
    DIRK10RationalTwelveAlternateFlagReplay.A_lower d,
    DIRK10RationalTwelveAlternateFlagReplay.transport d hd,
    DIRK10RationalTwelveAlternateFlagReplay.next_star_isUnit d hd h19891⟩

theorem smooth_unit (h : IsUnit ((Nat.factorial 10 : ℕ):R)) : IsUnit (27216000:R) := by
  let f := Int.castRingHom R
  have h0 : IsUnit (3628800:R) := by
    rw [show Nat.factorial 10 = 3628800 by decide +kernel] at h
    exact h
  have hs := congrArg f Arithmetic.coverDivFactorialSquared
  simp only [map_mul, map_pow, map_ofNat] at hs
  have hu := h0.pow 2
  rw [← hs] at hu
  exact (IsUnit.mul_iff.mp hu).1

theorem paid_local [IsLocalRing R] (h : IsUnit ((Nat.factorial 10 : ℕ):R)) : Paid R := by
  let f := Int.castRingHom R
  have hSmooth := smooth_unit h
  have hcover := congrArg f Arithmetic.coverBezout
  simp only [map_add,map_mul,map_neg,map_ofNat] at hcover
  change (1761374130916471727129987906589657431558423718257995510158477:R) *
      (DIRK10RationalTwelve.D:R) +
      (-330723624932663944996782097049:R) *
        ((DIRK10RationalTwelveAlternateFlagReplay.denominator:R) * (19891:R)) =
      (27216000:R) at hcover
  rw [← hcover] at hSmooth
  rcases IsLocalRing.isUnit_or_isUnit_of_isUnit_add hSmooth with hL | hR
  · exact paid_base (IsUnit.mul_iff.mp hL).2
  · obtain ⟨hD,hstar⟩ := IsUnit.mul_iff.mp (IsUnit.mul_iff.mp hR).2
    exact paid_alternate hD hstar

theorem exists_exact_local [IsLocalRing R] (h : IsUnit ((Nat.factorial 10 : ℕ):R)) :
    ∃ (A : Matrix (Fin 12) (Fin 12) R) (b : Fin 12 → R),
      A.IsLowerTriangular ∧ HasOrder 10 A b ∧ ¬ HasOrder 11 A b := by
  obtain ⟨A, b, hL, hp, hu⟩ := paid_local h
  exact ⟨A,b,hL,hp,not_order_eleven hu⟩

end RKResearch.Certified.DIRK10RationalPortfolio
