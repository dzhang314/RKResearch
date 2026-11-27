module

public import RKCert.ReviewedNative.ERK9RationalFifteen
public import RKCert.ReviewedNative.ERK9RationalFifteenSecond
public import Mathlib.RingTheory.LocalRing.Basic

@[expose] public section

/-! The two genuine literal order-nine witnesses have common
denominator gcd dividing a power of 9!. A local ring paying 9!
therefore pays at least one of the two tableaux. -/

namespace RKResearch.Certified.ERK9FifteenLocalRing

open RKResearch
open scoped Matrix

abbrev D₁ := ERK9RationalFifteen.D
abbrev D₂ := ERK9RationalFifteenSecond.D

def c₁ : ℤ :=
  821289585235370257099814532575434324274799999608272971450402563954229096406030932903122608106
def c₂ : ℤ := -2261894477206979971669

theorem bezout : c₁*D₁+c₂*D₂=(10450944000:ℤ) := by decide +kernel

variable {R : Type*} [CommRing R]

theorem denominator_sum_unit (h : IsUnit (Nat.factorial 9 : R)) :
    IsUnit ((c₁:R)*(D₁:R)+(c₂:R)*(D₂:R)) := by
  have hd : (10450944000:ℕ)∣(Nat.factorial 9)^3 := by decide +kernel
  have hpow : IsUnit (((Nat.factorial 9)^3:ℕ):R) := by
    simpa only [Nat.cast_pow] using h.pow 3
  have hg : IsUnit (10450944000:R) := by
    exact isUnit_of_dvd_unit (Nat.cast_dvd_cast (α:=R) hd) hpow
  have hb := congrArg (Int.castRingHom R) bezout
  change (((c₁*D₁+c₂*D₂:ℤ):R))=((10450944000:ℤ):R) at hb
  simp only [Int.cast_add,Int.cast_mul,Int.cast_ofNat] at hb
  rwa [hb]

theorem exists_exact_local [IsLocalRing R]
    (h : IsUnit (Nat.factorial 9 : R)) :
    ∃ (U : Matrix (Fin 15) (Fin 15) R) (w : Fin 15 → R),
      ERK U ∧ HasOrder 9 U w ∧ ¬ HasOrder 10 U w := by
  rcases IsLocalRing.isUnit_or_isUnit_of_isUnit_add (denominator_sum_unit h) with h1 | h2
  · exact ERK9RationalFifteen.exists_exact_of_unit (isUnit_of_mul_isUnit_right h1)
  · exact ERK9RationalFifteenSecond.exists_exact_of_unit (isUnit_of_mul_isUnit_right h2)

end RKResearch.Certified.ERK9FifteenLocalRing

#print axioms RKResearch.Certified.ERK9FifteenLocalRing.exists_exact_local
