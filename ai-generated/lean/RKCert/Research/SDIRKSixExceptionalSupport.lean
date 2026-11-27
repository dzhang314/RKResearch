module
public import RKCert.Research.SDIRKSixResidualExclusions
public import RKCert.ReviewedNative.SDIRKSixSmallCharacteristicExclusion
import Mathlib.Tactic.NormNum.Prime
public section

namespace RKResearch
open Certified.Graded.SDIRKSix
open RKCert.ReviewedNative.SDIRKSixReceipts

/-- Exactly the prime characteristics in which an order-six, six-stage
strict SDIRK exists over *some* field; 3533 needs a quadratic extension. -/
@[expose] def sixStageSupport : ℕ := 11 * 17 * 163 * 263 * 457 * 3533 * 126963077

theorem sixStageSupport_eq : sixStageSupport = 11 * 17 * 163 * 263 * 457 * 3533 * 126963077 := rfl

private theorem old_dvd :
    fourExceptionProduct ∣ (30 * 7 * 241 * 255919 * sixStageSupport)^60 := by decide +kernel

private theorem strict_field_floor_off_support {K : Type*} [Field K] {s : ℕ}
    {A : Matrix (Fin s) (Fin s) K} {b : Fin s → K} {γ : K}
    (ho : HasOrder 6 A b) (ha : A.IsLowerTriangular) (he : ∀ i, A i i = γ)
    (hγ : γ ≠ 0) (hD : (sixStageSupport : K) ≠ 0) : 7 ≤ s := by
  by_cases hp : (fourExceptionProduct : K) = 0
  · obtain ⟨m,hm⟩ := old_dvd
    have hcast := congrArg (fun a : ℕ => (a : K)) hm
    simp only [Nat.cast_pow, Nat.cast_mul, Nat.cast_ofNat, hp, zero_mul] at hcast
    have h0 := eq_zero_of_pow_eq_zero hcast
    have h2 := (ho.natCast_isUnit (n := 2) (by decide) (by decide)).ne_zero
    have h3 := (ho.natCast_isUnit (n := 3) (by decide) (by decide)).ne_zero
    have h5 := (ho.natCast_isUnit (n := 5) (by decide) (by decide)).ne_zero
    have h30 : (30:K) ≠ 0 := by
      rw [show (30 : K) = (2:K)*3*5 by norm_num]
      exact mul_ne_zero (mul_ne_zero h2 h3) h5
    by_cases h7 : (7:K) = 0
    · let : CharP K 7 := (CharP.charP_iff_prime_eq_zero (by decide : Nat.Prime 7)).mpr h7
      exact seven_le_of_strict_order_six_char_seven ho ha he hγ
    by_cases h241 : (241:K) = 0
    · let : CharP K 241 := (CharP.charP_iff_prime_eq_zero (by norm_num : Nat.Prime 241)).mpr h241
      exact seven_le_of_strict_order_six_char_241 ho ha he hγ
    have h255 : (255919:K) = 0 := by
      by_contra hn
      exact (mul_ne_zero (mul_ne_zero (mul_ne_zero (mul_ne_zero h30 h7) h241) hn) hD) h0
    let : CharP K 255919 := (CharP.charP_iff_prime_eq_zero (by norm_num : Nat.Prime 255919)).mpr h255
    exact seven_le_of_strict_order_six_char_255919 ho ha he hγ
  · exact seven_le_of_strict_order_six_away_four hp ho ha he hγ

/-- At six stages every field image must kill the squarefree exact
support product, and the common diagonal must be a unit. In contrapositive
form this remains valid over rings with zero divisors and nilpotents. -/
theorem HasOrder.common_diagonal_order_six_stages_off_exceptional_support
    {R : Type*} [CommRing R] {s : ℕ} {A : Matrix (Fin s) (Fin s) R}
    {b : Fin s → R} {γ : R}
    (ho : HasOrder 6 A b) (ha : A.IsLowerTriangular) (he : ∀ i, A i i = γ)
    (hgood : ¬ IsUnit γ ∨ ¬ IsNilpotent (sixStageSupport : R)) : 7 ≤ s := by
  have h := ho.common_diagonal_stage_floor_away_nat (D := sixStageSupport) (k := 7)
    ha he hgood (fun _ _ _ _ _ d ord tr dg nz => strict_field_floor_off_support ord tr dg nz d)
  have he6 : erkUniformFloor 6 = 7 := by
    have hh := congrArg (fun xs : List ℕ => xs[6]?) erkUniformFloor_through_twenty
    change some (erkUniformFloor 6) = some 7 at hh
    exact Option.some.inj hh
  simpa only [he6, min_self] using h

end RKResearch
