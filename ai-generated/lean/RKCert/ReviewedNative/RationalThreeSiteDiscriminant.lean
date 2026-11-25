module

public import Mathlib.Algebra.Field.Rat
public import Mathlib.Data.Rat.Lemmas
public import Mathlib.Data.Nat.Prime.Basic
import Mathlib.Data.ZMod.Basic
import Mathlib.Tactic.FinCases
import Mathlib.Tactic.LinearCombination
import Mathlib.Tactic.Ring

@[expose] public section

/-! # The rational three-site discriminant for exact moments through degree four

Work with the cross-multiplied discriminant: this does not require
canceling `3*r^2 - 1` or imposing distinctness of the three putative roots.
The obstruction at the prime 3 is proved by integer divisibility, not by
a reduction map on the rationals. -/

namespace RKResearch.Certified.RationalQuadratureFive

/-- The integer represented by a prime with multiplicity exactly one
cannot become a square in the rationals. -/
theorem not_isSquare_rat_intCast_prime_mul {q : ℕ} {a : ℤ} (hq : q.Prime)
    (ha : ¬ (q : ℤ) ∣ a) : ¬ IsSquare (((q : ℤ) * a : ℤ) : ℚ) := by
  rw [Rat.isSquare_intCast_iff]
  rintro ⟨z, hz⟩
  have hd : (q : ℤ) ∣ z * z := hz ▸ dvd_mul_right (q : ℤ) a
  have hn : q ∣ z.natAbs := by
    apply hq.dvd_of_dvd_pow (n := 2)
    simpa only [pow_two, Int.natAbs_mul] using (Int.ofNat_dvd_left.mp hd)
  obtain ⟨t, ht⟩ := Int.ofNat_dvd_left.mpr hn
  apply ha
  refine ⟨t * t, mul_left_cancel₀ (Int.natCast_ne_zero.mpr hq.ne_zero) ?_⟩
  calc
    (q : ℤ) * a = z * z := hz
    _ = (q : ℤ) * ((q : ℤ) * (t * t)) := by rw [ht]; ring

/-- Homogeneous quartic appearing in the cleared discriminant. -/
def centeredDiscriminantQuartic (n : ℤ) (d : ℕ) : ℤ :=
  25 * n^4 - 22 * n^2 * (d : ℤ)^2 + 5 * (d : ℤ)^4

private theorem quartic_mod_three_zero_iff (a b : ZMod 3) :
    25 * a^4 - 22 * a^2 * b^2 + 5 * b^4 = 0 ↔ a = 0 ∧ b = 0 := by
  revert a b
  decide

/-- At a primitive integer pair the homogeneous quartic is a 3-adic unit. -/
theorem three_not_dvd_centeredDiscriminantQuartic {n : ℤ} {d : ℕ}
    (h : n.natAbs.Coprime d) : ¬ (3 : ℤ) ∣ centeredDiscriminantQuartic n d := by
  intro hd
  have hz : (centeredDiscriminantQuartic n d : ZMod 3) = 0 :=
    (ZMod.intCast_zmod_eq_zero_iff_dvd _ 3).mpr hd
  simp only [centeredDiscriminantQuartic, Int.cast_sub, Int.cast_add, Int.cast_mul,
    Int.cast_pow, Int.cast_natCast, Int.cast_ofNat] at hz
  obtain ⟨hn, hd⟩ := (quartic_mod_three_zero_iff (n : ZMod 3) (d : ZMod 3)).mp hz
  have hnn : 3 ∣ n.natAbs :=
    Int.ofNat_dvd_left.mp ((ZMod.intCast_zmod_eq_zero_iff_dvd n 3).mp hn)
  have hdd : 3 ∣ d := (ZMod.natCast_eq_zero_iff d 3).mp hd
  have hg : Nat.gcd n.natAbs d = 1 := h
  have h31 : (3 : ℕ) = 1 := (Nat.gcd_eq_one_iff.mp hg) 3 hnn hdd
  exact (by decide : (3 : ℕ) ≠ 1) h31

/-- The discriminant numerator after the square denominator has been
cleared is not a rational square, for every rational first root. -/
theorem centered_discriminant_not_isSquare (r : ℚ) :
    ¬ IsSquare (12 * (25 * r^4 - 22 * r^2 + 5)) := by
  rintro ⟨z, hz⟩
  have hn : (r.num : ℚ) = r * (r.den : ℚ) := (Rat.mul_den_eq_num r).symm
  have hquartic :
      (centeredDiscriminantQuartic r.num r.den : ℚ) =
        (r.den : ℚ)^4 * (25 * r^4 - 22 * r^2 + 5) := by
    simp only [centeredDiscriminantQuartic, Int.cast_sub, Int.cast_add, Int.cast_mul,
      Int.cast_pow, Int.cast_natCast, Int.cast_ofNat]
    rw [hn]
    ring
  have hnot : ¬ IsSquare ((3 * centeredDiscriminantQuartic r.num r.den : ℤ) : ℚ) :=
    not_isSquare_rat_intCast_prime_mul Nat.prime_three
      (three_not_dvd_centeredDiscriminantQuartic r.reduced)
  apply hnot
  refine ⟨(r.den : ℚ)^2 * z / 2, ?_⟩
  rw [Int.cast_mul, Int.cast_ofNat, hquartic]
  calc
    3 * ((r.den : ℚ)^4 * (25 * r^4 - 22 * r^2 + 5)) =
        (r.den : ℚ)^4 / 4 * (12 * (25 * r^4 - 22 * r^2 + 5)) := by ring
    _ = (r.den : ℚ)^4 / 4 * (z * z) := by rw [hz]
    _ = _ := by ring

/-- From the two centered moment constraints the other two roots'
difference would square to the cleared discriminant. -/
theorem centered_three_roots_discriminant (r u v : ℚ)
    (hpair : r*u + r*v + u*v = -3/5)
    (hprod : 3*(r*u*v) + (r+u+v) = 0) :
    (5*(3*r^2 - 1)*(u-v))^2 = 12 * (25*r^4 - 22*r^2 + 5) := by
  have hs : 5*(3*r^2 - 1)*(u+v) = -4*r := by
    linear_combination (15*r)*hpair - 5*hprod
  have hp : 5*(3*r^2 - 1)*(u*v) = 3 - 5*r^2 := by
    linear_combination (5*(3*r^2 - 1))*hpair - r*hs
  calc
    (5*(3*r^2 - 1)*(u-v))^2 =
        (5*(3*r^2 - 1)*(u+v))^2 - 4*(5*(3*r^2 - 1))*(5*(3*r^2 - 1)*(u*v)) := by
      ring
    _ = _ := by rw [hs, hp]; ring

theorem no_rational_centered_three_roots (r u v : ℚ)
    (hpair : r*u + r*v + u*v = -3/5)
    (hprod : 3*(r*u*v) + (r+u+v) = 0) : False := by
  apply centered_discriminant_not_isSquare r
  refine ⟨5*(3*r^2 - 1)*(u-v), ?_⟩
  rw [← pow_two]
  exact (centered_three_roots_discriminant r u v hpair hprod).symm

/-- Unit raw mean of the monic cubic with the three specified roots. -/
def threeNodeUnitMean {K : Type*} [Field K] (r u v : K) : K :=
  1/4 - (r+u+v)*(1/3) + (r*u+r*v+u*v)*(1/2) - r*u*v

/-- Unit raw mean of the same cubic times the abscissa. -/
def threeNodeUnitXMean {K : Type*} [Field K] (r u v : K) : K :=
  1/5 - (r+u+v)*(1/4) + (r*u+r*v+u*v)*(1/3) - (r*u*v)*(1/2)

/-- It is impossible for both vanishing tests to hold on three rational
roots, including a triple with repetitions. -/
theorem no_rational_unit_three_roots (r u v : ℚ)
    (h0 : threeNodeUnitMean r u v = 0) (h1 : threeNodeUnitXMean r u v = 0) : False := by
  unfold threeNodeUnitMean at h0
  unfold threeNodeUnitXMean at h1
  refine no_rational_centered_three_roots (2*r-1) (2*u-1) (2*v-1) ?_ ?_
  · linear_combination 48*h1 - 24*h0
  · linear_combination (-24)*h0

end RKResearch.Certified.RationalQuadratureFive
