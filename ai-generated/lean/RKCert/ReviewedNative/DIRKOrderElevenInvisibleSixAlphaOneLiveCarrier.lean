import Mathlib.Algebra.Ring.Basic

namespace RKCert.ReviewedNative.DIRKOrderElevenInvisibleSixAlphaOneLiveCarrier

variable {K : Type*} [CommRing K]

theorem monic_adjacent {a0 a1 a2 E : K}
    (h : a0 + a1 * E + a2 * E ^ 2 = 0) :
    (a2 * E) ^ 2 + a1 * (a2 * E) + a2 * a0 = 0 := by
  calc
    (a2 * E) ^ 2 + a1 * (a2 * E) + a2 * a0 =
        a2 * (a0 + a1 * E + a2 * E ^ 2) := by
      simp only [pow_two, mul_add, mul_assoc, mul_comm, mul_left_comm,
        add_assoc, add_comm, add_left_comm]
    _ = 0 := by simp [h]

theorem carrier_homogeneous_three {a2 E g0 g1 g2 g3 : K}
    (h : g0 + g1 * E + g2 * E ^ 2 + g3 * E ^ 3 = 0) :
    a2 ^ 3 * g0 + a2 ^ 2 * g1 * (a2 * E) +
      a2 * g2 * (a2 * E) ^ 2 + g3 * (a2 * E) ^ 3 = 0 := by
  calc
    _ = a2 ^ 3 * (g0 + g1 * E + g2 * E ^ 2 + g3 * E ^ 3) := by
      simp only [show (2 : Nat) = 1 + 1 from rfl,
        show (3 : Nat) = (1 + 1) + 1 from rfl, pow_add, pow_one,
        mul_add, mul_assoc, mul_comm, mul_left_comm]
    _ = 0 := by simp [h]

theorem scaled_carrier_zero_iff [IsDomain K] {q a2 E : K}
    (hq : q ≠ 0) (ha2 : a2 ≠ 0) :
    a2 * (q * E) = 0 ↔ E = 0 := by
  simp [mul_eq_zero, hq, ha2]

theorem scaled_clock_contact_iff [IsDomain K] {q B z : K}
    (hq : q ≠ 0) : B * q - q * z = 0 ↔ B = z := by
  have h : B * q - q * z = q * (B - z) := by rw [mul_sub, mul_comm B q]
  rw [h, mul_eq_zero, or_iff_right hq, sub_eq_zero]

theorem guarded_evaluation_ne [IsDomain K] {G h Q u v : K}
    (hG : G ≠ 0) (hh : h = 0) (hQ : Q = 0) :
    G ≠ (G * h) * u + (G * Q) * v := by
  simpa [hh, hQ] using hG

end RKCert.ReviewedNative.DIRKOrderElevenInvisibleSixAlphaOneLiveCarrier

open RKCert.ReviewedNative.DIRKOrderElevenInvisibleSixAlphaOneLiveCarrier
#print axioms monic_adjacent
#print axioms carrier_homogeneous_three
#print axioms scaled_carrier_zero_iff
#print axioms scaled_clock_contact_iff
#print axioms guarded_evaluation_ne
