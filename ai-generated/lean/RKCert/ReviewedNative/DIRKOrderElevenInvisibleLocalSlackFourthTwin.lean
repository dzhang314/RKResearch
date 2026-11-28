import Mathlib.Algebra.CharZero.Defs
import Mathlib.Algebra.Field.Defs
import Mathlib.Tactic.LinearCombination
import Mathlib.Tactic.NormNum
import Mathlib.Tactic.Ring

namespace RKCert.ReviewedNative.DIRKOrderElevenInvisibleLocalSlackFourthTwin

/-- Integer numerator of the determinant of the two actual remainders.
The scales on the rows are 300 and 1500, respectively. -/
theorem cleared_remainder_determinant {K : Type*} [CommRing K] (s : K) :
    (-100*s^2+15*s-9)*(100*s^2-45*s) -
    (50*s^2+15*s)*(-200*s^2-45*s+27) = 2250*s^2*(5*s-1) := by ring

theorem live_remainder_pin {K : Type*} [Field K] [CharZero K] {s a : K}
    (hs : s ≠ 0)
    (h0 : 100*s^2-45*s = a*(50*s^2+15*s))
    (h1 : -200*s^2-45*s+27 = a*(-100*s^2+15*s-9)) :
    5*s=1 := by
  have hd : 2250*s^2*(5*s-1)=0 := by
    rw [← cleared_remainder_determinant, h0, h1]
    ring
  have hb : (2250 : K)*s^2 ≠ 0 := mul_ne_zero (by norm_num) (pow_ne_zero 2 hs)
  exact sub_eq_zero.mp ((mul_eq_zero.mp hd).resolve_left hb)

/-- A matched fourth strict prefix with a shared slack clock pays
for the second primitive without dividing by its reverse cubic. -/
theorem matched_twin_second_primitive {K : Type*} [Field K]
    {b G rho I_mark I2 : K} (hb : b≠0) (hr : rho=0)
    (hing : I_mark = -I2) (h : b*I_mark=G*(-rho)) :
    I2=0 := by
  rw [hr, neg_zero, mul_zero] at h
  have hi : I_mark=0 := (mul_eq_zero.mp h).resolve_left hb
  exact neg_eq_zero.mp (hing.symm.trans hi)

theorem product_coordinates {R : Type*} [CommRing R]
    {c0 c1 c2 c3 a B : R}
    (h1 : c0*a=c1) (h2 : c0*B=c2) (h3 : c0*(a*B)=c3) :
    c0*c3-c1*c2=0 := by
  rw [← h1, ← h2, ← h3]
  ring

end RKCert.ReviewedNative.DIRKOrderElevenInvisibleLocalSlackFourthTwin

open RKCert.ReviewedNative.DIRKOrderElevenInvisibleLocalSlackFourthTwin
#print axioms cleared_remainder_determinant
#print axioms live_remainder_pin
#print axioms matched_twin_second_primitive
#print axioms product_coordinates
