import Mathlib.Tactic.Ring

/-! Exact scalar and integer receipts for the four-ordinary-site pure branch. -/
namespace RKResearch.Certified.SDIRKEightFiveZeroPureFourOrdinary

def firstZeroCubic {R : Type*} [CommRing R] (u : R) : R :=
  4*u^3-12*u^2+3*u+2

def coincidentGaussGate {R : Type*} [CommRing R] (u : R) : R := -12*u^2-12*u-3

theorem coincident_gauss_bezout {R : Type*} [CommRing R] (u : R) :
    (-6*u^2+20*u-11)*coincidentGaussGate u +
    (-18*u-12)*firstZeroCubic u = (9 : R) := by
  unfold coincidentGaussGate firstZeroCubic
  ring

theorem front_rear_literal_coprimality :
    Nat.gcd 50962055131435661 (2^57*5^12*7^6*3517*10759456151) = 1 ∧
    Nat.gcd 50962055131435661 (2^6*3^5) = 1 ∧
    Nat.gcd 50962055131435661
      (2^112*3^45*5^48*7^25*853*9453064485587*77302364448451*12847924825634167528081)
      = 1 := by
  decide +kernel

end RKResearch.Certified.SDIRKEightFiveZeroPureFourOrdinary
