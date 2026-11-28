import Mathlib.Algebra.Field.Defs
import Mathlib.Tactic.LinearCombination

namespace RKCert.ReviewedNative.DIRKOrderElevenInvisibleLocalSlackFifthTwin

theorem true_primitive_factor {R : Type*} [CommRing R] {d q a s j : R}
    (h0 : s=q*j) (h1 : (1+a)*s=d*j) :
    (d-q*(1+a))*s=0 := by
  linear_combination d*h0 - q*h1

theorem incompatible_multipliers {R : Type*} [CommRing R] {d q a : R}
    (hd : d≠0) (h0 : d=q*(1+a)) (h1 : d=a*q) :
    False := by
  have hq : q=0 := by linear_combination h1 - h0
  exact hd (by simpa [hq] using h0)

end RKCert.ReviewedNative.DIRKOrderElevenInvisibleLocalSlackFifthTwin

open RKCert.ReviewedNative.DIRKOrderElevenInvisibleLocalSlackFifthTwin
#print axioms true_primitive_factor
#print axioms incompatible_multipliers
