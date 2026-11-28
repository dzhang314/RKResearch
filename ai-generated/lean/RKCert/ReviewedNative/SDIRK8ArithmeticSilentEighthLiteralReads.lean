module

public import Mathlib.Algebra.Ring.Basic
import Mathlib.Tactic.Ring
import Mathlib.Tactic.LinearCombination

@[expose] public section

namespace RKCert.ReviewedNative.SDIRK8ArithmeticSilentEighthLiteralReads

/-- The actual arithmetic literal third pays the normalized row-sum,
quadratic and cubic reads. The quantities m₂ and l₂ are twice the
second and first strict taps, respectively. In the scaled cubic read
the defect is l₂/6, not the zero-coupling star value. -/
theorem arithmeticLiteralThirdReads {R : Type*} [CommRing R]
    (t a b m₂ l₂ : R) (ht : 2*t^2=1)
    (ha : a=2+2*t) (hb : b=3+4*t)
    (hm : m₂=1+6*t) (hl : l₂=3+2*t) :
    (2+l₂+m₂=2*b) ∧
    (2*b+l₂+m₂*a=b^2) ∧
    (6*b^2+3*l₂+3*m₂*a^2=2*b^3+l₂) := by
  rw [ha,hb,hm,hl]
  refine ⟨?_,?_,?_⟩
  · ring
  · linear_combination -2*ht
  · linear_combination (-18-28*t)*ht

/-- Synthetic deletion of the actual penultimate preserves every
different actual ordinary fifth. This is characteristic-zero
reasoning before reduction; later multiplicities can still merge. -/
theorem deleteRetainsDistinctRoot {R : Type*} [CommRing R] [NoZeroDivisors R]
    (y c value : R) (h : y≠c) (hr : (y-c)*value=0) : value=0 :=
  (mul_eq_zero.mp hr).resolve_left (sub_ne_zero.mpr h)

#print axioms arithmeticLiteralThirdReads
#print axioms deleteRetainsDistinctRoot

end RKCert.ReviewedNative.SDIRK8ArithmeticSilentEighthLiteralReads
