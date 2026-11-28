module

public import Mathlib.Algebra.Ring.Basic
public import Mathlib.Algebra.CharZero.Defs
import Mathlib.Tactic.LinearCombination
import Mathlib.Tactic.Ring
import Mathlib.Tactic.NormNum

@[expose] public section

namespace RKCert.ReviewedNative.SDIRK8ArithmeticLiteralSecondGates

/-- The two arithmetic literal clocks are not interchangeable by the
star-front permutation: the inverted actual strict coupling is nonzero. -/
theorem arithmeticCouplingNonzero {K : Type*} [CommRing K] [CharZero K]
    (t m : K) (ht : 2*t^2=1) (hm : 2*m=1+6*t) : m≠0 := by
  intro hz
  rw [hz, mul_zero] at hm
  have hn : (1+6*t)*(1-6*t) = -(17 : K) := by
    linear_combination -18*ht
  rw [← hm, zero_mul] at hn
  exact (by norm_num : (17 : K) ≠ 0) (neg_eq_zero.mp hn.symm)

/-- Chronology-free paid cross read at the genuine ordinary tail. -/
theorem literalSecondPaidRatio {K : Type*} [CommRing K] [NoZeroDivisors K]
    (c d x z k Hc Hd Hx h j Rc Rd : K)
    (haf : (x-z)*Hc=k*(c-z)*Hx)
    (hTail : h*Hd+2*j*Hc=k*j*Hx)
    (hclock : d-z=2*(c-z)-(x-z))
    (hcross : Rc*Hd=Rd*Hc)
    (hk : k≠0) (hHx : Hx≠0) :
    h*(c-z)*Rd+j*(d-z)*Rc=0 := by
  have hd : (x-z)*(h*Hd+j*Hc+j*Hc-k*j*Hx)=0 := by
    linear_combination (x-z)*hTail
  have hr : k*Hx*(h*(c-z)*Rd+j*(d-z)*Rc)=0 := by
    linear_combination
      Rc*hd - h*(x-z)*hcross - (h*Rd+2*j*Rc)*haf
        + k*Hx*j*Rc*hclock
  exact (mul_eq_zero.mp hr).resolve_left (mul_ne_zero hk hHx)

#print axioms arithmeticCouplingNonzero
#print axioms literalSecondPaidRatio

end RKCert.ReviewedNative.SDIRK8ArithmeticLiteralSecondGates
