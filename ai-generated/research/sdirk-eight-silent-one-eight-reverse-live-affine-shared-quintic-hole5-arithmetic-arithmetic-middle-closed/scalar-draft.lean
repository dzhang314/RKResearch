module

public import Mathlib.Algebra.Ring.Basic
import Mathlib.Tactic.LinearCombination

@[expose] public section

namespace RKCert.ReviewedNative.SDIRK8ReverseLiveAffineSharedQuinticHoleFiveArithmeticArithmeticMiddle

/-- The literal arithmetic rear removes exactly the common covector scale
minus (γ*u)^2 from the actual terminal equality. The missing clock n is
a true ordinary clock, not the ordinarily silent one. -/
theorem actualArithmeticMiddleTerminal {R : Type*} [CommRing R] [NoZeroDivisors R]
    (γ u x c d n Hc Hx Mc Mx : R)
    (hγ : γ≠0) (hu : u≠0)
    (hc : c=x-γ*u) (hd : d=x-2*γ*u)
    (h : Hc*Mc*(c-d)*(c-x)*(c-n)=Hx*Mx*(x-c)*(x-d)*(x-n)) :
    Hc*Mc*(c-n)+2*Hx*Mx*(x-n)=0 := by
  have hz : (γ*u)^2*(Hc*Mc*(c-n)+2*Hx*Mx*(x-n))=0 := by
    rw [hc,hd] at h ⊢
    linear_combination -h
  exact (mul_eq_zero.mp hz).resolve_left (pow_ne_zero 2 (mul_ne_zero hγ hu))

/-- In the actual chart the terminal cofactor has a nonzero coefficient
of its missing clock. The homogeneous replay need not divide by it. -/
theorem actualArithmeticTerminalCoefficient {R : Type*} [CommRing R] [NoZeroDivisors R]
    (c x n Uc Ux : R)
    (hTwo : (2:R)≠0) (hxc : x-c≠0) (hUx : Ux≠0)
    (h : Uc*(c-n)+2*Ux*(x-n)=0) :
    Uc+2*Ux≠0 := by
  intro h0
  have hz : 2*(x-c)*Ux=0 := by
    linear_combination h-(c-n)*h0
  exact (mul_ne_zero (mul_ne_zero hTwo hxc) hUx) hz

#print axioms actualArithmeticMiddleTerminal
#print axioms actualArithmeticTerminalCoefficient

end RKCert.ReviewedNative.SDIRK8ReverseLiveAffineSharedQuinticHoleFiveArithmeticArithmeticMiddle
