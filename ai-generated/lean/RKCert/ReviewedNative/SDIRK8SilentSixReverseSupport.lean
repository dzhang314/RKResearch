module

public import Mathlib.Algebra.Field.Basic
import Mathlib.Tactic.LinearCombination
import Mathlib.Tactic.Ring

@[expose] public section

namespace RKCert.ReviewedNative.SDIRK8SilentSixReverseSupport

/-- A nonzero affine reverse-support multiplier has only one root.
The terminal component of w can therefore pin the silent eighth clock. -/
theorem affineSupportRoot {K : Type*} [Field K]
    (q₀ q₁ x z wx wz : K) (hq : q₁≠0) (hx : wx≠0) (hz : wz≠0)
    (ex : (q₀+q₁*x)*wx=0) (ez : (q₀+q₁*z)*wz=0) : z=x := by
  have ex' := (mul_eq_zero.mp ex).resolve_right hx
  have ez' := (mul_eq_zero.mp ez).resolve_right hz
  have eq : q₁*(z-x)=0 := by linear_combination ez'-ex'
  exact sub_eq_zero.mp ((mul_eq_zero.mp eq).resolve_left hq)

/-- When a silent eighth stage uses the terminal clock and the reverse
quadratic factor is nonzero, its observed gap is literally two. -/
theorem silentTerminalGap {K : Type*} [Field K]
    (g k u : K) (hg : g≠0) (hk : k≠0) (h : g*k*(u-2)=0) : u=2 :=
  sub_eq_zero.mp ((mul_eq_zero.mp h).resolve_left (mul_ne_zero hg hk))

#print axioms affineSupportRoot
#print axioms silentTerminalGap

end RKCert.ReviewedNative.SDIRK8SilentSixReverseSupport
