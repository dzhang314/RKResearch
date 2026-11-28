module

public import Mathlib.Algebra.Field.Basic
import Mathlib.Tactic.FinCases
import Mathlib.Tactic.LinearCombination
import Mathlib.Tactic.NormNum
import Mathlib.Tactic.Ring
import Mathlib.Data.Rat.Defs
import Mathlib.Data.Fintype.Basic

@[expose] public section

namespace RKCert.ReviewedNative.SDIRK8EightActiveReverseLiveDeflation

/-- Deflate an actual reverse-live node from a distinct-site nodal
derivative. No amplitude or clock difference is canceled. -/
theorem deflatedAtOrdinaryNode {R : Type*} [CommRing R]
    (c z d w b h T S scale : R)
    (ht : T=(c-z)*d*w) (hs : S=T*h)
    (hr : b*h=scale*(c-z)*w) : S*(b*d)=scale*T^2 := by
  rw [hs]
  calc
    T*h*(b*d) = (T*d)*(b*h) := by ring
    _ = (T*d)*(scale*(c-z)*w) := by rw [hr]
    _ = scale*T*((c-z)*d*w) := by ring
    _ = scale*T^2 := by rw [← ht]; ring

/-- At the actual ordinarily silent eighth, its clock comparison
and its penultimate affine read imply the cleared gap equation. -/
theorem silentEighthRead {R : Type*} [Field R]
    (x c z g k u hx hc : R) (hγ : g ≠ 0) (hk : k ≠ 0)
    (hclock : c=x-g*u) (hz : 2*(z-x)=g*k*(u-2))
    (hr : (x-z)*hc=k*(c-z)*hx) : (u-2)*hc=(2*u+k*(u-2))*hx := by
  rw [hclock] at hr
  apply mul_left_cancel₀ (mul_ne_zero hγ hk)
  linear_combination -2*hr - (hc-k*hx)*hz

/-- The shifted Legendre quintic is orthogonal to the first five
scalar powers under formal integration on the unit interval. -/
theorem legendreFiveMoments (j : Fin 5) :
    let a : ℚ := j.val;
    -1/(a+1) + 30/(a+2) - 210/(a+3) + 560/(a+4) - 630/(a+5) + 252/(a+6) = 0 := by
  fin_cases j <;> norm_num

/-- Consecutive shifted Legendre rows cannot be proportional at different
clocks with both quartic values nonzero. This is the cleared recurrence
certificate, leaving characteristic and nonzero guards to the application. -/
theorem frontRankConflict {R : Type*} [CommRing R]
    (a b a₃ a₄ a₅ b₃ b₄ b₅ : R)
    (ha : 5*a₅+4*a₃=9*(2*a-1)*a₄)
    (hb : 5*b₅+4*b₃=9*(2*b-1)*b₄)
    (hm₃ : a₃*b₄=b₃*a₄) (hm₅ : a₅*b₄=b₅*a₄) :
    18*(a-b)*a₄*b₄=0 := by
  linear_combination 5*hm₅+4*hm₃-b₄*ha+a₄*hb

#print axioms deflatedAtOrdinaryNode
#print axioms silentEighthRead
#print axioms legendreFiveMoments
#print axioms frontRankConflict

end RKCert.ReviewedNative.SDIRK8EightActiveReverseLiveDeflation
