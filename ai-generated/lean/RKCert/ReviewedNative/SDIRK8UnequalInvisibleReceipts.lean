module

public import Mathlib.Algebra.Field.Basic
import Mathlib.Tactic.LinearCombination
import Mathlib.Tactic.Ring

@[expose] public section

namespace RKCert.ReviewedNative.SDIRK8UnequalInvisibleReceipts

/-- Two physical invisible inputs at the same clock contribute one
scalar clock moment but an independent residual moment. Their strict
cubic-defect feed is determined by the difference of those two reads. -/
theorem invisiblePairFeed {R : Type*} [CommRing R] (g d a b σ : R) :
    b*(σ*(d-g))=σ*((a*g+b*d)-g*(a+b)) := by ring

/-- The affine output-supported shape at three active tail clocks gives
the denominator-free reverse gap compatibility. -/
theorem tailAffineCross {R : Type*} [CommRing R]
    (g x u v k q a b h8 h9 h10 : R)
    (hT : h10=a+b*x)
    (hP : h9=k*(a+b*(x-g*u)))
    (hE : h8=q*(a+b*(x-g*v))) :
    k*u*h8=q*(k*(u-v)*h10+v*h9) := by
  rw [hT,hP,hE]
  ring

/-- A silent third-from-last row does not need a normalized reverse
weight. Its two actual weighted successor taps suffice to determine
its own clock in terms of the penultimate gap. -/
theorem silentThirdClock {K : Type*} [Field K]
    (g x c z u k s t w n : K)
    (hg : g≠0) (hu : u≠0) (hw : w≠0)
    (hd : x-c=g*u) (hk : k=1+2*u-u^2)
    (hs : s+t=0)
    (hW : w= -2*((1-c)*s+(1-x)*t))
    (hN : n= -g^2*(k*s+t))
    (hp : (z-x)*w= -k*n) :
    2*(z-x)=g*k*(u-2) := by
  have hW' : w=2*(x-c)*t := by linear_combination hW-2*(1-c)*hs
  have hN' : n= -g^2*(1-k)*t := by linear_combination hN-g^2*k*hs
  have ht : t≠0 := by
    intro he
    exact hw (by simp [hW',he])
  have d : (2*(z-x)*(x-c)-k*g^2*(1-k))*t=0 := by
    linear_combination hp-(z-x)*hW'-k*hN'
  have e := (mul_eq_zero.mp d).resolve_right ht
  rw [hd] at e
  have f : (2*(z-x)-g*k*(u-2))*(g*u)=0 := by
    linear_combination e-k*g^2*hk
  exact sub_eq_zero.mp ((mul_eq_zero.mp f).resolve_right (mul_ne_zero hg hu))

end RKCert.ReviewedNative.SDIRK8UnequalInvisibleReceipts
