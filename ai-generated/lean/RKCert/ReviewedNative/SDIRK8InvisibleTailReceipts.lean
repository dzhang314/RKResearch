module

public import Mathlib.Algebra.Field.Basic
import Mathlib.Tactic.LinearCombination
import Mathlib.Tactic.Ring

@[expose] public section

namespace RKCert.ReviewedNative.SDIRK8InvisibleTailReceipts

/-- A silent third-from-last physical coordinate has two weighted strict
successor taps. This is the scalar parameter relation without using an
inverse weight at that coordinate. -/
theorem silentThirdParameter {K : Type*} [Field K]
    (g x z u k s t w n : K)
    (hg : g≠0) (hu : u≠0) (hw : w≠0)
    (hx : x=1-g) (hd : x-z=g*u) (hk : k=1+2*u-u^2)
    (hs : s+t=0)
    (hW : w= -2*((1-z)*s+(1-x)*t))
    (hN : n= -g^2*(k*s+t))
    (hp : (g-x)*w= -k*n) :
    g*(4-k*(u-2))=2 := by
  have hW' : w=2*(x-z)*t := by linear_combination hW-2*(1-z)*hs
  have hN' : n= -g^2*(1-k)*t := by linear_combination hN-g^2*k*hs
  have ht : t≠0 := by
    intro he
    exact hw (by simp [hW',he])
  have d : (2*(g-x)*(x-z)-k*g^2*(1-k))*t=0 := by
    linear_combination hp-(g-x)*hW'-k*hN'
  have e := (mul_eq_zero.mp d).resolve_right ht
  rw [hd,hx] at e
  have hf : (g*(4-k*(u-2))-2)*(g*u)=0 := by
    linear_combination e-k*g^2*hk
  exact sub_eq_zero.mp ((mul_eq_zero.mp hf).resolve_right (mul_ne_zero hg hu))

/-- At the half diagonal the same tail read gives the required ratio of
the penultimate and terminal cubic defects. -/
theorem halfSilentThirdRatio {K : Type*} [Field K]
    (g δ t w lam μ h9 h10 : K) (ht : t≠0)
    (hw : w=2*δ*t) (hl : lam*w= -g^2*t)
    (h9e : h9= -μ*g^2*δ) (h10e : h10=μ*lam*g^2) :
    g^2*h9=2*δ^2*h10 := by
  have q : (2*δ*lam+g^2)*t=0 := by linear_combination hl-lam*hw
  have q' := (mul_eq_zero.mp q).resolve_right ht
  linear_combination g^2*h9e-2*δ^2*h10e-μ*g^2*δ*q'

end RKCert.ReviewedNative.SDIRK8InvisibleTailReceipts
