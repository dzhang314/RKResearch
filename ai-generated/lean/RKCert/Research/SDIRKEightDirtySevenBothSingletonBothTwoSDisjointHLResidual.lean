import Mathlib.Tactic.Ring.Basic

/-!
Exact scalar gates for projecting the residual (off-rank-curve) clock chart.
The paid ingress and definite resultant and number-field computations are separate.
-/
namespace RKCert.Research.SDIRKEightDirtySevenBothSingletonBothTwoSDisjointHLResidual

theorem pseudo_remainder_vanishes {R : Type*} [CommRing R]
    (a b p q : R) (hp : p = 0) (hq : q = 0) :
    a * p - b * q = 0 := by
  simp [hp, hq]

theorem affine_common_root_minor {R : Type*} [CommRing R]
    (u v s t y : R) (h₁ : u + v * y = 0) (h₂ : s + t * y = 0) :
    u * t - v * s = 0 := by
  calc
    u * t - v * s = t * (u + v * y) - v * (s + t * y) := by ring
    _ = 0 := by simp [h₁, h₂]

end RKCert.Research.SDIRKEightDirtySevenBothSingletonBothTwoSDisjointHLResidual
