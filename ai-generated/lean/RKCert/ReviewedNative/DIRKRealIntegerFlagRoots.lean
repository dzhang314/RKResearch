module

public import RKCert.ReviewedNative.DIRKRealFlagRoots
public import RKCert.ReviewedNative.DIRKRealIntegerFlagData
import Mathlib.Tactic.NormNum
import Mathlib.Tactic.Ring

@[expose] public section

/-! Transport of the exact real roots to the cleared integral tower.
All coefficients after scaling are compared as rational polynomials. -/
namespace RKResearch.Certified.DIRKRealOrderTenIntegerRoots

open CubicCubicQuadraticReplay DIRKRealOrderTenIntegerData

set_option maxRecDepth 50000
set_option maxHeartbeats 0

theorem scale_inner (x : ℝ) :
    val3 (25*x) reductions.inner =
      (25:ℝ)^3*CubicCubicQuadraticRatReplay.val3 x DIRKRealOrderTenData.reductions.inner := by
  norm_num [val3,v3,reductions,CubicCubicQuadraticRatReplay.val3,DIRKRealOrderTenData.reductions,
    DIRKRealOrderTenRoots.realMap,Rat.mkRat_eq_div]
  ring

theorem scale_middle (x y : ℝ) :
    val9 (25*x) (rootScaleY*y) reductions.middle =
      (rootScaleY:ℝ)^3*CubicCubicQuadraticRatReplay.val9 x y DIRKRealOrderTenData.reductions.middle := by
  norm_num [val9,val3,v3,reductions,rootScaleY,CubicCubicQuadraticRatReplay.val9,
    CubicCubicQuadraticRatReplay.val3,DIRKRealOrderTenData.reductions,
    DIRKRealOrderTenRoots.realMap,Rat.mkRat_eq_div]
  ring

theorem scale_outer (x y z : ℝ) :
    val (25*x) (rootScaleY*y) (rootScaleY*z) reductions.outer =
      (rootScaleY:ℝ)^2*CubicCubicQuadraticRatReplay.val x y z DIRKRealOrderTenData.reductions.outer := by
  norm_num [val,val9,val3,v2,v3,reductions,rootScaleY,CubicCubicQuadraticRatReplay.val,
    CubicCubicQuadraticRatReplay.val9,CubicCubicQuadraticRatReplay.val3,
    DIRKRealOrderTenData.reductions,DIRKRealOrderTenRoots.realMap,Rat.mkRat_eq_div]
  ring

theorem exists_roots : ∃ x y z : ℝ, Roots reductions x y z := by
  obtain ⟨x,y,z,h⟩ := DIRKRealOrderTenRoots.exists_roots
  exact ⟨25*x,rootScaleY*y,rootScaleY*z,⟨
    by rw [mul_pow,h.inner,scale_inner],
    by rw [mul_pow,h.middle,scale_middle],
    by rw [mul_pow,h.outer,scale_outer]⟩⟩

end RKResearch.Certified.DIRKRealOrderTenIntegerRoots

#print axioms RKResearch.Certified.DIRKRealOrderTenIntegerRoots.exists_roots
