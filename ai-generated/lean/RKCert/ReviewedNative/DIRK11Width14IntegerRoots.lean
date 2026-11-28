module

public import RKCert.ReviewedNative.DIRK11Width14IntegerData
public import Mathlib.Analysis.Real.Sqrt
import Mathlib.Tactic.Linarith
import Mathlib.Tactic.Positivity

@[expose] public section

/-! A real place for the exact width-fourteen coefficient tower.
The fourth constant reduction has all positive coefficients in the
first three positive radicals, so its quadratic has a positive root. -/
namespace RKResearch.Certified.DIRK11Width14IntegerData
open QuadTowerIntReplay

theorem positive_real_roots :
    ∃ x y z w : ℝ, 0 < x ∧ 0 < y ∧ 0 < z ∧ 0 < w ∧ Roots reductions x y z w := by
  let x := Real.sqrt 15
  have xp : 0 < x := Real.sqrt_pos.2 (by norm_num)
  have xx : x*x = 15 := Real.mul_self_sqrt (by norm_num)
  have x5 : x < 5 := by
    by_contra! h
    nlinarith [mul_nonneg (show 0 ≤ x+5 by linarith) (show 0 ≤ x-5 by linarith)]
  have byp : 0 < 495+66*x := by positivity
  have bzp : 0 < 495-66*x := by linarith
  let y := Real.sqrt (495+66*x)
  let z := Real.sqrt (495-66*x)
  have yp : 0 < y := Real.sqrt_pos.2 byp
  have zp : 0 < z := Real.sqrt_pos.2 bzp
  have yy : y*y = 495+66*x := Real.mul_self_sqrt byp.le
  have zz : z*z = 495-66*x := Real.mul_self_sqrt bzp.le
  let a := val8 x y z reductions.fourth0
  let b := val8 x y z reductions.fourth1
  have ap : 0 < a := by
    unfold a
    norm_num [val8,val4,val2,atRoot,reductions]
    positivity
  let d := b*b+4*a
  have dr : 0 ≤ d := by unfold d; nlinarith [mul_self_nonneg b]
  have ds : (Real.sqrt d)*(Real.sqrt d)=d := Real.mul_self_sqrt dr
  let w := (b+Real.sqrt d)/2
  have wp : 0 < w := by
    by_contra! h
    have sn := Real.sqrt_nonneg d
    have both : 0 ≤ (-b-Real.sqrt d)*(-b+Real.sqrt d) := by
      apply mul_nonneg <;> dsimp [w] at h <;> linarith
    dsimp [d] at ds
    nlinarith
  refine ⟨x,y,z,w,xp,yp,zp,wp,?_,?_,?_,?_⟩
  · exact xx
  · simpa [reductions,val2,atRoot,add_comm,mul_comm] using yy
  · simpa [reductions,val4,val2,atRoot,sub_eq_add_neg,add_comm,mul_comm] using zz
  · change w*w=a+w*b
    dsimp [w,d] at *
    nlinarith

end RKResearch.Certified.DIRK11Width14IntegerData
