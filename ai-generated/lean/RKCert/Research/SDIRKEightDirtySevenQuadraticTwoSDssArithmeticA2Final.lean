import Mathlib.Tactic.Ring.Basic

namespace RKResearch.Certified.SDIRKEightDirtySevenQuadraticTwoSDssArithmeticA2Final

variable {K : Type*} [CommRing K]

theorem primitive_step_common_root (A B C scale u v : K)
    (h : scale*C=u*A-v*B) (hA : A=0) (hB : B=0) :
    scale*C=0 := by
  rw [h,hA,hB]
  ring1

theorem remove_actual_nonzero_guard [IsDomain K] (E P G : K)
    (he : E=G*P) (hg : G≠0) (h : E=0) :
    P=0 := by
  rw [he] at h
  exact (mul_eq_zero.mp h).resolve_left hg

end RKResearch.Certified.SDIRKEightDirtySevenQuadraticTwoSDssArithmeticA2Final
