import Mathlib.Tactic.Ring
import Mathlib.Tactic.LinearCombination

namespace RKCert.ReviewedNative.DIRKOrderElevenInvisibleSixAlphaOneFifthCompensator

variable {K : Type*} [CommRing K]

theorem fifth_transfer {d z x l w eta nu : K}
    (hn : nu=eta-(1+l)*w)
    (h : d*((1+l)*w-eta)=(z-x)*(l*w-eta)) :
    d*nu=(z-x)*(nu+w) := by
  rw [hn]
  linear_combination -h

theorem zero_iff_literal_gap [IsDomain K] {d b x v w : K}
    (hv : v≠0) (hbx : b≠x) (h : d*v=(b-x)*(v+w)) :
    w=0 ↔ d=b-x := by
  constructor
  · intro hw
    have hh : (d-(b-x))*v=0 := by
      rw [hw] at h
      linear_combination h
    exact sub_eq_zero.mp ((mul_eq_zero.mp hh).resolve_right hv)
  · intro hd
    have hh : (b-x)*w=0 := by
      rw [hd] at h
      linear_combination -h
    exact (mul_eq_zero.mp hh).resolve_left (sub_ne_zero.mpr hbx)

end RKCert.ReviewedNative.DIRKOrderElevenInvisibleSixAlphaOneFifthCompensator
