module

public import RKCert.ERKOrderNineOneOffEndpoint
public import RKCert.ERKOrderNinePencil

@[expose] public section

namespace RKCert.Paired.OneOff
open Polynomial RKCert.GoodPrimeDense

variable {K : Type*} [Field K] [CharZero K]

/-- The checked integer polynomial is the manuscript's
Christoffel--Darboux numerator divided by its exact linear factor. -/
theorem endpointF_jacobi (d z : K) :
    (z-2*d)*endpointF d z =
      588*(lobattoCubic.eval (2*d)*(lobattoPencil 0).eval z -
        (lobattoPencil 0).eval (2*d)*lobattoCubic.eval z) := by
  simp [endpointF,readGrid,endpointFData,GoodPrimeDense.read,lobattoCubic,lobattoPencil]
  ring

theorem eval_lobattoPencil_affine (l x : K) :
    (lobattoPencil l).eval x = (lobattoPencil 0).eval x + l*lobattoCubic.eval x := by
  simp [lobattoCubic,lobattoPencil]
  ring

theorem endpointF_zero_of_cubic_roots {d z : K} (hne : z≠2*d)
    (ht : (lobattoCubic : K[X]).eval (2*d)=0) (hz : (lobattoCubic : K[X]).eval z=0) :
    endpointF d z=0 := by
  have h := endpointF_jacobi d z
  rw [ht,hz,zero_mul,mul_zero,sub_self,mul_zero] at h
  exact (mul_eq_zero.mp h).resolve_left (sub_ne_zero.mpr hne)

theorem endpointF_zero_of_pencil_roots {l d z : K} (hne : z≠2*d)
    (ht : (lobattoPencil l).eval (2*d)=0) (hz : (lobattoPencil l).eval z=0) :
    endpointF d z=0 := by
  rw [eval_lobattoPencil_affine] at ht hz
  have h := endpointF_jacobi d z
  have h0 : (z-2*d)*endpointF d z=0 := by
    linear_combination h - 588*lobattoCubic.eval z*ht + 588*lobattoCubic.eval (2*d)*hz
  exact (mul_eq_zero.mp h0).resolve_left (sub_ne_zero.mpr hne)

/-- A cubic or free quartic beta polynomial on the two repeated fibres
cannot also vanish at the first clean node d when the seventh-row
slope obstruction holds. -/
theorem endpoint_jacobi_three_roots_impossible {P : K[X]} {d z : K}
    (hd : d≠0) (hzd : z≠d) (hzt : z≠2*d)
    (hP : (∃ c : K,c≠0 ∧ P=C c*lobattoCubic) ∨
      (∃ c l : K,c≠0 ∧ P=C c*lobattoPencil l))
    (ht : P.eval (2*d)=0) (hz : P.eval z=0) (hd' : P.eval d=0)
    (hg : endpointG d z=0) : False := by
  have hdt : d≠2*d := by intro e; apply hd; linear_combination -e
  rcases hP with ⟨c,hc,rfl⟩|⟨c,l,hc,rfl⟩
  · simp only [eval_mul,eval_C,mul_eq_zero,or_iff_right hc] at ht hz hd'
    exact endpoint_nonzero hzd (endpointF_zero_of_cubic_roots hdt ht hd')
      (endpointF_zero_of_cubic_roots hzt ht hz) hg
  · simp only [eval_mul,eval_C,mul_eq_zero,or_iff_right hc] at ht hz hd'
    exact endpoint_nonzero hzd (endpointF_zero_of_pencil_roots hdt ht hd')
      (endpointF_zero_of_pencil_roots hzt ht hz) hg

end RKCert.Paired.OneOff
