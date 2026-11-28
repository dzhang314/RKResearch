import Mathlib.Tactic.Ring
import Mathlib.Tactic.LinearCombination

namespace RKCert.ReviewedNative.DIRKOrderElevenInvisibleSixAlphaOneBetaTwoZeroFifth

variable {K : Type*} [CommRing K]

/-- The actual fourth sample of the commutator multiple:
only the live carrier is cancelled. -/
theorem center_fourth [IsDomain K] {B5 ell u j lam xi : K}
    (hu : u≠0) (hB : B5=ell*u) (hread : lam*B5+j*xi*u=0) :
    j*xi= -lam*ell := by
  have h : u*(j*xi+lam*ell)=0 := by
    linear_combination hread-lam*hB
  have hh := (mul_eq_zero.mp h).resolve_left hu
  linear_combination hh

/-- The old sample after removal of its common inverse multiplication.
No carrier, tableau coefficient, or clock is inverted in this transfer. -/
theorem old_column {m U B5 j D H ell lam xi eta y V : K}
    (hB : m*B5=j*D) (hU : m*U=H)
    (hf : j*xi= -ell*lam+j*eta*(y-V))
    (hread : lam*B5+j*xi*U=0) :
    lam*(j*D-ell*H)+j*eta*(y-V)*H=0 := by
  calc
    lam*(j*D-ell*H)+j*eta*(y-V)*H
        = lam*(m*B5)+(j*xi)*(m*U) := by
          rw [hB,hU,hf]
          ring
    _ = m*(lam*B5+j*xi*U) := by ring
    _ = 0 := by rw [hread,mul_zero]

end RKCert.ReviewedNative.DIRKOrderElevenInvisibleSixAlphaOneBetaTwoZeroFifth
