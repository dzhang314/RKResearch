import Mathlib.Tactic.Ring.Basic

/-! Scalar affine-plane and centered-root identities for the late finite-gap charts. -/

namespace RKResearch.Certified.SDIRKEightEightZeroAffineLateFinite

variable {R : Type*} [CommRing R]

theorem affine_plane {lam v d bs bt br k k₃ : R}
    (hs : bs=lam*(v-d)) (ht : k*bt=lam*(-d))
    (hr : k₃*br=lam*(-v-d)) :
    bs+k₃*br=2*(k*bt) := by
  rw [hs,hr,ht]
  ring1

theorem cleared_plane {h k Q k₃ bs bt br : R}
    (hp : h*k₃=-(k*Q)) (hr : bs+k₃*br=2*(k*bt)) :
    h*bs-2*(h*k)*bt-(k*Q)*br=0 := by
  calc
    _ = h*bs-2*(h*k)*bt+(-(k*Q))*br := by ring1
    _ = h*(bs+k₃*br-2*(k*bt)) := by
      rw [← hp]
      ring1
    _ = 0 := by
      rw [hr]
      ring1

theorem centered_jump_product (m d v x : R) :
    ((m+d)-(m+x))*((m+d)-(m+v))*((m+d)-m)*((m+d)-(m-v)) =
    (d-x)*d*(d^2-v^2) := by
  ring1

end RKResearch.Certified.SDIRKEightEightZeroAffineLateFinite
