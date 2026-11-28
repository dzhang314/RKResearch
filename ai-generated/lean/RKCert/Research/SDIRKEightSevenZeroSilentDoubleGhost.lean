import Mathlib.Tactic.Ring.Basic

/-!
Arithmetic receipts for the silent constant-double SDIRK8 chart.
All actual root-order and chronological ingress remains separate.
-/

namespace RKResearch.Certified.SDIRKEightSevenZeroSilentDoubleGhost

variable {R : Type*} [CommRing R]

/-- Two nonzero entries on a collinear off projection must sit at the
same scalar level. -/
theorem nonzero_off_levels_agree [IsDomain R]
    {z₁ z₂ x₁ x₂ ℓ : R} (h₁ : z₁≠0) (h₂ : z₂≠0)
    (e₁ : z₁*x₁=z₁*ℓ) (e₂ : z₂*x₂=z₂*ℓ) :
    x₁=x₂ := by
  have h (z x : R) (hz : z≠0) (e : z*x=z*ℓ) : x=ℓ := by
    have h0 : z*(x-ℓ)=0 := by rw [mul_sub,e,sub_self]
    exact sub_eq_zero.mp ((mul_eq_zero.mp h0).resolve_left hz)
  exact (h z₁ x₁ h₁ e₁).trans (h z₂ x₂ h₂ e₂).symm

/-- Remove the common pure coordinate scalar in the two supported
reverse reads, without dividing by an ordinary weight. -/
theorem supported_ghost_third_clear
    {Bt Br Jt Fr μ t r d : R}
    (ht : -(Bt*Jt)=μ*(t-d)) (hr : Br*Fr=μ*(r-d)) :
    (t-d)*Br*Fr+(r-d)*Jt*Bt=0 := by
  calc
    _ = (t-d)*(Br*Fr)-(r-d)*(-(Bt*Jt)) := by ring1
    _ = _ := by rw [ht,hr]; ring1

end RKResearch.Certified.SDIRKEightSevenZeroSilentDoubleGhost
