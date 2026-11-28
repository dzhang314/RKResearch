import Mathlib.Tactic.Ring

/-! Ring identities underlying the first-clean-fifth stage exclusions.
The causal grade-four reduction and finite affine fibers are a separate proof. -/
namespace RKResearch.Certified.SDIRKEightFourZeroFirstCleanFive

theorem two_fifth_reads_eliminate_fourth_residual {R : Type*} [CommRing R]
    {tap z p D B r sig rho : R}
    (hD : tap * (z-p) = D) (hB : tap * r = B) (hσ : sig*z = rho) :
    B*(rho-sig*p)-D*r*sig=0 := by
  rw [←hD, ←hB, ←hσ]
  ring

theorem singular_fourth_recovery {F : Type*} [Field F] {D B z p r : F}
    (hne : B ≠ 0) (h : B*(z-p) = D*r) :
    z = p+D*r/B := by
  have h' : z-p = D*r/B := (eq_div_iff hne).2 (by simpa [mul_comm] using h)
  calc
    z = p+(z-p) := by ring
    _ = p+D*r/B := by rw [h']

theorem two_clean_reads_cancel_first_clock {R : Type*} [CommRing R]
    {r₁a r₂a r₁b r₂b s₁b s₂b tap : R}
    (h₁ : s₁b-r₁b=tap*r₁a) (h₂ : s₂b-r₂b=tap*r₂a) :
    r₂a*(s₁b-r₁b)-r₁a*(s₂b-r₂b)=0 := by
  rw [h₁,h₂]
  ring

def twiceStar {R : Type*} [CommRing R] (X : R) : R := 4*X-2-X^2

theorem twice_star_first {R : Type*} [CommRing R] :
    twiceStar (1 : R) = 1 := by
  unfold twiceStar
  ring

theorem twice_star_second {R : Type*} [CommRing R] (u : R) :
    twiceStar (1+u) = 1+2*u-u^2 := by
  unfold twiceStar
  ring

theorem twice_star_third {R : Type*} [CommRing R] (u : R) :
    twiceStar (3-u) = 1+2*u-u^2 := by
  unfold twiceStar
  ring

theorem twice_arithmetic_third {R : Type*} [CommRing R]
    {u H tap : R} (h : tap*H=2*u*(3*u-2)) :
    H*twiceStar (1+2*u)+2*(3*u-2)*(2*u)*u =
      H*(1+4*u-4*u^2+2*tap*u) := by
  calc
    _ = H*(1+4*u-4*u^2)+2*u*(2*u*(3*u-2)) := by
      unfold twiceStar
      ring
    _ = H*(1+4*u-4*u^2)+2*u*(tap*H) := by rw [h]
    _ = _ := by ring

end RKResearch.Certified.SDIRKEightFourZeroFirstCleanFive
