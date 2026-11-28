import Mathlib.Tactic.Ring.Basic

/-! Reproducing-kernel and three-read determinant gates for a paired star. -/

namespace RKResearch.Certified.SDIRKEightEightZeroStarUnequalFront

variable {R : Type*} [CommRing R]

def l₁ (q : R) := 2*q-1
def l₂ (q : R) := 6*q^2-6*q+1
def l₃ (q : R) := 20*q^3-30*q^2+12*q-1

def k₀ (q : R) := 1-3*l₁ q+5*l₂ q-7*l₃ q
def k₁ (q : R) := 6*l₁ q-30*l₂ q+84*l₃ q
def k₂ (q : R) := 30*l₂ q-210*l₃ q
def k₃ (q : R) := 140*l₃ q

/-- The degree-three reproducing kernel on the unit interval,
with denominators cleared before specialization. -/
theorem cleared_kernel_moments (q : R) :
    12*k₀ q+6*k₁ q+4*k₂ q+3*k₃ q=12 ∧
    30*k₀ q+20*k₁ q+15*k₂ q+12*k₃ q=60*q ∧
    20*k₀ q+15*k₁ q+12*k₂ q+10*k₃ q=60*q^2 ∧
    105*k₀ q+84*k₁ q+70*k₂ q+60*k₃ q=420*q^3 := by
  unfold k₀ k₁ k₂ k₃ l₁ l₂ l₃
  exact ⟨by ring1, by ring1, by ring1, by ring1⟩

/-- Actual transfer from the first two rows controls each oriented
two-singleton determinant without dividing by a transfer coefficient. -/
theorem singleton_minor_transfer {ha hb hc ka kb kc a b : R}
    (hh : hc=a*ha+b*hb) (hk : kc=a*ka+b*kb) :
    hb*kc-hc*kb=(-a)*(ha*kb-hb*ka) ∧
    hc*ka-ha*kc=(-b)*(ha*kb-hb*ka) := by
  rw [hh,hk]
  exact ⟨by ring1, by ring1⟩

end RKResearch.Certified.SDIRKEightEightZeroStarUnequalFront
