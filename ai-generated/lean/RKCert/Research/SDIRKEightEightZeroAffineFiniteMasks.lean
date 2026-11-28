import Mathlib.Tactic.Ring.Basic

/-! Relative cardinal scalar elimination and late-star mask transport. -/

namespace RKResearch.Certified.SDIRKEightEightZeroAffineFiniteMasks

variable {R : Type*} [CommRing R]

theorem affine_relative_cardinal {om k r t s q bt bs : R}
    (hs : om*bs=r*(s-q)) (ht : om*k*bt=r*(t-q)) :
    om*(k*(s-q)*bt-(t-q)*bs)=0 := by
  calc
    _ = (s-q)*(om*k*bt)-(t-q)*(om*bs) := by ring1
    _ = 0 := by rw [hs,ht]; ring1

theorem affine_arithmetic_third {h k Q k₃ s q r b₈ b₁₀ : R}
    (hp : h*k₃=-(k*Q))
    (hr : k₃*(s-q)*b₈=(r-q)*b₁₀) :
    -(k*Q)*(s-q)*b₈-h*(r-q)*b₁₀=0 := by
  calc
    _ = h*(k₃*(s-q)*b₈)-h*(r-q)*b₁₀ := by rw [← hp]; ring1
    _ = 0 := by rw [hr]; ring1

theorem affine_late_star_mask (Y w : R) :
    (Y-w)*(Y+w)*(Y-1)+(Y-w)*((1-w)*Y-(2-w)) =
    (Y-w)*(Y^2-2) := by
  ring1

end RKResearch.Certified.SDIRKEightEightZeroAffineFiniteMasks
