import Mathlib.Tactic.Ring.Basic

/-! Gap-free scalar receipts for an affine reverse numerator at a
live reflected star, independently of any assertion of ordinary order. -/

namespace RKResearch.Certified.SDIRKEightEightZeroAffineStarMasks

variable {R : Type*} [CommRing R]

theorem pair_mask (Y w d : R) :
    (d-w)*((Y-1)*(Y-d))-(-d-w)*((Y-1)*(Y+d)) =
      2*d*(Y-1)*(Y+w) := by
  ring1

theorem terminal_mask (d w m₀ m₁ m₂ : R) :
    m₂-d^2*m₀-(2-d^2)*(1-w)*(m₁-m₀) =
      (m₂+(w-1)*m₁-w*m₀)+(d^2-1)*((1-w)*m₁-(2-w)*m₀) := by
  ring1

theorem divided_mean_numerator (p p₀ Y w d : R) :
    p*(Y^2-d^2)-p₀*(w^2-d^2) =
      (w^2-d^2)*(p-p₀)+(Y-w)*(p*(Y+w)) := by
  ring1

end RKResearch.Certified.SDIRKEightEightZeroAffineStarMasks
