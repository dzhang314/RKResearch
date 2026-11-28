import Mathlib.Tactic.Ring.Basic

namespace RKResearch.Certified.SDIRKEightDirtySevenBothSingletonSSSArithmetic

variable {K : Type*} [CommRing K]

theorem scale_paid_d_row (L C R B d g n : K)
    (hs : n = d*g) (hL : L = g*C+B*g*(g-R)) :
    d^2 * L - d*n*C = B*(n*(n-d*R)) := by
  rw [hs,hL]
  ring1

theorem paid_pair_cross (X₂ X₃ U₂ U₃ B : K)
    (h₂ : X₂ = B*U₂) (h₃ : X₃ = B*U₃) :
    X₂*U₃-X₃*U₂=0 := by
  rw [h₂,h₃]
  ring1

end RKResearch.Certified.SDIRKEightDirtySevenBothSingletonSSSArithmetic
