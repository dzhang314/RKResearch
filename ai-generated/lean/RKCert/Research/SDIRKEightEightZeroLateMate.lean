import Mathlib.Tactic.Ring.Basic

/-! The late-mate scaled Legendre determinant, independently of any
Legendre evaluation pivot or coefficient field. -/

namespace RKResearch.Certified.SDIRKEightEightZeroLateMate

variable {R : Type*} [CommRing R]

def det3 (a b c d e f g h i : R) : R :=
  a*(e*i-f*h)-b*(d*i-f*g)+c*(d*h-e*g)

/-- An affine-coefficient representation of the third moment column
annuls the three-by-three determinant, without any division. -/
theorem three_moment_determinant {m₀ m₁ m₂ m₃ n₀ n₁ n₂ p q : R}
    (h₀ : n₀=p*m₀+q*m₁) (h₁ : n₁=p*m₁+q*m₂)
    (h₂ : n₂=p*m₂+q*m₃) :
    det3 m₀ m₁ n₀ m₁ m₂ n₁ m₂ m₃ n₂=0 := by
  unfold det3
  rw [h₀,h₁,h₂]
  ring1

end RKResearch.Certified.SDIRKEightEightZeroLateMate
