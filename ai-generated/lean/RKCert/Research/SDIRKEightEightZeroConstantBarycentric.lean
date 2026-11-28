import Mathlib.Tactic.Ring.Basic

/-! Paid scalar identities for the constant reverse-numerator chart. -/

namespace RKResearch.Certified.SDIRKEightEightZeroConstantBarycentric

variable {R : Type*} [CommRing R]

/-- The normalized third moment of the third shifted Legendre mode,
with all ordinary denominators cleared. -/
theorem cleared_legendre_third {D i₃ i₄ i₅ i₆ : R}
    (h₃ : 4*i₃=D^3) (h₄ : 5*i₄=D^4)
    (h₅ : 6*i₅=D^5) (h₆ : 7*i₆=D^6) :
    140*(20*i₆-30*D*i₅+12*D^2*i₄-D^3*i₃)=D^6 := by
  apply sub_eq_zero.mp
  calc
    _ = 400*(7*i₆-D^6)-700*D*(6*i₅-D^5)
        +336*D^2*(5*i₄-D^4)-35*D^3*(4*i₃-D^3) := by ring1
    _ = 0 := by rw [h₆,h₅,h₄,h₃]; ring1

/-- The exact third-site shape relation factors the rank-exception
projection without dividing by the third Legendre residual. -/
theorem shape_rank_factor {p q g h lam : R} (hh : h+lam*g=0) :
    p*g-q*h=g*(p+lam*q) := by
  apply sub_eq_zero.mp
  calc
    _ = -q*(h+lam*g) := by ring1
    _ = 0 := by rw [hh,mul_zero]

end RKResearch.Certified.SDIRKEightEightZeroConstantBarycentric
