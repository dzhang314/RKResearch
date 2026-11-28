import Lean.Elab.Tactic.Grind

namespace RKResearch.Certified.ERK10TiltJacobiFour

/-- The integer Jacobi polynomial in homogeneous coordinates modulo eleven;
the point at infinity is also included by testing all residue pairs. -/
def evalMod11 (a b : Fin 11) : Nat :=
  (9*a.val^4+4*a.val^3*b.val+a.val^2*b.val^2+8*a.val*b.val^3+b.val^4)%11

theorem projectiveNoRoot :
    ∀ a b : Fin 11, (a ≠ 0 ∨ b ≠ 0) → evalMod11 a b ≠ 0 := by decide

/-- 2520 times the moment of X^(k+1)(1-X). -/
def moment (k : Nat) : Int := (2520/((k+2:Nat):Int))-(2520/((k+3:Nat):Int))

theorem fourMoments :
    ∀ k : Fin 4,
    moment k.val-14*moment (k.val+1)+56*moment (k.val+2)
     -84*moment (k.val+3)+42*moment (k.val+4)=0 := by decide

end RKResearch.Certified.ERK10TiltJacobiFour
#print axioms RKResearch.Certified.ERK10TiltJacobiFour.projectiveNoRoot
#print axioms RKResearch.Certified.ERK10TiltJacobiFour.fourMoments
