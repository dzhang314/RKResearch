import Lean.Elab.Tactic.Omega

/-! Portable denominator-cleared scalar implications for the true
nonzero-fourth-diagonal obstruction. The graded stage argument,
integration, and factor identities are independently documented. -/
namespace RKResearch.Certified.Graded.OrderTwelveFifteen.NonzeroFourthObstructionCore

/-- The numerical own-input value of the genuine commutator forces
the literal fifth diagonal to vanish. -/
theorem fifthDiagonalZero (d s : Int) (hs : s ≠ 0)
    (h : (-d*d)*s=0) : d=0 := by
  rcases Int.mul_eq_zero.mp h with hn | hn
  · rcases Int.mul_eq_zero.mp hn with hd | hd
    · omega
    · exact hd
  · exact False.elim (hs hn)

/-- Variables Q and Z represent the two scalar shape values after
clearing one common nonzero denominator U. With the exact polynomial
cross identity, the two paid factored gates force their common factor. -/
theorem commonFactorForcesCollision (Q U Z A B F : Int) (hq : Q≠0)
    (shapeA : A=9*Z-8*Q)
    (cross : 9*B-(2*Q-9*U)*A=2*Q*(8*Q-9*U))
    (atEqual : Z=U → F=U*(8*Q-9*U))
    (paidA : A*F=0) (paidB : B*F=0) : F=0 := by
  by_cases hf : F=0
  · exact hf
  · have ha : A=0 := by
      rcases Int.mul_eq_zero.mp paidA with h | h
      · exact h
      · exact False.elim (hf h)
    have hb : B=0 := by
      rcases Int.mul_eq_zero.mp paidB with h | h
      · exact h
      · exact False.elim (hf h)
    have hp : (2*Q)*(8*Q-9*U)=0 := by
      simpa [ha,hb] using cross.symm
    have hc : 8*Q-9*U=0 := by
      rcases Int.mul_eq_zero.mp hp with h | h
      · have h0 : Q=0 := by omega
        exact False.elim (hq h0)
      · exact h
    have he : Z=U := by omega
    rw [atEqual he,hc,Int.mul_zero]

#print axioms fifthDiagonalZero
#print axioms commonFactorForcesCollision
end RKResearch.Certified.Graded.OrderTwelveFifteen.NonzeroFourthObstructionCore
