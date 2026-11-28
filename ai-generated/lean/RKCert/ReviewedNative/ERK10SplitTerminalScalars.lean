namespace RKResearch.Certified.ERK10SplitTerminalScalars

/-- Homogeneous cubic in the rational probe's numerator and denominator,
with coefficients reduced modulo 8. The parameter is 2-integral. -/
def cubicMod8 (c a b : Nat) : Nat :=
  (3*c^3+4*c^2+5*c+3)*b^3 +
  (3*c^3+4*c^2+5*c+6)*a*b^2 +
  (2*c^3+4*c^2+5*c+2)*a^2*b +
  (2*c^3+5*c+6)*a^3

theorem projectiveCubicModEight :
    ∀ c a b : Fin 8, c ≠ 2 →
      (a.val % 2 = 1 ∨ b.val % 2 = 1) →
      cubicMod8 c.val a.val b.val % 8 ≠ 0 := by decide

theorem constantParameterModTwo :
    ∀ a b : Fin 2, (a ≠ 0 ∨ b ≠ 0) →
      (a.val^3 + a.val*b.val^2 + b.val^3) % 2 ≠ 0 := by decide

theorem leadingParameterModSeventeen :
    ∀ a b : Fin 17, (a ≠ 0 ∨ b ≠ 0) →
      (8*a.val^3+12*a.val^2*b.val+4*a.val*b.val^2+15*b.val^3) % 17 ≠ 0 := by decide

end RKResearch.Certified.ERK10SplitTerminalScalars

#print axioms RKResearch.Certified.ERK10SplitTerminalScalars.projectiveCubicModEight
#print axioms RKResearch.Certified.ERK10SplitTerminalScalars.constantParameterModTwo
#print axioms RKResearch.Certified.ERK10SplitTerminalScalars.leadingParameterModSeventeen
