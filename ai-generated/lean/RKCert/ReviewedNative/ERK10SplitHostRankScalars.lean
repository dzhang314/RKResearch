namespace RKResearch.Certified.ERK10SplitHostRankScalars

/-- Six projective guard polynomials for the rank-two physical exit. -/
def guardValues (a b : Fin 7) : List Nat :=
  let x:=a.val; let y:=b.val
  [x^2+3*x*y+y^2,
   5*x^3+x^2*y+4*x*y^2+6*y^3,
   x^3+3*x^2*y+6*x*y^2+2*y^3,
   x^2+4*x*y+y^2,
   5*x^2+5*y^2,
   3*x^2+3*y^2]

theorem rootlessProjective :
    ∀ a b : Fin 7, (a≠0 ∨ b≠0) →
      ((guardValues a b).map (fun z => z%7)).contains 0 = false := by decide

end RKResearch.Certified.ERK10SplitHostRankScalars
#print axioms RKResearch.Certified.ERK10SplitHostRankScalars.rootlessProjective
