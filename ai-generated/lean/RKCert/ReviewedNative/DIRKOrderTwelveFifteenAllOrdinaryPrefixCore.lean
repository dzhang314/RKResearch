import Lean.Elab.Tactic.Omega

/-! The literal two-row algebra in denominator-cleared coordinates.
The genuine stage-space, pure-mode rank and finite projection are documented separately. -/
namespace RKResearch.Certified.Graded.OrderTwelveFifteen.AllOrdinaryPrefixCore

/-- Replace generic two modal rows by two genuine cardinal rows. -/
theorem cardinalRowEliminate (J U V R ρ I Fx : Int) (hU : U = R-ρ*V) :
    J-U*I-V*Fx = J-R*I-V*(Fx-ρ*I) := by
  rw [hU, Int.sub_mul, Int.mul_sub]
  have h : (ρ*V)*I = V*(ρ*I) := by
    rw [Int.mul_comm ρ V, Int.mul_assoc]
  rw [h]
  omega

/-- When the other real mode is nonzero at the first row, its coefficient
is removed by the two actual ordinary scalar reads. -/
theorem trueMomentEliminate (r1 rx k1 kx ρ M K I Fx : Int)
    (hρ : kx = ρ*k1) (h1 : r1*M+k1*K = I) (hx : rx*M+kx*K = Fx) :
    (rx-ρ*r1)*M = Fx-ρ*I := by
  rw [← h1, ← hx, hρ, Int.sub_mul, Int.mul_add]
  simp only [Int.mul_assoc]
  omega

#print axioms cardinalRowEliminate
#print axioms trueMomentEliminate
end RKResearch.Certified.Graded.OrderTwelveFifteen.AllOrdinaryPrefixCore
