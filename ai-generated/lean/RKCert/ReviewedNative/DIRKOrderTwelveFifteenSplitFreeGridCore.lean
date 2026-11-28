import Lean.Elab.Tactic.Omega

/-! Arithmetic guard for the monic split-free reverse quadratic.
The exact real moment and physical split arguments are documented separately. -/
namespace RKResearch.Certified.Graded.OrderTwelveFifteen.SplitFreeGridCore

/-- Q is four times the zeroth--second moment product; N is nine times
the square of the first anchor moment. The true reverse clock r is nonzero,
so a candidate component cannot lose the quadratic leading coefficient. -/
theorem orientationLeadingNonzero (Q N r : Int) (hn : N ≠ 0) (hr : r ≠ 0)
    (h : (Q-N)*(r*r)+(-Q+2*N)*r+(Q-N)=0) : Q-N ≠ 0 := by
  intro h0
  have h1 : Q=N := by omega
  rw [h1] at h
  have hp : N*r=0 := by
    have hh : -N+2*N=N := by omega
    rw [hh] at h
    simp at h
    exact h
  rcases Int.mul_eq_zero.mp hp with hN | hR
  · exact hn hN
  · exact hr hR

/-- The slope-zero polynomial in the affine variable cannot occur on
an actual nonzero reverse-clock component. -/
theorem orientationLeadAtEqual (N r : Int) (hn : N ≠ 0) (hr : r ≠ 0) :
    (N-N)*(r*r)+(-N+2*N)*r+(N-N) ≠ 0 := by
  intro h
  have hn' := orientationLeadingNonzero N N r hn hr h
  exact hn' (Int.sub_self N)

#print axioms orientationLeadingNonzero
#print axioms orientationLeadAtEqual
end RKResearch.Certified.Graded.OrderTwelveFifteen.SplitFreeGridCore
