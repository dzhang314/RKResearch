import Mathlib.Tactic.Ring

/-! Scalar components of the graph four-off-site contradiction. -/
namespace RKResearch.Certified.SDIRKEightFiveZeroGraphDistinctOff

theorem equal_graph_residual_opposite_pair {R : Type*} [CommRing R] [IsDomain R]
    {a b g : R} (hg : g≠0) (h : a*g+b*g=0) : a+b=0 := by
  have hf : (a+b)*g=0 := by rw [add_mul,h]
  exact (mul_eq_zero.mp hf).resolve_right hg

theorem localized_pure_terminal_zero {R : Type*} [CommRing R]
    {a b z : R} (hab : a+b=0) (h : a+b+z=0) : z=0 := by
  simpa [hab] using h

theorem proportional_off_multiplier_when_clocks_equal {R : Type*} [CommRing R]
    {v w x y t k : R} (hxy : x=y) (h₁ : k*v=(t-x)*w) :
    k*v=(t-y)*w := by simpa [hxy] using h₁

end RKResearch.Certified.SDIRKEightFiveZeroGraphDistinctOff
