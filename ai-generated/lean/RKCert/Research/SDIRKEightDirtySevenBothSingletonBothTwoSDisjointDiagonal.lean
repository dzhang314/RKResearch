import Mathlib.Tactic.Ring.Basic

namespace RKResearch.Certified.SDIRKEightDirtySevenBothSingletonBothTwoSDisjointDiagonal

theorem inverse_square_clearing {K : Type*} [CommRing K]
    (L A B g : K) (hL : L=g*(A+B*g)) :
    (A+B*g)^2=A^2+B*L+A*B*g := by
  rw [hL]
  ring1

theorem two_center_fourths {K : Type*} [Field K]
    (c n f g : K) (h₁ : c*f=n) (h₂ : c*g=n) (hne : f≠g) :
    c=0 ∧ n=0 := by
  have hz : c*(f-g)=0 := by
    calc
      c*(f-g) = c*f-c*g := by ring1
      _ = 0 := by rw [h₁,h₂]; ring1
  have hc := (mul_eq_zero.mp hz).resolve_right (sub_ne_zero.mpr hne)
  exact ⟨hc, by simpa [hc] using h₁.symm⟩

end RKResearch.Certified.SDIRKEightDirtySevenBothSingletonBothTwoSDisjointDiagonal
