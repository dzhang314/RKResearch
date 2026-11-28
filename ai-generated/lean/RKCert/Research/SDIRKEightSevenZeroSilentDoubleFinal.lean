import Mathlib.Tactic.Ring.Basic

/-!
Gap-free reflected star moments and a division-free quadratic-root
projection. No rooted tableau or coefficient-field lift is claimed here.
-/

namespace RKResearch.Certified.SDIRKEightSevenZeroSilentDoubleFinal

variable {R : Type*} [CommRing R]

theorem star_collision_factor (v : R) :
    1-(v-1)^2 = v*(2-v) := by ring1

/-- The literal cardinal ratio loses its gap parameter after the two
ordinary masked equations. The remaining factor is a collision guard. -/
theorem star_gap_free_moments [IsDomain R]
    {δ h₀ h₁ h₂ h₃ : R} (hs : 1-δ^2≠0) (h₁₀ : h₁=h₀)
    (hOrd : h₃-h₂-δ^2*(h₁-h₀)=0)
    (hCar : (2-δ^2)*(h₂-(1+δ)*h₁+δ*h₀)=h₂-δ^2*h₀) :
    h₃=h₂ ∧ h₂=2*h₀ := by
  have he : h₃-h₂=0 := by simpa only [h₁₀,sub_self,mul_zero,sub_zero] using hOrd
  have hf : (1-δ^2)*(h₂-2*h₀)=0 := by
    calc
      _ = (2-δ^2)*(h₂-(1+δ)*h₁+δ*h₀)-(h₂-δ^2*h₀) := by rw [h₁₀]; ring1
      _ = _ := sub_eq_zero.mpr hCar
  exact ⟨sub_eq_zero.mp he, sub_eq_zero.mp ((mul_eq_zero.mp hf).resolve_left hs)⟩

/-- A common root of the cleared quadratics kills their degree-two
resultant, even if one leading coefficient (including the ordinary
Cramer pivot) vanishes. -/
theorem common_quadratic_root_projection
    {A B C d e f r : R} (hQ : A*r^2+B*r+C=0) (hF : d*r^2+e*r+f=0) :
    (A*f-C*d)^2-(A*e-B*d)*(B*f-C*e)=0 := by
  have hL : A*f-C*d = -(A*e-B*d)*r := by
    calc
      _ = -(A*e-B*d)*r+A*(d*r^2+e*r+f)-d*(A*r^2+B*r+C) := by ring1
      _ = _ := by rw [hF,hQ]; ring1
  have hR : B*f-C*e = (A*e-B*d)*r^2 := by
    calc
      _ = (A*e-B*d)*r^2+B*(d*r^2+e*r+f)-e*(A*r^2+B*r+C) := by ring1
      _ = _ := by rw [hF,hQ]; ring1
  rw [hL,hR]
  ring1

end RKResearch.Certified.SDIRKEightSevenZeroSilentDoubleFinal
