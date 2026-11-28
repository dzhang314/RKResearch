/-! Portable scalar algebra for the nonaliased dormant center. -/
namespace RKResearch.ERK11NonaliasedCenterQuadraticGate
open Lean.Grind

theorem bilinearElimination {R : Type} [CommRing R]
    (a₀ a₁ a₂ a₃ c₀ c₁ c₂ c₃ u v : R)
    (ha : a₀+a₁*u+(a₂+a₃*u)*v=0)
    (hc : c₀+c₁*u+(c₂+c₃*u)*v=0) :
    (a₀*c₂-c₀*a₂)+(a₀*c₃+a₁*c₂-c₀*a₃-c₁*a₂)*u+
      (a₁*c₃-c₁*a₃)*u^2 = 0 := by
  have ha' : a₀+a₁*u = -(a₂+a₃*u)*v := by grind
  have hc' : c₀+c₁*u = -(c₂+c₃*u)*v := by grind
  calc
    (a₀*c₂-c₀*a₂)+(a₀*c₃+a₁*c₂-c₀*a₃-c₁*a₂)*u+
        (a₁*c₃-c₁*a₃)*u^2 =
      (a₀+a₁*u)*(c₂+c₃*u)-(c₀+c₁*u)*(a₂+a₃*u) := by grind
    _ = 0 := by rw [ha', hc']; grind

theorem centeredConstant {R : Type} [CommRing R]
    (H C₁ C₂ I₀ I₁ I₂ s : R) :
    H^2*(I₂-2*s*I₁+s^2*I₀)-
      H*(I₁-s*I₀)*((C₁-H*s)+(C₂-H*s))+
      I₀*(C₁-H*s)*(C₂-H*s) =
    H^2*I₂-H*(C₁+C₂)*I₁+I₀*C₁*C₂ := by
  grind

theorem centroidPole {K : Type} [Field K]
    (u p delta x s : K) (hu : u≠0)
    (h : p*(x-s)= -u*delta) :
    (p=0 → delta=0) ∧ (delta=0 → x≠s → p=0) := by
  constructor
  · intro hp
    rw [hp] at h
    grind
  · intro hd hs
    rw [hd] at h
    grind

theorem centeredPoolMass {R : Type} [CommRing R] (u v b A B J q m : R)
    (hJ : J=b*A*B*u*v) (hm : m=b*A*B*q) :
    u*v*m=J*q := by
  rw [hm, hJ]
  grind

end RKResearch.ERK11NonaliasedCenterQuadraticGate
#print axioms RKResearch.ERK11NonaliasedCenterQuadraticGate.bilinearElimination
#print axioms RKResearch.ERK11NonaliasedCenterQuadraticGate.centeredConstant
#print axioms RKResearch.ERK11NonaliasedCenterQuadraticGate.centroidPole
#print axioms RKResearch.ERK11NonaliasedCenterQuadraticGate.centeredPoolMass
