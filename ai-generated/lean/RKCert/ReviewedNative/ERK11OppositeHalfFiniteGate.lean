/-! Scalar algebra of the pivot-free opposite-half atlas. The physical
grades, Lagrange quadrature, and exact rational projections are separate. -/
namespace RKResearch.ERK11OppositeHalfFiniteGate

open Lean.Grind
variable {K : Type} [CommRing K]

theorem scaledBilinear
    (δ σ π t s f00 f10 f01 f11 : K)
    (hs : δ*(t+s)=σ)
    (hp : δ*t*s=π)
    (h : f00+f10*t+f01*s+f11*t*s=0) :
    (f10-f01)*(δ*t)+(δ*f00+σ*f01+π*f11)=0 := by
  have h₁ : δ*s=σ-δ*t := by grind
  have h₂ : δ*(f00+f10*t+f01*s+f11*t*s) =
      δ*f00+f10*(δ*t)+f01*(δ*s)+f11*(δ*t*s) := by grind
  rw [h, hp, h₁] at h₂
  grind

theorem scaledQuadratic
    (δ σ π t s : K)
    (hs : δ*(t+s)=σ) (hp : δ*t*s=π) :
    (δ*t)^2-σ*(δ*t)+δ*π=0 := by
  rw [← hs, ← hp]
  grind

theorem compatibility (u v u' v' y : K)
    (h : u*y+v=0) (h' : u'*y+v'=0) :
    u*v'-u'*v=0 := by
  have h₁ : u*v'-u'*v = u*(u'*y+v')-u'*(u*y+v) := by grind
  rw [h,h'] at h₁
  grind

theorem scaledNorm
    (δ σ π u v y : K)
    (hq : y^2-σ*y+δ*π=0) (hr : u*y+v=0) :
    v^2+σ*u*v+δ*π*u^2=0 := by
  have h : v^2+σ*u*v+δ*π*u^2 =
      (u*y+v)*(u*(σ-y)+v)+u^2*(y^2-σ*y+δ*π) := by grind
  rw [hq,hr] at h
  grind

theorem crossoverAtHalf (h e gh ge jh je det : K) :
    gh*((h-h)*jh-det)*(e-h)-ge*((e-h)*je-det)*(h-h) =
      (h-e)*gh*det := by
  grind

end RKResearch.ERK11OppositeHalfFiniteGate

#print axioms RKResearch.ERK11OppositeHalfFiniteGate.scaledBilinear
#print axioms RKResearch.ERK11OppositeHalfFiniteGate.scaledQuadratic
#print axioms RKResearch.ERK11OppositeHalfFiniteGate.compatibility
#print axioms RKResearch.ERK11OppositeHalfFiniteGate.scaledNorm
#print axioms RKResearch.ERK11OppositeHalfFiniteGate.crossoverAtHalf
