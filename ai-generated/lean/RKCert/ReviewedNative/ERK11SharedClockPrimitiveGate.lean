/-!
Product-level, denominator-free gates for a shared clock and a measured
Jacobi mass. The actual RK pair, support, and polynomial degree bridges
are separate.
-/
namespace RKResearch.ERK11SharedClockPrimitiveGate

open Lean.Grind

variable {R : Type} [CommRing R]

theorem singletonRankOne (d b f : R) :
    (d*b*f)*(d*b*f^3) = (d*b*f^2)^2 := by
  grind

theorem pairRankOneDefect (b₁ b₂ f₁ f₂ : R) :
    (b₁*f₁+b₂*f₂)*(b₁*f₁^3+b₂*f₂^3) -
      (b₁*f₁^2+b₂*f₂^2)^2 =
      b₁*b₂*f₁*f₂*(f₁-f₂)^2 := by
  grind

theorem endpointAndTwoClockMask (c p r t : R)
    (h : c=0 ∨ c=1 ∨ c=p ∨ c=r ∨ t=0) :
    c*(1-c)*(c-p)*(c-r)*t=0 := by
  rcases h with h | h | h | h | h <;> grind

/-- No division by an inferred primitive amplitude or Lagrange mass.
In the forward application, x is the actual clock, y its complement,
u the vector read, and n the normalized polynomial primitive. Swap x
and y for the reflected application. -/
theorem primitiveBeforeCancellation
    (x y b u mass n observed model : R)
    (hMass : mass = b*x*y*u)
    (hRead : b*y*u*observed = n*mass)
    (hModel : model = x*n) :
    (b*y*u)*(observed-model)=0 := by
  have hm : b*y*u*model=n*mass := by
    rw [hModel,hMass]
    grind
  calc
    (b*y*u)*(observed-model) =
        b*y*u*observed - b*y*u*model := by grind
    _ = n*mass - n*mass := by rw [hRead,hm]
    _ = 0 := by grind

variable {K : Type} [Field K]

theorem primitiveAtLiveMask
    (x y b u mass n observed model : K)
    (hMass : mass = b*x*y*u)
    (hRead : b*y*u*observed = n*mass)
    (hModel : model = x*n)
    (hLive : b*y*u ≠ 0) :
    observed=model := by
  have hh := primitiveBeforeCancellation x y b u mass n observed model hMass hRead hModel
  clear hMass hRead hModel
  grind

end RKResearch.ERK11SharedClockPrimitiveGate

#print axioms RKResearch.ERK11SharedClockPrimitiveGate.singletonRankOne
#print axioms RKResearch.ERK11SharedClockPrimitiveGate.pairRankOneDefect
#print axioms RKResearch.ERK11SharedClockPrimitiveGate.endpointAndTwoClockMask
#print axioms RKResearch.ERK11SharedClockPrimitiveGate.primitiveBeforeCancellation
#print axioms RKResearch.ERK11SharedClockPrimitiveGate.primitiveAtLiveMask
