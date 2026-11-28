/-! The scalar coefficient gate on the shared ERK11 fixed-moment curves. -/
namespace RKResearch.ERK11NeighborSharedFixedArithmetic
open Lean.Grind

/-- The left and right seventh-row slopes of Y(Y-w)r give matching endpoint
    values for the sparse column B1.  Both identities are denominator-free. -/
theorem sparseEndpointValues {R : Type} [CommRing R]
    (w h r0 rw l0 l1 : R) (hh : w = 2*h)
    (h0 : l0 = -w*r0) (h1 : l1 = w*rw) :
    2*((-h)*(w*l0)) = w^3*r0 ∧
      2*((w-h)*(w*l0-(l0-l1)*w)) = w^3*rw := by
  subst w
  subst l0
  subst l1
  constructor <;> grind

/-- A projective read on the kernel span of r and Yr.  Here C is T/t,
    lambda0+lambda1*Y is the second-pool quotient by r, and g is affine.
    No field or live divisors are used in this cleared version. -/
theorem affineFirstPool {R : Type} [CommRing R]
    (h lambda0 lambda1 g0 g1 A U W C Y : R)
    (hA : h*A = -(lambda0*g0))
    (hU : h*U = -((lambda0+lambda1*h)*(g0+g1*h)))
    (hW : W = lambda1*g1)
    (hC : lambda0*C = lambda1*A) :
    (h*lambda0)*(U+(C-W)*(Y-h)) =
      -(lambda0*(g0+g1*h))*(lambda0+lambda1*Y) := by
  have hl : (h*lambda0)*(C-W) = -(lambda0*lambda1*(g0+g1*h)) := calc
    (h*lambda0)*(C-W) = h*(lambda0*C) - h*lambda0*W := by grind
    _ = h*(lambda1*A) - h*lambda0*(lambda1*g1) := by rw [hC, hW]
    _ = lambda1*(h*A) - h*lambda0*(lambda1*g1) := by grind
    _ = -(lambda0*lambda1*(g0+g1*h)) := by rw [hA]; grind
  calc
    (h*lambda0)*(U+(C-W)*(Y-h)) =
        lambda0*(h*U) + ((h*lambda0)*(C-W))*(Y-h) := by grind
    _ = -(lambda0*(g0+g1*h))*(lambda0+lambda1*Y) := by
      rw [hU, hl]
      grind

end RKResearch.ERK11NeighborSharedFixedArithmetic

#print axioms RKResearch.ERK11NeighborSharedFixedArithmetic.sparseEndpointValues
#print axioms RKResearch.ERK11NeighborSharedFixedArithmetic.affineFirstPool
