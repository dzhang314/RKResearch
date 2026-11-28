import Mathlib.Tactic.Ring.Basic

/-! Scalar clearing identities for the five-doubled-row boundary projection. -/
namespace RKResearch.Certified.SDIRKEightDirtySevenQuadraticFiveDPrefix

variable {R : Type*} [CommRing R]

theorem cleared_singleton_trace (lam nu beta c a p : R) :
    lam*nu*a+c-nu*beta*p =
      nu*(lam*a-beta*p)+c := by
  ring1

theorem affine_singleton_product (nu W T beta lam a : R) :
    nu*W*(lam*a-beta*T+lam*beta*nu*W) =
      lam*nu*W*(a+beta*nu*W)-beta*nu*W*T := by
  ring1

end RKResearch.Certified.SDIRKEightDirtySevenQuadraticFiveDPrefix
