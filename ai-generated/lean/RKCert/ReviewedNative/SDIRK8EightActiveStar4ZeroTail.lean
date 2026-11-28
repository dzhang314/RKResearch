module

public import Mathlib.Algebra.Field.Basic
import Mathlib.Tactic.LinearCombination
import Mathlib.Tactic.Ring
import Mathlib.Tactic.NormNum

@[expose] public section

namespace RKCert.ReviewedNative.SDIRK8EightActiveStar4ZeroTail

/-- The highest centered coefficient, with its true nonzero diagonal
factor canceled, gives the affine relation of the Legendre coefficients. -/
theorem topCenteredCollapse {R : Type*} [Field R]
    (g b c : R) (hg : g≠0) (h14 : (14:R)≠0)
    (h : 70*g^4*b-126*g^4*(18*g-5)*c=0) :
    5*b=(162*g-45)*c := by
  have hz : (14*g^4)*(5*b-(162*g-45)*c)=0 := by
    linear_combination h
  exact sub_eq_zero.mp ((mul_eq_zero.mp hz).resolve_left (mul_ne_zero h14 (pow_ne_zero _ hg)))

/-- A centered top relation and its next independent relation
give the homogeneous Legendre coefficient vector without division. -/
theorem middleCenteredCollapse {R : Type*} [CommRing R]
    (d q p a c : R) (h : 5*q*a+8*p*c=0) (hd : d=5*q) :
    d*a=-8*p*c := by
  rw [hd]
  linear_combination h

#print axioms topCenteredCollapse
#print axioms middleCenteredCollapse

end RKCert.ReviewedNative.SDIRK8EightActiveStar4ZeroTail
