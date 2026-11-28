import Mathlib.Algebra.Ring.Defs
import Mathlib.Tactic.LinearCombination
import Mathlib.Tactic.Ring

namespace RKCert.ReviewedNative.DIRKOrderElevenInvisibleSixThreeGapTorsion

variable {K : Type*} [CommRing K]

def ev2 (h0 h1 h2 x : K) := h0+h1*x+h2*x^2
def difference (a b c : K) := (a-b)*(a-c)*(b-c)

/-- Denominator-free interpolation of a quadratic. The Vandermonde
factor need not be nonzero or a unit. -/
theorem quadratic_interpolation
    (h0 h1 h2 a b c y : K) :
    difference a b c * ev2 h0 h1 h2 y =
      ev2 h0 h1 h2 a * (b-c)*(y-b)*(y-c)
      + ev2 h0 h1 h2 b * (c-a)*(y-a)*(y-c)
      + ev2 h0 h1 h2 c * (a-b)*(y-a)*(y-b) := by
  unfold difference ev2
  ring

/-- Multiply by the product of the three physical ghost heads. This is
valid even when an individual head is a zero divisor. -/
theorem weighted_vandermonde {h0 h1 h2 a b c ga gb gc : K}
    (ha : ga*ev2 h0 h1 h2 a=0)
    (hb : gb*ev2 h0 h1 h2 b=0)
    (hc : gc*ev2 h0 h1 h2 c=0) (y : K) :
    (ga*gb*gc)*difference a b c*ev2 h0 h1 h2 y=0 := by
  have h := quadratic_interpolation h0 h1 h2 a b c y
  linear_combination (ga*gb*gc)*h
    + (gb*gc*(b-c)*(y-b)*(y-c))*ha
    + (ga*gc*(c-a)*(y-a)*(y-c))*hb
    + (ga*gb*(a-b)*(y-a)*(y-b))*hc

/-- Nodal values of twelve times the first primitive and sixty times
the second primitive, respectively. -/
def I12 (u v : K) := u^3*(2*v-u)
def IX60 (u v : K) := u^4*(5*v-3*u)

theorem nodal_torsion_determinant (u v : K) :
    IX60 v u * I12 u v - IX60 u v * I12 v u = 6*u^3*v^3*(u-v)^3 := by
  unfold IX60 I12
  ring

/-- True cleared prefix transfer for three physical ghosts. No
regularity or invertibility of the factors is assumed. -/
theorem three_ghosts_torsion
    {P Q : K → K}
    {u v a b c ga gb gc bu bv hu hv k p0 p1 p2 : K}
    (hp : ∀ t, Q t-k*P t=ev2 p0 p1 p2 t)
    (ha : ga*(Q a-k*P a)=0)
    (hb : gb*(Q b-k*P b)=0)
    (hc : gc*(Q c-k*P c)=0)
    (hpu : hu*P u = bu*I12 u v)
    (hpv : hv*P v = bv*I12 v u)
    (hqu : hu*Q u = bu*IX60 u v)
    (hqv : hv*Q v = bv*IX60 v u) :
    (ga*gb*gc)*difference a b c*bu*bv*(6*u^3*v^3*(u-v)^3)=0 := by
  let D : K := (ga*gb*gc)*difference a b c
  have ha' := ha
  have hb' := hb
  have hc' := hc
  rw [hp] at ha' hb' hc'
  have each (x : K) : D*(Q x-k*P x)=0 := by
    rw [hp]
    exact weighted_vandermonde ha' hb' hc' x
  have s (x ht bb I QI : K)
      (hP : ht*P x=bb*I) (hQ : ht*Q x=bb*QI) :
      D*bb*(QI-k*I)=0 := by
    have hx := each x
    linear_combination ht*hx + D*k*hP - D*hQ
  have eU := s u hu bu (I12 u v) (IX60 u v) hpu hqu
  have eV := s v hv bv (I12 v u) (IX60 v u) hpv hqv
  change D*bu*bv*(6*u^3*v^3*(u-v)^3)=0
  rw [← nodal_torsion_determinant]
  linear_combination bu*I12 u v*eV - bv*I12 v u*eU

/-- With at most two initial physical forward ghosts, retain both
cubic factors in the cleared contradiction. It is not necessary to
assume there is a second real donor when a tap is zero. -/
theorem first_forward_two_ghost_torsion {x p q l r d g h : K}
    (m0 : l*g+r*h=0) (m1 : l*p*g+r*q*h=0)
    (h1 : 2*(l*p+r*q+d*x)=x^2)
    (h2 : 3*(l*p^2+r*q^2+d*x^2)=x^3) :
    (p-q)*g*h*x^3=0 := by
  let D := (p-q)*g*h
  have el : D*l=0 := by
    dsimp [D]
    linear_combination h*(m1-q*m0)
  have er : D*r=0 := by
    dsimp [D]
    linear_combination g*(p*m0-m1)
  change D*x^3=0
  linear_combination 2*D*h2 - 3*D*x*h1
    - 6*(p^2-x*p)*el - 6*(q^2-x*q)*er

/-- One real donor does not need an auxiliary clock. -/
theorem first_forward_one_ghost_torsion {x p l d g : K}
    (m : l*g=0)
    (h1 : 2*(l*p+d*x)=x^2) (h2 : 3*(l*p^2+d*x^2)=x^3) :
    g*x^3=0 := by
  linear_combination 2*g*h2-3*g*x*h1-6*(p^2-x*p)*m

theorem first_forward_no_ghost_torsion {x d : K}
    (h1 : 2*(d*x)=x^2) (h2 : 3*(d*x^2)=x^3) :
    x^3=0 := by
  linear_combination 2*h2-3*x*h1

end RKCert.ReviewedNative.DIRKOrderElevenInvisibleSixThreeGapTorsion

open RKCert.ReviewedNative.DIRKOrderElevenInvisibleSixThreeGapTorsion
#print axioms quadratic_interpolation
#print axioms weighted_vandermonde
#print axioms nodal_torsion_determinant
#print axioms three_ghosts_torsion
#print axioms first_forward_two_ghost_torsion
#print axioms first_forward_one_ghost_torsion
#print axioms first_forward_no_ghost_torsion
