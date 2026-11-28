module

public import Mathlib.Algebra.Ring.Basic
import Mathlib.Tactic.Ring
import Mathlib.Tactic.LinearCombination

@[expose] public section

/-! Denominator-cleared scalar transfers for the midpoint DIRK12 support.
These are polynomial identities, not assertions that a selected real
algebraic point satisfies the two input moment relations. -/
namespace RKResearch.Certified.DIRK12MidpointMomentTransfers

variable {K : Type*} [CommRing K]

def A (u w : K) : K := 9*w-4*u
def B (u w : K) : K := 3*w-u
def C (u w : K) : K := 3*w-2*u

def k0 (_u _w e : K) : K := -3*e^3
def k1 (u w e : K) : K := 3*e^2*(C u w+2*B u w)
def k2 (u w e : K) : K := -e*(6*B u w*C u w+A u w*B u w)
def k3 (u w _e : K) : K := A u w*B u w*C u w
def cubic (a b c y : K) : K :=
  let u := a*c
  let w := b*b
  let e := b*c
  k0 u w e + k1 u w e*y + k2 u w e*y^2 + k3 u w e*y^3

def j60 (a b c y : K) : K :=
  let u := a*c
  let w := b*b
  let e := b*c
  30*k0 u w e*y + 20*k1 u w e*y^2 + 15*k2 u w e*y^3 + 12*k3 u w e*y^4

def mk (a b c y : K) : K :=
  let u := a*c
  let w := b*b
  let e := b*c
  (k3 u w e*c + k2 u w e*b + k1 u w e*a) +
    (k3 u w e*b + k2 u w e*a)*y + k3 u w e*a*y^2

def affine60 (a b c y : K) : K :=
  let u := a*c
  let w := b*b
  9*b^4*c^5*(u-w)*(16*u-9*w) - 72*a*b^3*c^5*(u-w)*C u w*y

def quotient60 (a b c y : K) : K :=
  let u := a*c
  let w := b*b
  3*b*c^2*(u-w)*(16*u-9*w) +
  3*c*(32*u^3-56*u^2*w-87*u*w^2+81*w^3)*y +
  3*b*(u-3*w)*(7*u-12*w)*(16*u-9*w)*y^2 +
  12*a*(u-3*w)*(2*u-3*w)*(4*u-9*w)*y^3

/-- Compensated reverse quartic scalar calculation in denominator-free form. -/
theorem reverse_quartic (a b c y : K) :
    -mk a b c y*j60 a b c y-affine60 a b c y =
      quotient60 a b c y*cubic a b c y := by
  unfold mk j60 affine60 quotient60 cubic k0 k1 k2 k3 A B C
  ring

theorem affine_at_root {a b c y : K} (h : cubic a b c y=0) :
    -mk a b c y*j60 a b c y = affine60 a b c y := by
  have h' := reverse_quartic a b c y
  rw [h,mul_zero,sub_eq_zero] at h'
  exact h'

def rel3 (a b c d : K) : K := B (a*c) (b*b)*d-2*(b*c)*c
def rel4 (a b c d e : K) : K := A (a*c) (b*b)*e-5*(b*c)*d

/-- First vanishing nodal moment, after multiplying by the moving denominator. -/
theorem paid_hull0 (a b c d : K) :
    k3 (a*c) (b*b) (b*c)*d + k2 (a*c) (b*b) (b*c)*c +
      k1 (a*c) (b*b) (b*c)*b + k0 (a*c) (b*b) (b*c)*a =
      A (a*c) (b*b)*C (a*c) (b*b)*rel3 a b c d := by
  unfold k0 k1 k2 k3 rel3 A B C
  ring

/-- Second vanishing nodal moment, after multiplying by the moving denominator. -/
theorem paid_hull1 (a b c d e : K) :
    k3 (a*c) (b*b) (b*c)*e + k2 (a*c) (b*b) (b*c)*d +
      k1 (a*c) (b*b) (b*c)*c + k0 (a*c) (b*b) (b*c)*b =
      B (a*c) (b*b)*C (a*c) (b*b)*rel4 a b c d e +
      6*(b*c)*(a*c-2*b*b)*rel3 a b c d := by
  unfold k0 k1 k2 k3 rel3 rel4 A B C
  ring

/-- The one cancellation needed to turn the published higher relation
into the linear grade-four one. -/
theorem paid_relation4 {a b c d e : K} (h3 : rel3 a b c d=0)
    (h4 : 2*A (a*c) (b*b)*c*e-5*B (a*c) (b*b)*d^2=0) :
    (2*c)*rel4 a b c d e=0 := by
  unfold rel3 at h3
  unfold rel4
  linear_combination h4+5*d*h3


/-- All four paid scalar primitive tests are explicit consequences of
the same two moment relations; the first two require neither. -/
theorem paid_pair0 (a b c : K) :
    2*((b*c)*a-C (a*c) (b*b)*b)-6*(a*c-b*b)*b=0 := by
  unfold C
  ring

theorem paid_pair1 (a b c : K) :
    3*((b*c)*b-C (a*c) (b*b)*c)-6*(a*c-b*b)*c=0 := by
  unfold C
  ring

theorem paid_pair2 (a b c d : K) :
    4*((b*c)*c-C (a*c) (b*b)*d)-6*(a*c-b*b)*d = -2*rel3 a b c d := by
  unfold C rel3 B
  ring

theorem paid_pair3 (a b c d e : K) :
    5*((b*c)*d-C (a*c) (b*b)*e)-6*(a*c-b*b)*e = -rel4 a b c d e := by
  unfold C rel4 A
  ring


end RKResearch.Certified.DIRK12MidpointMomentTransfers

#print axioms RKResearch.Certified.DIRK12MidpointMomentTransfers.reverse_quartic
#print axioms RKResearch.Certified.DIRK12MidpointMomentTransfers.paid_hull1
