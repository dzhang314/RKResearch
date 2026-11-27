import Lean

/-! Scalar contact exclusions for the two-half Lobatto branch. -/
namespace RKResearch.ERK10BalancedHalfGate
open Lean.Grind
variable {K : Type} [Field K]

def J4 (u : K) : K := 21*u^4-14*u^2+1

theorem J4AtThird (u : K) (h : 3*u=1) : 81*J4 u = -24 := by
  have hi : 81*J4 u=21*(3*u)^4-126*(3*u)^2+81 := by unfold J4; grind
  rw [h] at hi
  grind

theorem J4AtHalf (u : K) (h : 2*u=1) : 16*J4 u = -19 := by
  have hi : 16*J4 u=21*(2*u)^4-56*(2*u)^2+16 := by unfold J4; grind
  rw [h] at hi
  grind

theorem J4AtTwoThirds (u : K) (h : 3*u=2) : 81*J4 u = -87 := by
  have hi : 81*J4 u=21*(3*u)^4-126*(3*u)^2+81 := by unfold J4; grind
  rw [h] at hi
  grind

theorem boundaryContact (u v : K)
    (hj : J4 u=0) (h : 3*v^2+(4-6*u)*v+3*u^2-6*u+2=0)
    (hv : v = -u ∨ 3*v^2+3*u^2=2)
    (nv : v+1 ≠ 0) (n2 : (2:K) ≠ 0) (n19 : (19:K) ≠ 0)
    (n24 : (24:K) ≠ 0) (n87 : (87:K) ≠ 0) : False := by
  rcases hv with hv | hv
  · rw [hv] at h
    have hc : (2:K)*((3*u-1)*(2*u-1))=0 := by grind
    rcases Field.of_mul_eq_zero ((Field.of_mul_eq_zero hc).resolve_left n2) with ha | hb
    · have hp : 3*u=1 := by grind
      have hc := J4AtThird u hp
      rw [hj] at hc
      exact n24 (by grind)
    · have hp : 2*u=1 := by grind
      have hc := J4AtHalf u hp
      rw [hj] at hc
      exact n19 (by grind)
  · have hh : (4-6*u)*(v+1)=0 := by grind
    have he := (Field.of_mul_eq_zero hh).resolve_right nv
    have hq : (2:K)*(3*u-2)=0 := by grind
    have hz := (Field.of_mul_eq_zero hq).resolve_left n2
    have hp : 3*u=2 := by grind
    have hn := J4AtTwoThirds u hp
    rw [hj] at hn
    exact n87 (by grind)

def r0 (u : K) : K := 18*u^3-9*u^2-7*u+2
def r1 (u : K) : K := -3*u^2-7*u+2
def small (u : K) : K := 483*u^3-327*u^2-43*u+27

theorem reflectedContactBezout (u : K) :
    (-3452001*u^2+1949220*u+272857)*J4 u
    +(150087*u^3+16863*u^2-87143*u-9387)*small u = 19408 := by
  unfold J4 small
  grind

set_option maxHeartbeats 2500000 in
theorem reflectedContact (u v t : K)
    (hJ : J4 u=0) (hv : 3*v^2+3*u^2=2)
    (forward : 7*u^2-4*u+1+(2-10*u)*t=0)
    (rear : 3*v^2+(2+4*u)*v+1+2*u-(4*v+2+6*u)*t=0)
    (n2 : (2:K) ≠ 0) (n4 : (4:K) ≠ 0)
    (n19408 : (19408:K) ≠ 0) : False := by
  have fr : (4:K)*(r0 u+r1 u*v)=0 := by
    unfold r0 r1
    grind
  have sr := (Field.of_mul_eq_zero fr).resolve_left n4
  have rr : r0 u= -(r1 u*v) := by grind
  have zz : r0 u ^ 2=r1 u ^ 2*v^2 := by rw [rr]; grind
  have hs : 7*(r1 u ^ 2*(2-3*u^2)-3*r0 u ^ 2)-2*small u =
      (-333*u^2+282*u-82)*J4 u := by
    unfold r0 r1 small J4
    grind
  have vv : 2-3*u^2=3*v^2 := by grind
  rw [vv,zz,hJ] at hs
  have hsp : (2:K)*small u=0 := by grind
  have hsmall := (Field.of_mul_eq_zero hsp).resolve_left n2
  have hf := reflectedContactBezout u
  rw [hJ,hsmall] at hf
  exact n19408 (by grind)

theorem twoPrimitiveConflict (u w : K) (n3 : (3:K) ≠ 0) (nu : u ≠ 0)
    (h : 2*w=u) (hr : 2*u=w) : False := by
  have hn : (3:K)*u=0 := by grind
  exact nu ((Field.of_mul_eq_zero hn).resolve_left n3)

end RKResearch.ERK10BalancedHalfGate
#print axioms RKResearch.ERK10BalancedHalfGate.J4AtThird
#print axioms RKResearch.ERK10BalancedHalfGate.J4AtHalf
#print axioms RKResearch.ERK10BalancedHalfGate.J4AtTwoThirds
#print axioms RKResearch.ERK10BalancedHalfGate.boundaryContact
#print axioms RKResearch.ERK10BalancedHalfGate.reflectedContactBezout
#print axioms RKResearch.ERK10BalancedHalfGate.reflectedContact
#print axioms RKResearch.ERK10BalancedHalfGate.twoPrimitiveConflict
