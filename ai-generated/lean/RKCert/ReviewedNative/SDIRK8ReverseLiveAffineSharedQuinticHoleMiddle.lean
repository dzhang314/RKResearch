module

public import Mathlib.Algebra.Polynomial.Derivative
public import Mathlib.LinearAlgebra.Matrix.Adjugate
import Mathlib.Algebra.BigOperators.Fin
import Mathlib.Tactic.LinearCombination
import Mathlib.Tactic.Ring

@[expose] public section

namespace RKCert.ReviewedNative.SDIRK8ReverseLiveAffineSharedQuinticHoleMiddle

open scoped Matrix BigOperators Polynomial
open Polynomial

/-- The evaluation-at-hole divided-difference column for a nodal factor
with an additional factor X-r is itself a multiple of the hole value. -/
theorem massCorrectionColumn {R : Type*} [CommRing R]
    (x r h hᵣ E WH F beta : R)
    (h₀ : (x-r)*WH=h-hᵣ) :
    hᵣ*F-beta*(h*E-(x-r)*E*WH)=hᵣ*(F-beta*E) := by
  linear_combination beta*E*h₀

/-- After subtracting r times the previous column, both higher signed
columns contain the same true homogeneous hole-value factor. -/
theorem doubleSignedColumnFactor {R : Type*} [CommRing R]
    (a₀ a₁ a₂ b₀ b₁ b₂ c₀ c₁ c₂ r h : R) :
    (Matrix.det !![a₀,r*a₀+h*b₀,r*(r*a₀+h*b₀)+h*c₀;
      a₁,r*a₁+h*b₁,r*(r*a₁+h*b₁)+h*c₁;
      a₂,r*a₂+h*b₂,r*(r*a₂+h*b₂)+h*c₂]) =
      h^2*(Matrix.det !![a₀,b₀,c₀; a₁,b₁,c₁; a₂,b₂,c₂]) := by
  simp [Matrix.det_fin_three]
  ring

/-- The monic missing quadratic gives a unit coordinate in every true
three-column coefficient minor. No entry or rank pivot is assumed. -/
theorem signedCoefficientMinorZero {R : Type*} [CommRing R]
    (M : Matrix (Fin 3) (Fin 3) R) (r₀ r₁ : R)
    (h : ∀ i, M i 0*r₀+M i 1*r₁+M i 2=0) : M.det=0 := by
  let v : Fin 3 → R := ![r₀,r₁,1]
  apply Matrix.det_eq_zero_of_mulVec_eq_zero_of_mem_nonZeroDivisors
    (v := v) (i := 2)
  · funext i
    change (∑ j, M i j*v j)=0
    simpa [Fin.sum_univ_succ,v,add_assoc] using h i
  · simp [v]

/-- At an actual known ordinary peg the derivative comes only from
its nodal factor, including when some other formal peg coalesces. -/
theorem derivativeAtPeg {R : Type*} [CommRing R] (E Q : R[X])
    (c : R) (hc : E.eval c=0) :
    (derivative (E*Q)).eval c=(derivative E).eval c*Q.eval c := by
  rw [derivative_mul,eval_add,eval_mul,eval_mul,hc,zero_mul,add_zero]

/-- Equal true ordinary weights turn the constant deflated nodewise
read into a denominator-free row in the missing cofactor. -/
theorem terminalWeightCoefficientRow {R : Type*} [CommRing R] [NoZeroDivisors R]
    (Hc Hx Dc Dx Ec Ex Rc Rx b lam : R)
    (hb : b≠0) (hc : Hc*Dc*b=lam) (hx : Hx*Dx*b=lam)
    (hc' : Dc=Ec*Rc) (hx' : Dx=Ex*Rx) :
    Hc*Ec*Rc-Hx*Ex*Rx=0 := by
  have hz : (Hc*Dc-Hx*Dx)*b=0 := by linear_combination hc-hx
  have hs := (mul_eq_zero.mp hz).resolve_right hb
  rw [hc',hx'] at hs
  linear_combination hs

#print axioms massCorrectionColumn
#print axioms doubleSignedColumnFactor
#print axioms signedCoefficientMinorZero
#print axioms derivativeAtPeg
#print axioms terminalWeightCoefficientRow

end RKCert.ReviewedNative.SDIRK8ReverseLiveAffineSharedQuinticHoleMiddle
