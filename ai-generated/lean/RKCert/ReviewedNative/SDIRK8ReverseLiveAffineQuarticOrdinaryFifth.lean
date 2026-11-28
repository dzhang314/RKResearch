module

public import Mathlib.Algebra.Polynomial.Div
import Mathlib.Tactic.LinearCombination
import Mathlib.Tactic.Ring

@[expose] public section

namespace RKCert.ReviewedNative.SDIRK8ReverseLiveAffineQuarticOrdinaryFifth

open Polynomial
open scoped Polynomial

/-- True monic ordinary pegs leave the monic quotient. This identity
commutes with specialization even when distinct roots coalesce. -/
theorem actualMissingQuotient {R : Type*} [CommRing R]
    (D E : R[X]) (r₀ r₁ : R) (hE : E.Monic)
    (hD : D=E*(C r₀+C r₁*X+X^2)) :
    D /ₘ E=C r₀+C r₁*X+X^2 := by
  rw [hD,mul_divByMonic_cancel_left _ hE]

/-- On the missing quadratic use the whole two-dimensional multiplication
determinant. It vanishes at any shared actual root, including a repeated
root and a candidate fifth equation whose degree has dropped. -/
theorem quadraticCommonRootDet {R : Type*} [CommRing R]
    (y r₀ r₁ a₀ a₁ a₂ : R)
    (hordinary : y^2+r₁*y+r₀=0) (hfifth : a₀+a₁*y+a₂*y^2=0) :
    let c₀ := a₀-a₂*r₀
    let c₁ := a₁-a₂*r₁
    c₀^2-c₀*c₁*r₁+c₁^2*r₀=0 := by
  dsimp
  let c₀ := a₀-a₂*r₀
  let c₁ := a₁-a₂*r₁
  change c₀^2-c₀*c₁*r₁+c₁^2*r₀=0
  have h : c₀+c₁*y=0 := by
    dsimp [c₀,c₁]
    linear_combination hfifth - a₂*hordinary
  calc
    c₀^2-c₀*c₁*r₁+c₁^2*r₀ =
        (c₀+c₁*y)*(c₀-c₁*y-c₁*r₁)+c₁^2*(y^2+r₁*y+r₀) := by ring
    _ = 0 := by rw [h,hordinary,zero_mul,mul_zero,add_zero]

#print axioms actualMissingQuotient
#print axioms quadraticCommonRootDet

end RKCert.ReviewedNative.SDIRK8ReverseLiveAffineQuarticOrdinaryFifth
