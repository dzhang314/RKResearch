module

public import Mathlib.Algebra.Field.Basic
import Mathlib.Tactic.LinearCombination
import Mathlib.Tactic.Ring

@[expose] public section

namespace RKCert.ReviewedNative.SDIRK8TailPinnedAffine

/-- The actual terminal and ninth clock comparison determines the affine
profile up to scale, with an exact divided difference replacing the
zero-gap padded factor. -/
theorem tailPinsAffine {K : Type*} [Field K]
    (X C U A B F q₀ q₁ Y : K)
    (hU : X-C=U) (hF : A-B=U*F) (hne : U ≠ 0)
    (h : A*(q₀+q₁*X)=B*(q₀+q₁*C)) :
    B*(q₀+q₁*Y)=(q₀+q₁*X)*(B-F*(Y-X)) := by
  have h0 : U*(B*q₁+F*(q₀+q₁*X))=0 := by
    linear_combination h - (B*q₁)*hU - (q₀+q₁*X)*hF
  have h1 := (mul_eq_zero.mp h0).resolve_left hne
  linear_combination (Y-X)*h1

/-- In the two-silent literal/eighth chart the common physical clock
equation gives the reciprocal diagonal without using either silent defect. -/
theorem silentEighthPinsReciprocal {R : Type*} [CommRing R]
    (γ b k u : R)
    (hs : 2*(1-γ-γ*b)+γ*k*(u-2)=0) :
    γ*(2*(1+b)-k*(u-2))=2 := by
  linear_combination -hs

#print axioms tailPinsAffine
#print axioms silentEighthPinsReciprocal

end RKCert.ReviewedNative.SDIRK8TailPinnedAffine
