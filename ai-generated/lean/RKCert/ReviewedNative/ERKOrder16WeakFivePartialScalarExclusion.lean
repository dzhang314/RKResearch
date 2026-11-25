module

public import RKCert.ReviewedNative.ERKOrder16OrderedAssembly
public import RKCert.ReviewedNative.ERKOrder16WeakFiveSoleOuterEndpoint
public import RKCert.ReviewedNative.ERKOrder16WeakFiveCrossedNegativeTail

@[expose] public section

/-! # Direct intake into the exact reviewed weak-five scalar obligation

Only sole inner exterior and three interior changes remain as inputs.
This file neither assumes nor concludes the independent weak-four scalar
obligation. No unconditional weak-five exclusion or stage floor is asserted.
-/

namespace RKResearch.Certified.ERK16

open Polynomial RKCert.ReviewedNative.WeakFive16
open RKCert.ReviewedNative.PolynomialCertificate.WeakFiveCells
open scoped Polynomial

universe u
variable {K : Type u} [Field K] [LinearOrder K] [IsStrictOrderedRing K]

/-- Exact type expected by the reviewed order-sixteen assembly. The only
two callback premises consume the original packet and the classified
remaining geometry. All other classified native scalar sectors are handled
on the same actual packet, with no fresh chronological labels. -/
theorem weak_five_scalar_exclusion_of_sole_inner_three_interior
    (soleInner : ∀ {q Z : K[X]} {c : Fin 5 → K}, Moments q Z c → SoleInner q c → False)
    (threeInterior : ∀ {q Z : K[X]} {c : Fin 5 → K}, Moments q Z c → ThreeInterior q c → False) :
    WeakFiveScalarExclusion K := by
  intro q Z c M
  rcases actual_weak_five_without_outer M with inner | three | neg
  · exact soleInner M inner
  · exact threeInterior M three
  · obtain ⟨E, r, s, b₀, b₁, T⟩ := neg
    exact no_actual_crossed_negative_tail T

end RKResearch.Certified.ERK16
