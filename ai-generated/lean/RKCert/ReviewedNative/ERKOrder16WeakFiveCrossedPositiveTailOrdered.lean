module

public import RKCert.ReviewedNative.ERKOrder16WeakFiveCrossedPositiveTail
public import RKCert.ReviewedNative.OrderedSingleGapRoot

@[expose] public section

/-! # Ordered-field crossed positive-tail endpoint

Draft: the root factory replaces the previous explicit UnitRootSource
premise without changing the actual phase or any paid moment.
-/
namespace RKCert.ReviewedNative.WeakFiveCrossedPositiveTail

open Polynomial
open RKCert.ReviewedNative.WeakFive16
open RKCert.ReviewedNative.CrossedPositiveTailRoots
open RKCert.ReviewedNative.OrderedSingleGapRoot

theorem no_actual_crossed_positive_tail_ordered
    {K : Type*} [Field K] [LinearOrder K] [IsStrictOrderedRing K]
    {q Z : K[X]} {c : Fin 5 → K}
    (M : Moments q Z c) (degree : q.natDegree=4)
    (phase : CrossedSignPhase (monicProfile q) (c 4) (c 3) (c 2) (c 1)) :
    False := by
  obtain ⟨E,source⟩ := exists_unitRootSource (monicProfile q)
  exact no_actual_crossed_positive_tail E.embed E.mono M degree phase source

end RKCert.ReviewedNative.WeakFiveCrossedPositiveTail
