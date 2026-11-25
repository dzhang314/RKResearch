module

public import RKCert.ReviewedNative.ERKOrder16WeakFiveCrossedPositiveTail
public import RKCert.ReviewedNative.FiniteRootSeparatorReal

@[expose] public section

/-! # Real-instance weak-five positive-tail exclusion -/
namespace RKCert.ReviewedNative.WeakFiveCrossedPositiveTail

open Polynomial
open RKCert.ReviewedNative.WeakFive16
open RKCert.ReviewedNative.FiniteRootSeparator
open RKCert.ReviewedNative.CrossedPositiveTailRoots

theorem no_actual_crossed_positive_tail_of_ordered_real_embedding
    {K : Type*} [Field K] [LinearOrder K] [IsStrictOrderedRing K]
    (e : K →+* ℝ) (ord : StrictMono e) {q Z : K[X]} {c : Fin 5 → K}
    (M : Moments q Z c) (degree : q.natDegree=4)
    (phase : CrossedSignPhase (monicProfile q) (c 4) (c 3) (c 2) (c 1)) :
    False :=
  no_actual_crossed_positive_tail e ord M degree phase
    (unit_root_source_real e ord (monicProfile q))

/-- The native real theorem needs no additional root-source premise. -/
theorem no_actual_crossed_positive_tail_real {q Z : ℝ[X]} {c : Fin 5 → ℝ}
    (M : Moments q Z c) (degree : q.natDegree=4)
    (phase : CrossedSignPhase (monicProfile q) (c 4) (c 3) (c 2) (c 1)) :
    False :=
  no_actual_crossed_positive_tail_of_ordered_real_embedding (RingHom.id ℝ) strictMono_id
    M degree phase

end RKCert.ReviewedNative.WeakFiveCrossedPositiveTail
