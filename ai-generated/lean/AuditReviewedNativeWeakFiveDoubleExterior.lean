import RKCert.ReviewedNative.ERKOrder16WeakFiveDoubleExterior

open Polynomial RKCert.ReviewedNative.PositiveRule19
open RKCert.ReviewedNative.FiniteOrderedSigns
open RKCert.ReviewedNative.EvenExteriorBarycentric
open RKCert.ReviewedNative.SaturatedEvenMoment
open RKCert.ReviewedNative.WeakFive16

variable {K : Type*} [Field K] [LinearOrder K] [IsStrictOrderedRing K]

example {T : K[X]} (tm : T.Monic) (td : T.natDegree = 6)
    (alt : HasAlternationsOn T (Set.Ioo (0 : K) 1) 6) :
    (∀ x : K, x ≤ 0 → 0 < T.eval x) ∧
      (∀ x : K, 1 ≤ x → 0 < T.eval x) ∧
      (∀ x y : K, x < y → y ≤ 0 → T.eval y < T.eval x) ∧
      (∀ x y : K, 1 ≤ x → x < y → T.eval x < T.eval y) :=
  exterior_of_even_alternations (n := 3) (by decide) tm td alt

example {T : K[X]} {l r : K} (tm : T.Monic) (td : T.natDegree = 6)
    (l0 : l < 0) (r1 : 1 < r)
    (six : ∀ R : K[X], R.natDegree ≤ 5 →
      integral 0 1 (fourWeight l 0 1 r*T*R)=0) :
    0 < integral 0 1 T :=
  integral_pos_of_six tm td l0 r1 six

example {q Z : K[X]} {c : Fin 5 → K}
    (M : Moments q Z c) (qd : q.natDegree = 4) : ¬ DoubleExteriorShapes c :=
  M.no_classified_double_exterior qd

#check @RKResearch.Certified.ERK16.width24_weak_five_excludes_classified_double_exterior
#print axioms RKCert.ReviewedNative.EvenExteriorBarycentric.exterior_of_even_alternations
#print axioms RKCert.ReviewedNative.SaturatedEvenMoment.integral_pos_of_saturated_even
#print axioms RKCert.ReviewedNative.WeakFive16.Moments.no_opposed_outer_double_exterior
#print axioms RKCert.ReviewedNative.WeakFive16.Moments.no_left_crossed_double_exterior
#print axioms RKCert.ReviewedNative.WeakFive16.Moments.no_right_crossed_double_exterior
#print axioms RKResearch.Certified.ERK16.width24_weak_five_excludes_classified_double_exterior
