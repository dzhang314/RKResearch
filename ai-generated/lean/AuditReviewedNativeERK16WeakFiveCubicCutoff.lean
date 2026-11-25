import RKCert.ReviewedNative.ERKOrder16WeakFiveCubicCutoff
import Mathlib.Tactic.NormNum

open Polynomial
open RKCert.ReviewedNative.WeakFive16 RKCert.ReviewedNative.JacobiSix

variable {K : Type*} [Field K] [LinearOrder K] [IsStrictOrderedRing K]

example {q : K[X]} {u a h z : K} (W : CubicWindow q u a h z) :
    ∃ alpha : K, q*cubicHull u a h z = J7 K+C alpha*J6 K :=
  W.product_in_jacobi_pencil

example {q : K[X]} {u a h z : K} (O : OrientedCubicWindow q u a h z) :
    0 < (q*cubicHull u a h z).eval (14/15) ∧
      0 < (q*cubicHull u a h z).eval (15/16) :=
  ⟨O.product_positive_above_cut _ le_rfl, O.product_positive_above_cut _ (by norm_num)⟩

example {q Z : K[X]} {c : Fin 5 → K} (M : Moments q Z c) : q.natDegree ≠ 3 :=
  M.natDegree_ne_three

#print axioms RKCert.ReviewedNative.WeakFive16.CubicWindow.product_in_jacobi_pencil
#print axioms RKCert.ReviewedNative.WeakFive16.OrientedCubicWindow.product_positive_above_cut
#print axioms RKCert.ReviewedNative.WeakFive16.Moments.natDegree_ne_three
