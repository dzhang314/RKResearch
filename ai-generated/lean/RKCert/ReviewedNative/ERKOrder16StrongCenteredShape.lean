module

public import RKCert.ReviewedNative.ERKOrder16StrongCenteredMoments
public import RKCert.ReviewedNative.UnitBubbleMoments

import Mathlib.Tactic.NormNum
import Mathlib.Tactic.Ring

@[expose] public section

/-! # The actual two simple interior pivots of the centered scalar cut -/
namespace RKCert.ReviewedNative.StrongCentered16

open Polynomial
open RKCert.ReviewedNative.UnitBubbleMoments

variable {K : Type*} [Field K] [LinearOrder K]

noncomputable abbrev contrastProduct (q : K[X]) (a z : K) : K[X] := (X-C a)*(X-C z)*q

structure Shape (q : K[X]) (a z : K) : Prop where
  qDegree : q.natDegree=5
  firstInterior : a∈Set.Ioo (0:K) 1
  lastInterior : z∈Set.Ioo (0:K) 1
  firstValue : q.eval a≠0
  lastValue : q.eval z≠0
  oddContrast : (contrastProduct q a z).comp (1-X)=-(contrastProduct q a z)

variable [IsStrictOrderedRing K]

/-- The local equations play no role in this consequence of the seven
global tests. In particular, neither chronological order is assumed. -/
theorem Moments.shape {q : K[X]} {a z : K} (h : Moments q a z) : Shape q a z := by
  let J := contrastProduct q a z
  have an : (X-C a : K[X])≠0 := (monic_X_sub_C a).ne_zero
  have zn : (X-C z : K[X])≠0 := (monic_X_sub_C z).ne_zero
  have jn : J≠0 := mul_ne_zero (mul_ne_zero an zn) h.qNonzero
  have dJ : J.natDegree=q.natDegree+2 := by
    dsimp only [J,contrastProduct]
    rw [natDegree_mul (mul_ne_zero an zn) h.qNonzero,natDegree_mul an zn,
      natDegree_X_sub_C,natDegree_X_sub_C]
    omega
  have orth : OrthogonalThrough J 6 := fun H hd => h.weightedMoments H hd
  have jd := degree_eq_succ jn (by have := h.qDegree; omega) orth (by decide)
  have ha := quotient_interior_simple (r:=a) (U:=(X-C z)*q) jn jd orth (by decide)
    (by simp only [J,mul_assoc])
  have hz := quotient_interior_simple (r:=z) (U:=(X-C a)*q) jn jd orth (by decide)
    (by dsimp only [J,contrastProduct]; ring)
  refine ⟨by omega,ha.1,hz.1,?_,?_,?_⟩
  · intro z
    exact ha.2 (by simp only [eval_mul,z,mul_zero])
  · intro z
    exact hz.2 (by simp only [eval_mul,z,mul_zero])
  · have r := signed_reflection jn jd orth (by decide)
    have c : (-1:K)^(6+1:ℕ)=-1 := by norm_num
    simpa only [J,c,map_neg,map_one,neg_one_mul] using r

end RKCert.ReviewedNative.StrongCentered16
