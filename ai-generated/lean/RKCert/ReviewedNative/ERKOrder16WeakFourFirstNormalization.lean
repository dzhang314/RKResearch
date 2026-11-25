module

public import RKCert.ReviewedNative.ERKOrder16WeakFourFirstBoxes
import Mathlib.Tactic.Linarith
import Mathlib.Tactic.Ring

@[expose] public section

/-! # Algebraic change of factors before a weak-four sign-box check

This file contains no boxes, table or reference computations. It gives
the rescalings used by a separately-affine product solver. In particular
ordinary interior factors are normalized by the *sum* of the two clocks,
so there is no singular denominator when an interval touches zero at one
of its (necessarily disjoint) strips.
-/
namespace RKCert.ReviewedNative.WeakFourFirstOnly

open Polynomial
open RKCert.ReviewedNative.PositiveRule19
open scoped BigOperators

noncomputable section
variable {K : Type*} [Field K] [LinearOrder K] [IsStrictOrderedRing K]

theorem unitPair_C_mul_iff {c : K} (cn : c≠0) (P : K[X]) :
    UnitPair (C c*P) ↔ UnitPair P := by
  have integral_scale (T : K[X]) :
      integral 0 1 (T*(C c*P))=c*integral 0 1 (T*P) := by
    rw [show T*(C c*P)=C c*(T*P) from by ring]
    simpa only [Polynomial.smul_eq_C_mul,smul_eq_mul] using
      (integral (0:K) 1).map_smul c (T*P)
  unfold UnitPair
  simp only [integral_scale,mul_eq_zero,cn,false_or]

/-- Individual nonzero rescalings preserve the two moment zeros. -/
theorem unitPair_factors_iff {ι : Type*} (r : ι → K) (I : Finset ι)
    (a : K) (k : ι → K) (f : ι → K[X])
    (scale : ∀ i∈I, C a*X-C (r i)=C (k i)*f i)
    (nonzero : ∀ i∈I, k i≠0) :
    UnitPair (stoppedFactors r I a) ↔ UnitPair (∏ i∈I,f i) := by
  have fEq : stoppedFactors r I a = C (∏ i∈I,k i)*(∏ i∈I,f i) := by
    unfold stoppedFactors
    rw [map_prod,←Finset.prod_mul_distrib]
    exact Finset.prod_congr rfl scale
  rw [fEq,unitPair_C_mul_iff (Finset.prod_ne_zero_iff.mpr nonzero)]

def ordinaryFactor (w : K) : K[X] := C (1-w)*X-C w
def lowFitFactor (w : K) : K[X] := C w*X+C (1-w)
def highFitFactor (w : K) : K[X] := 1-C w*X

theorem ordinaryFactor_scale {a r : K} (d : a+r≠0) :
    C a*X-C r = C (a+r)*ordinaryFactor (r/(a+r)) := by
  let w := r/(a+r)
  have wr : (a+r)*w=r := by
    dsimp only [w]
    rw [mul_comm (a+r),div_mul_cancel₀ _ d]
  have wa : (a+r)*(1-w)=a := by rw [mul_sub,mul_one,wr]; ring
  change C a*X-C r = C (a+r)*ordinaryFactor w
  rw [ordinaryFactor,mul_sub,←mul_assoc,←C_mul,wa,←C_mul,wr]

theorem lowFitFactor_scale {a e : K} (d : a-e≠0) :
    C a*X-C e = C (a-e)*lowFitFactor (a/(a-e)) := by
  let w := a/(a-e)
  have wa : (a-e)*w=a := by
    dsimp only [w]
    rw [mul_comm (a-e),div_mul_cancel₀ _ d]
  have we : (a-e)*(1-w)=-e := by rw [mul_sub,mul_one,wa]; ring
  change C a*X-C e = C (a-e)*lowFitFactor w
  rw [lowFitFactor,mul_add,←mul_assoc,←C_mul,wa,←C_mul,we,C_neg,sub_eq_add_neg]

theorem highFitFactor_scale {a e : K} (d : e≠0) :
    C a*X-C e = C (-e)*highFitFactor (a/e) := by
  have eq : (-e)*(a/e)=-a := by
    rw [neg_mul,mul_comm e,div_mul_cancel₀ _ d]
  rw [highFitFactor,mul_sub,mul_one,←mul_assoc,←C_mul,eq,map_neg,map_neg]
  ring

theorem ordinaryFactor_pencil (w : K) :
    ordinaryFactor w = OrderedPolynomialSignStrips.pencil (X:K[X]) (-1) w := by
  simp only [ordinaryFactor,OrderedPolynomialSignStrips.pencil,mul_neg,mul_one,sub_eq_add_neg]

theorem lowFitFactor_pencil (w : K) :
    lowFitFactor w = OrderedPolynomialSignStrips.pencil (1:K[X]) X w := by
  simp only [lowFitFactor,OrderedPolynomialSignStrips.pencil,mul_one]
  exact add_comm _ _

theorem highFitFactor_pencil (w : K) :
    highFitFactor w = OrderedPolynomialSignStrips.pencil (1:K[X]) (1-X) w := by
  simp only [highFitFactor,OrderedPolynomialSignStrips.pencil,map_sub,map_one,mul_one,mul_sub]
  ring

/-- One scalar proves the normalization of both exterior orientations.
The bound uses only the leading reference coefficient, never division by
the root itself or by the compactified pencil parameter. -/
theorem mul_outer_of_vieta {v d A B S e : K} (dn : d≠0)
    (H : (1-v)*A+v*B = -(v*d)*(e+S)) :
    v*e = -((1-v)*A+v*B)/d-v*S := by
  have aux : -((1-v)*A+v*B)/d = v*(e+S) := by
    apply (div_eq_iff dn).2
    rw [H]
    ring
  rw [aux]
  ring

/-- Ratio bounds from disjoint nonnegative clock intervals. Only the
two displayed cross denominators and the actual sum are assumed positive.
Either clock's own lower endpoint may equal zero. -/
theorem compactRatio_bounds {a r al ah rl rh : K}
    (a0 : 0≤al) (r0 : 0≤rl) (A : al≤a ∧ a≤ah) (R : rl≤r ∧ r≤rh)
    (dl : ah+rl>0) (dh : al+rh>0) (d : a+r>0) :
    rl/(ah+rl) ≤ r/(a+r) ∧ r/(a+r) ≤ rh/(al+rh) := by
  have ah0 : 0≤ah := a0.trans (A.1.trans A.2)
  have rh0 : 0≤rh := r0.trans (R.1.trans R.2)
  constructor
  · apply (div_le_div_iff₀ dl d).2
    have h : rl*a ≤ r*ah := (mul_le_mul_of_nonneg_left A.2 r0).trans
      (mul_le_mul_of_nonneg_right R.1 ah0)
    calc
      rl*(a+r) = rl*a+rl*r := by ring
      _ ≤ r*ah+rl*r := add_le_add h le_rfl
      _ = r*(ah+rl) := by ring
  · apply (div_le_div_iff₀ d dh).2
    have h : r*al ≤ rh*a := (mul_le_mul_of_nonneg_right R.2 a0).trans
      (mul_le_mul_of_nonneg_left A.1 rh0)
    calc
      r*(al+rh) = r*al+r*rh := by ring
      _ ≤ rh*a+r*rh := add_le_add h le_rfl
      _ = rh*(a+r) := by ring

end
end RKCert.ReviewedNative.WeakFourFirstOnly
