module

public import RKCert.ReviewedNative.ERKOrder16WeakFiveMoments
public import Mathlib.Data.Fin.VecNotation

import Mathlib.Tactic.FinCases
import Mathlib.Tactic.Linarith
import Mathlib.Tactic.Ring

@[expose] public section

/-! # Exact reflection of the weak-five chronological source packet

The reflected nonorigin labels are 1−z, 1−h, 1−a, 1−u. The origin remains
zero; its new nonvanishing condition q(1) ≠ 0 is explicit, not silently
inferred from the existing source packet. -/

namespace RKCert.ReviewedNative.PolynomialCertificate.WeakFiveCells

open Polynomial RKCert.ReviewedNative.WeakFive16 RKCert.ReviewedNative.PositiveRule19
open scoped Polynomial

variable {K : Type*} [Field K] [LinearOrder K] [IsStrictOrderedRing K]

def mirrorClock (c : Fin 5 → K) : Fin 5 → K := ![0, 1-c 4, 1-c 3, 1-c 2, 1-c 1]

noncomputable def mirrorMiddle (c : Fin 5 → K) : K[X] :=
  (X-C (1-c 3))*(X-C (1-c 2))

private theorem refl_comp_twice (P : K[X]) : (P.comp (1-X)).comp (1-X) = P := by
  rw [comp_assoc, show (1-X : K[X]).comp (1-X) = X by
    simp only [sub_comp, one_comp, X_comp, sub_sub_cancel], comp_X]

private theorem refl_deg (P : K[X]) : (P.comp (1-X)).natDegree = P.natDegree := by
  have h : (1-X : K[X]) = -(X-C (1:K)) := by simp [neg_sub]
  rw [natDegree_comp, h, natDegree_neg, natDegree_X_sub_C, mul_one]

private theorem refl_right (P : K[X]) (x : K) :
    integral (1-x) 1 (P.comp (1-X)) = integral 0 x P := by
  have h := (integral_reflect (P.comp (1-X)) (1-x)).symm
  rw [refl_comp_twice P, sub_sub_cancel] at h
  exact h

theorem reflected_source_product {q Z : K[X]} {c : Fin 5 → K} (M : Moments q Z c) :
    (q * nodalTail c Z).comp (1-X) = q.comp (1-X) * nodalTail (mirrorClock c) (mirrorMiddle c) := by
  change (q*((X-C (c 1))*(X-C (c 4))*Z)).comp (1-X) =
    q.comp (1-X)*((X-C (1-c 4))*(X-C (1-c 1))*((X-C (1-c 3))*(X-C (1-c 2))))
  simp only [M.middleFactor, mul_comp, sub_comp, X_comp, C_comp, map_sub, map_one]
  ring

theorem reflected_moments {q Z : K[X]} {c : Fin 5 → K} (M : Moments q Z c)
    (atOne : q.eval 1 ≠ 0) :
    Moments (q.comp (1-X)) (mirrorMiddle c) (mirrorClock c) := by
  have pair {i j : Fin 5} (ne : i ≠ j) : 1-c i ≠ 1-c j :=
    fun h => ne (M.clockSimple (by linarith only [h]))
  have off (i : Fin 5) : (0 : K) ≠ 1-c i := fun h => (M.active i).1 (by linarith only [h])
  refine ⟨?_, ?_, rfl, ?_, ?_, rfl, ?_, ?_, ?_, ?_, ?_, ?_, ?_⟩
  · intro h
    apply M.qNonzero
    rw [← refl_comp_twice q, h, zero_comp]
  · rw [refl_deg]; exact M.qDegree
  · intro i j e
    fin_cases i <;> fin_cases j <;> first | rfl | exact (off _ e).elim | exact (off _ e.symm).elim |
      exact (pair (by decide) e).elim
  · have keep (i : Fin 5) (hi : i ≠ 0) : 1-c i ≠ 1 ∧ (q.comp (1-X)).eval (1-c i) ≠ 0 := by
      refine ⟨fun eq => M.clock_ne_zero hi (by linarith only [eq]), ?_⟩
      simpa only [eval_comp, eval_sub, eval_one, eval_X, sub_sub_cancel] using (M.active i).2
    intro i
    fin_cases i
    · change (0 : K) ≠ 1 ∧ (q.comp (1-X)).eval 0 ≠ 0
      exact ⟨zero_ne_one, by simpa only [eval_comp, eval_sub, eval_one, eval_X, sub_zero] using atOne⟩
    · exact keep 4 (by decide)
    · exact keep 3 (by decide)
    · exact keep 2 (by decide)
    · exact keep 1 (by decide)
  · change integral 0 (1-c 4) (X*q.comp (1-X))=0
    simpa only [mul_comp, sub_comp, one_comp, X_comp, sub_sub_cancel] using
      (integral_reflect ((1-X)*q) (c 4)).trans M.reverseFirst
  · change integral 0 (1-c 4) (X^2*q.comp (1-X))=0
    simpa only [mul_comp, pow_comp, sub_comp, one_comp, X_comp, sub_sub_cancel] using
      (integral_reflect ((1-X)^2*q) (c 4)).trans M.reverseSecond
  · change integral 0 (1-c 3) (X*(X-C (1-c 4))*q.comp (1-X))=0
    have alg : ((1-X)*(C (c 4)-X)*q).comp (1-X) = X*(X-C (1-c 4))*q.comp (1-X) := by
      simp only [mul_comp, sub_comp, X_comp, C_comp, one_comp, map_sub, map_one]
      ring
    simpa only [alg] using (integral_reflect ((1-X)*(C (c 4)-X)*q) (c 3)).trans M.reverseInner
  · change integral (1-c 1) 1 ((1-X)*q.comp (1-X))=0
    simpa only [mul_comp, X_comp] using (refl_right (X*q) (c 1)).trans M.forwardFirst
  · change integral (1-c 1) 1 ((1-X)^2*q.comp (1-X))=0
    simpa only [mul_comp, pow_comp, X_comp] using
      (refl_right (X^2*q) (c 1)).trans M.forwardSecond
  · change integral (1-c 2) 1 ((1-X)*(C (1-c 1)-X)*q.comp (1-X))=0
    have alg : (X*(X-C (c 1))*q).comp (1-X) = (1-X)*(C (1-c 1)-X)*q.comp (1-X) := by
      simp only [mul_comp, sub_comp, X_comp, C_comp, map_sub, map_one]
      ring
    simpa only [alg] using (refl_right (X*(X-C (c 1))*q) (c 2)).trans M.forwardInner
  · intro H hd
    have paid := M.weightedMoments (H.comp (1-X)) (by rwa [refl_deg])
    have alg : (X*(1-X)*(q*nodalTail c Z)*(H.comp (1-X))).comp (1-X) =
        X*(1-X)*(q.comp (1-X)*nodalTail (mirrorClock c) (mirrorMiddle c))*H := by
      rw [mul_comp, refl_comp_twice, mul_comp, reflected_source_product M]
      simp only [mul_comp, sub_comp, X_comp, one_comp, sub_sub_cancel]
      ring
    simpa only [alg, sub_zero] using
      (integral_reflect (X*(1-X)*(q*nodalTail c Z)*(H.comp (1-X))) 0).trans paid

end RKCert.ReviewedNative.PolynomialCertificate.WeakFiveCells
