module

public import RKCert.ReviewedNative.CrossedGaussianEndpointBridge
import Mathlib.Tactic.Linarith
import Mathlib.Tactic.NormNum
import Mathlib.Tactic.Ring

@[expose] public section

/-! # Reflection for the oriented crossed endpoint consumer

Draft. Reflect the actual signed law, marked factors, and the original
two reverse endpoint moments. No new moment is inserted.
-/
namespace RKCert.ReviewedNative.CrossedGaussianReflection

open Polynomial
open RKCert.ReviewedNative.PositiveRule19
open RKCert.ReviewedNative.FiniteGaussianNodalLift
open RKCert.ReviewedNative.FiniteGaussianGridPositivity
open RKCert.ReviewedNative.CrossedGaussianSignedAdapter
open RKCert.ReviewedNative.CrossedGaussianEndpointBridge
open scoped BigOperators

noncomputable section
variable {K : Type*} [Field K] [LinearOrder K] [IsStrictOrderedRing K]

def flipClock (x : K) : K := 1-x
def flipPoly (P : K[X]) : K[X] := P.comp (1-X)

theorem flipClock_involutive (x : K) : flipClock (flipClock x) = x := by
  simp only [flipClock,sub_sub_cancel]

theorem flipClock_order {x y : K} (xy : x<y) : flipClock y<flipClock x := by
  unfold flipClock
  linarith only [xy]

def flipEmbedding (K : Type*) [Field K] [LinearOrder K] [IsStrictOrderedRing K] : K ↪ K :=
  ⟨flipClock, fun _ _ eq =>
    (flipClock_involutive _).symm.trans ((congrArg flipClock eq).trans (flipClock_involutive _))⟩

theorem flipEmbedding_apply (x : K) : flipEmbedding K x = flipClock x := rfl

theorem flipPoly_eval (P : K[X]) (x : K) : (flipPoly P).eval x = P.eval (flipClock x) := by
  simp only [flipPoly,flipClock,eval_comp,eval_sub,eval_one,eval_X]

theorem flipPoly_mul (P Q : K[X]) : flipPoly (P*Q) = flipPoly P*flipPoly Q := by
  simp only [flipPoly,mul_comp]

theorem flipPoly_involutive (P : K[X]) : flipPoly (flipPoly P) = P := by
  simp only [flipPoly,comp_assoc,sub_comp,one_comp,X_comp,sub_sub_cancel,comp_X]

private theorem flipSub : 1-(X:K[X]) = -(X-C (1:K)) := by rw [map_one]; ring

private theorem flipSubDegree : (1-(X:K[X])).natDegree = 1 := by
  rw [flipSub,natDegree_neg,natDegree_X_sub_C]

theorem flipPoly_degree (P : K[X]) : (flipPoly P).natDegree = P.natDegree := by
  simp only [flipPoly,natDegree_comp,flipSubDegree,mul_one]

theorem flipPoly_unitWeight : flipPoly (unitWeight K) = unitWeight K := by
  simp only [flipPoly,unitWeight,mul_comp,sub_comp,one_comp,X_comp,sub_sub_cancel]
  ring

private theorem flipLeading : (1-(X:K[X])).leadingCoeff = -1 := by
  rw [flipSub,leadingCoeff_neg,(monic_X_sub_C (1:K)).leadingCoeff]

theorem flip_monic_quadratic (B : K[X]) (monic : B.Monic) (deg : B.natDegree=2) :
    (flipPoly B).Monic := by
  change (B.comp (1-X)).leadingCoeff = 1
  rw [leadingCoeff_comp (by rw [flipSubDegree]; decide),
    monic.leadingCoeff,flipLeading,deg]
  norm_num

theorem flip_linear (r : K) : flipPoly (X-C r) = -(X-C (flipClock r)) := by
  simp only [flipPoly,flipClock,sub_comp,X_comp,C_comp,map_sub,map_one]
  ring

theorem flip_crossed_factor (q B : K[X]) (r s : K) (factor : q=B*((X-C r)*(X-C s))) :
    flipPoly q = flipPoly B*((X-C (flipClock s))*(X-C (flipClock r))) := by
  rw [factor]
  simp only [flipPoly_mul,flip_linear,neg_mul_neg]
  ring

theorem unitMoment_flip (q P : K[X]) : unitMoment (flipPoly q) P = unitMoment q (flipPoly P) := by
  have eq : (((unitWeight K*q)*flipPoly P).comp (1-X)) = (unitWeight K*flipPoly q)*P := by
    change flipPoly ((unitWeight K*q)*flipPoly P) = _
    simp only [flipPoly_mul,flipPoly_unitWeight,flipPoly_involutive]
  simpa only [sub_zero,eq,unitMoment_apply] using integral_reflect ((unitWeight K*q)*flipPoly P) 0

theorem exact_flip_rule {q : K[X]} {old : Finset K} {μ : K → K} {d : ℕ}
    (law : ExactRule (unitMoment q) old id μ d) :
    ExactRule (unitMoment (flipPoly q)) (old.map (flipEmbedding K)) id (μ ∘ flipClock) d := by
  intro P pd
  have qd : (flipPoly P).natDegree ≤ d := by rwa [flipPoly_degree]
  rw [unitMoment_flip,law _ qd,Finset.sum_map]
  apply Finset.sum_congr rfl
  intro x _
  simp only [id_eq,flipPoly_eval,Function.comp_apply,flipEmbedding_apply,flipClock_involutive]

theorem flip_fourMarks (z h a u : K) :
    (fourMarks z h a u).map (flipEmbedding K) =
      fourMarks (flipClock u) (flipClock a) (flipClock h) (flipClock z) := by
  ext x
  simp only [fourMarks,Finset.map_insert,Finset.map_singleton,flipEmbedding_apply,
    Finset.mem_insert,Finset.mem_singleton]
  simp only [or_assoc,or_left_comm,or_comm]

theorem flip_forward_first (q : K[X]) (z : K)
    (paid : integral z 1 ((1-X)*q)=0) :
    integral 0 (flipClock z) (X*flipPoly q) = 0 := by
  have e := integral_reflect ((1-X)*q) z
  rw [mul_comp, sub_comp, one_comp, X_comp, sub_sub_cancel, paid] at e
  exact e

theorem flip_forward_second (q : K[X]) (z : K)
    (paid : integral z 1 ((1-X)^2*q)=0) :
    integral 0 (flipClock z) (X^2*flipPoly q) = 0 := by
  have e := integral_reflect ((1-X)^2*q) z
  rw [mul_comp, pow_comp, sub_comp, one_comp, X_comp, sub_sub_cancel, paid] at e
  exact e

theorem flip_oriented (B : K[X]) (h : B.eval 0 ≤ B.eval 1) :
    (flipPoly B).eval 1 ≤ (flipPoly B).eval 0 := by
  simpa only [flipPoly_eval,flipClock,sub_self,sub_zero] using h

end
end RKCert.ReviewedNative.CrossedGaussianReflection
