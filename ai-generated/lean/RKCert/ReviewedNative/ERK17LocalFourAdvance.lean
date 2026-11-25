module

public import RKCert.ReviewedNative.ERK17LocalFourOrbit
public import RKCert.ReviewedNative.LocalLinearAffineAxisAdvance

@[expose] public section

/-! # Actual local, polynomial, or rational advance at order 17 -/
namespace RKResearch.Certified.ERK17

open RKResearch Module Polynomial Graded Graded.Reverse Graded.Reverse.LocalLinear
open RKCert.Endpoint
open scoped Classical Matrix
noncomputable section

variable {K : Type*} [Field K] [LinearOrder K] [IsStrictOrderedRing K]
variable {A : Matrix (Fin 26) (Fin 26) K} {b τ h ξ : Fin 26 → K}
variable {U : Submodule K (Fin 26 → K)} {P Q : K[X]}

set_option maxRecDepth 4000
set_option maxHeartbeats 1000000

theorem width26_local_four_actual_advance
    (ha : ∀ i j, i ≤ j → A i j = 0) (ho : HasOrder 17 A b)
    (F : LocalLinearBand A b 7 2 U τ) (full : primitiveBack A b 7 = annih (treeSpace A 8))
    (D : LocalFourAxes A b τ h ξ U) (trace : LocalLinearTraces A b U τ h 2 5 P Q) :
    (∀ R : K[X], R.natDegree ≤ 7 →
      weightedEval (reflectedClock A) τ R ∈ annih (treeSpace A 7)) ∨
    (∃ a δ v, LocalSignedHeadMode (reflectedClock A) τ ξ (annih (treeSpace A 7)) U a δ v) ∨
    (∃ a v, RationalHeadAdvance (reflectedClock A) τ (annih (treeSpace A 7)) U a v) := by
  let y := reflectedClock A
  let M := annih (treeSpace A 7)
  rcases D.geometry with ⟨a, localized⟩ | ⟨T,Tn,Td,powers,axis⟩
  · obtain ⟨v,live,paid,orth,off,form⟩ := local_four_axis_one_clock_mode ha ho F full D a localized
    exact Or.inr (Or.inl ⟨a,0,v,live,paid,orth,off,form⟩)
  obtain ⟨_, axisPaid, axisOrth⟩ := local_four_axis_paid_nonzero ha ho F full D
  have small (R : K[X]) (rd : R.natDegree ≤ 5-1) :
      τ*ξ ≠ weightedEval y τ R :=
    local_four_axis_no_small_profile ha ho F full D R rd
  have low (R : K[X]) (rd : R.natDegree ≤ 5-1) :
      weightedEval y τ R ∈ M ∧ weightedEval y τ R ∈ annih U := by
    refine ⟨local_four_low_head_paid_E7 ho F R (by omega), ?_⟩
    exact completeOrbit_annih F.invariant F.headOrthogonal ⟨R,rfl⟩
  have relation (i : Fin 26) : T.eval (y i)*(τ i*ξ i) = Q.eval (y i)*τ i := by
    have form := congrFun (show τ*h = weightedEval y τ Q from trace.tauTrace) i
    rw [axis] at form
    simp only [Pi.mul_apply,weightedEval_apply] at form
    linear_combination form
  rcases affine_weighted_axis_advance Tn Td trace.qDeg relation small axisPaid axisOrth low with
    ⟨R,Rd,fit⟩ | L | J
  · apply Or.inl
    let C := diag (nodes A)
    let J : K[X] := (1-X)^2*R
    have jdeg : J.natDegree = 6+1 := by
      have dn : (1-X : K[X]) ≠ 0 := by
        intro z
        have dd : (1-X : K[X]).natDegree = 1 := Thin.one_sub_X_natDegree
        rw [z,natDegree_zero] at dd
        contradiction
      have rn : R ≠ 0 := by intro z; rw [z,natDegree_zero] at Rd; contradiction
      change ((1-X)^2*R).natDegree = 6+1
      rw [natDegree_mul (pow_ne_zero _ dn) rn,natDegree_pow,Thin.one_sub_X_natDegree,Rd]
    have s := local_four_axis_paid_E7 ho F (powers 2 (by decide))
    have eq : weightedEval y τ J = τ*((C^2) ξ) := by
      funext i
      have form := congrFun fit i
      simp only [Pi.mul_apply, weightedEval_apply] at form
      have ci : 1-y i = nodes A i := by
        simp only [y,reflectedClock,Pi.sub_apply,Pi.one_apply]
        ring
      have cc : ((C^2) ξ) i = nodes A i^2*ξ i := by
        simp only [C,pow_two,Module.End.mul_eq_comp,LinearMap.comp_apply,diag_apply]
        ring
      simp only [J,weightedEval_apply,eval_mul,eval_pow,eval_sub,eval_one,eval_X,Pi.mul_apply]
      rw [ci,cc]
      linear_combination -(nodes A i)^2*form
    exact weighted_tests_one_more_of_top (local_four_low_head_paid_E7 ho F) jdeg (eq.symm ▸ s)
  · exact Or.inr (Or.inl L)
  · exact Or.inr (Or.inr J)

end
end RKResearch.Certified.ERK17
