module

public import RKCert.ReviewedNative.CrossedGaussianSignedAdapter
import Mathlib.Tactic.Linarith
import Mathlib.Tactic.NormNum
import Mathlib.Tactic.Ring

@[expose] public section

/-! # Conditional crossed positive-tail contradiction

Draft. Root selection and the base-field sign census are upstream. The
only inequalities about the residual here are finite mesh checks and the
seven rational coefficient samples. In particular there is no transfer of
base positivity to every point of a coefficient extension.
-/
namespace RKCert.ReviewedNative.CrossedGaussianEndpointBridge

open Polynomial
open RKCert.ReviewedNative.PositiveRule19
open RKCert.ReviewedNative.FiniteGaussianNodalLift
open RKCert.ReviewedNative.FiniteGaussianGridPositivity
open RKCert.ReviewedNative.FiniteGaussianLocalizer
open RKCert.ReviewedNative.CrossedGaussianCheckedMoments
open RKCert.ReviewedNative.CrossedGaussianSignedAdapter
open RKCert.ReviewedNative.CrossedGaussianRational

noncomputable section
variable {K : Type*} [Field K] [LinearOrder K] [IsStrictOrderedRing K]

private theorem integral_split (l u r : K) (P : K[X]) :
    integral l u P + integral u r P = integral l r P := by
  simp only [integral_apply]
  ring

/-- The genuine two forward endpoint moments imply strictly positive
full signed tail when the residual is nonnegative on the actual tail
grid. This consumer does not use the two inner port equations. -/
theorem positive_tail_of_endpoint_pair
    (q B : K[X]) (r s u : K)
    (u0 : 0<u) (u1 : u<1) (ru : r<u) (su : s<u)
    (factor : q=B*((X-C r)*(X-C s)))
    (Bne : B ≠ 0) (Bdeg : B.natDegree ≤ 2)
    (tailGrid : ∀ i : Fin 19, 0 ≤ B.eval (intervalPoint u 1 i))
    (end₁ : integral 0 u (X*q) = 0) (end₂ : integral 0 u (X^2*q) = 0) :
    0 < integral 0 1 (unitWeight K*q) := by
  have qne : q ≠ 0 := by
    rw [factor]
    exact mul_ne_zero Bne (mul_ne_zero (X_sub_C_ne_zero r) (X_sub_C_ne_zero s))
  have qd : q.natDegree ≤ 4 := by
    rw [factor]
    exact natDegree_mul_le_of_le Bdeg (natDegree_mul_le_of_le
      (by simp : (X-C r : K[X]).natDegree ≤ 1)
      (by simp : (X-C s : K[X]).natDegree ≤ 1))
  have wqdeg : (unitWeight K*q).natDegree < 19 :=
    (natDegree_mul_le_of_le unitWeight_degree qd).trans_lt (by decide)
  have htail : 0 < integral u 1 (unitWeight K*q) := by
    apply integral_pos_of_grid_nonneg u1 _ (mul_ne_zero unitWeight_nonzero qne) wqdeg
    intro i
    have hx := intervalPoint_mem u1 i
    rw [factor]
    simp only [eval_mul,eval_sub,eval_X,eval_C]
    exact mul_nonneg (unitWeight_eval_pos (u0.trans hx.1) hx.2).le
      (mul_nonneg (tailGrid i)
        (mul_nonneg (sub_nonneg.mpr (ru.trans hx.1).le) (sub_nonneg.mpr (su.trans hx.1).le)))
  have hp : unitWeight K*q = X*q-X^2*q := by unfold unitWeight; ring
  have hstop : integral 0 u (unitWeight K*q) = 0 := by
    rw [hp,map_sub,end₁,end₂,sub_zero]
  rw [← integral_split 0 u 1 (unitWeight K*q),hstop,zero_add]
  exact htail

private theorem centered_linear_pull (r : K) :
    (X-C (centerPoint r)).comp (centerMap K) = C (2:K)*(X-C r) := by
  rw [sub_comp, X_comp, C_comp]
  simp only [centerMap,centerPoint,map_sub,map_mul,C_1,C_ofNat]
  ring

/-- The two marked factors each contribute 2 under centering, in
addition to the residual's factor 4 and normalization 6. -/
theorem centered_pair_pullback (A k r s : K) (q B : K[X])
    (pull : (centeredResidual A k).comp (centerMap K) = C (4:K)*B)
    (factor : q=B*((X-C r)*(X-C s))) :
    centerRef K (centeredResidual A k*((X-C (centerPoint r))*(X-C (centerPoint s)))) =
      96*integral 0 1 (unitWeight K*q) := by
  have hp :
      X*(1-X)*((centeredResidual A k*((X-C (centerPoint r))*(X-C (centerPoint s)))).comp
        (centerMap K)) = C (16:K)*(unitWeight K*q) := by
    rw [factor]
    simp only [mul_comp,pull,centered_linear_pull,unitWeight,C_ofNat]
    ring
  rw [centerRef_pullback,hp,moment_C_mul]
  ring

/-- Exactly the coefficient-side tests in the rational Gaussian sign
lemma. They require only the listed rational samples of B. -/
structure CoeffTests (A k : K) : Prop where
  a0 : 0 ≤ A
  shear : 0 ≤ k
  quarter : 0 ≤ A+1/16-k/4
  half : 0 ≤ A+1/4-k/2
  twoThirds : 0 ≤ A+4/9-(2:K)/3*k
  threeQuarters : 0 ≤ A+9/16-(3:K)/4*k
  nineTenths : 0 ≤ A+81/100-(9:K)/10*k
  one : 0 ≤ A+1-k

def rationalSamples (K : Type*) [Field K] : List K := [0,1/4,1/2,2/3,3/4,9/10,1]

private theorem eval_residual_scalar (A k y : K) :
    (centeredResidual A k).eval y = A+y^2-k*y := by
  simp only [centeredResidual,eval_sub,eval_add,eval_pow,eval_mul,eval_X,eval_C]

theorem coeffTests_of_rational_samples (A k : K) (B : K[X])
    (pull : (centeredResidual A k).comp (centerMap K) = C (4:K)*B)
    (oriented : B.eval 1 ≤ B.eval 0)
    (samples : ∀ y ∈ rationalSamples K, 0 ≤ B.eval (uncenterPoint y)) :
    CoeffTests A k := by
  have base (y : K) (hy : y ∈ rationalSamples K) : 0 ≤ A+y^2-k*y := by
    rw [← eval_residual_scalar,centeredResidual_eval_of_pull A k B pull y]
    exact mul_nonneg (by norm_num) (samples y hy)
  have left := centeredResidual_eval_of_pull A k B pull (-1)
  have right := centeredResidual_eval_of_pull A k B pull 1
  norm_num [eval_residual_scalar,uncenterPoint] at left right
  refine ⟨?_,?_,?_,?_,?_,?_,?_,?_⟩
  · have h := base 0 (by simp [rationalSamples])
    linarith only [h]
  · linarith only [left,right,oriented]
  · have h := base (1/4) (by simp [rationalSamples])
    linarith only [h]
  · have h := base (1/2) (by simp [rationalSamples])
    linarith only [h]
  · have h := base (2/3) (by simp [rationalSamples])
    linarith only [h]
  · have h := base (3/4) (by simp [rationalSamples])
    linarith only [h]
  · have h := base (9/10) (by simp [rationalSamples])
    linarith only [h]
  · have h := base 1 (by simp [rationalSamples])
    linarith only [h]

/-- Complete consumer of the root-selected strictly interior positive
crossed sector. Distinctness/second-and-fifth order is supplied separately;
no extra primitive equation is needed. -/
theorem crossed_tail_contradiction_with_marks (old : Finset K)
    (z r s u A k : K) (q B : K[X]) (mass : K → K)
    (count : old.card=4) (freshS : s ∉ old) (freshR : r ∉ insert s old)
    (leftRank : ∀ x ∈ addMarks old r s, x<r → x=z)
    (rightRank : ∀ x ∈ addMarks old r s, s<x → x=u)
    (u0 : 0<u) (u1 : u<1) (ru : r<u) (su : s<u)
    (factor : q=B*((X-C r)*(X-C s)))
    (pull : (centeredResidual A k).comp (centerMap K) = C (4:K)*B)
    (Bne : B ≠ 0) (Bdeg : B.natDegree ≤ 2)
    (unitGrid : ∀ i : Fin 19, 0 ≤ B.eval (intervalPoint (0:K) 1 i))
    (tailGrid : ∀ i : Fin 19, 0 ≤ B.eval (intervalPoint u 1 i))
    (coeff : CoeffTests A k) (law : ExactRule (unitMoment q) old id mass 9)
    (end₁ : integral 0 u (X*q) = 0) (end₂ : integral 0 u (X^2*q) = 0) :
    False := by
  have exactSix := six_exact_of_signed_four old r s q B count freshS freshR factor mass law
  have exactCentered := centered_exact_of_unit_rule B A k pull exactSix
  let unitPos := @six_masses_pos K _ _ _ old r s B count freshS freshR Bne Bdeg unitGrid exactSix
  have centerPos := centerMass_pos_of_unit (s := addMarks old r s)
    (μ := cardinalMass (unitMoment B) (addMarks old r s) id) (fun _ hx => unitPos hx)
  have neg := signed_pair_neg (centerRef K) centerRef_powers centerRef_even centerRef_nonneg
    (fun y hy => (centerPos y hy).le) exactCentered
    (centered_second_exit z r leftRank) (centered_penultimate_exit s u rightRank)
    coeff.a0 coeff.shear coeff.quarter coeff.half coeff.twoThirds coeff.threeQuarters
    coeff.nineTenths coeff.one
  rw [centered_pair_pullback A k r s q B pull factor] at neg
  have pos := positive_tail_of_endpoint_pair q B r s u u0 u1 ru su factor Bne Bdeg tailGrid end₁ end₂
  linarith only [pos, neg]

def fourMarks (z h a u : K) : Finset K := {z,h,a,u}

/-- Only finite order/distinctness, independent of signed moments. -/
theorem crossed_mark_data (z r h a s u : K)
    (zr : z<r) (rh : r<h) (ha : h<a) (as' : a<s) (su : s<u) :
    (fourMarks z h a u).card=4 ∧ s ∉ fourMarks z h a u ∧
    r ∉ insert s (fourMarks z h a u) ∧
    (∀ x ∈ addMarks (fourMarks z h a u) r s, x<r → x=z) ∧
    (∀ x ∈ addMarks (fourMarks z h a u) r s, s<x → x=u) := by
  have zh := zr.trans rh
  have za := zh.trans ha
  have au := as'.trans su
  have hu := ha.trans au
  have zu := zh.trans hu
  have rs := rh.trans (ha.trans as')
  have rz : r ≠ z := ne_of_gt zr
  have ra : r ≠ a := ne_of_lt (rh.trans ha)
  have ru : r ≠ u := ne_of_lt (rs.trans su)
  have hs : h<s := ha.trans as'
  have zs : z<s := zh.trans hs
  have count : (fourMarks z h a u).card=4 := by
    unfold fourMarks
    have az : a ∉ ({u} : Finset K) := by simp [ne_of_lt au]
    have hz : h ∉ ({a,u} : Finset K) := by simp [ne_of_lt ha,ne_of_lt hu]
    have zz : z ∉ ({h,a,u} : Finset K) := by simp [ne_of_lt zh,ne_of_lt za,ne_of_lt zu]
    rw [Finset.card_insert_of_notMem zz,Finset.card_insert_of_notMem hz,
      Finset.card_insert_of_notMem az,Finset.card_singleton]
  have freshS : s ∉ fourMarks z h a u := by
    simp [fourMarks,ne_of_gt zs,ne_of_gt hs,ne_of_gt as',ne_of_lt su]
  have freshR : r ∉ insert s (fourMarks z h a u) := by
    simp [fourMarks,ne_of_lt rs,rz,ne_of_lt rh,ra,ru]
  have cases (x : K) : x ∈ addMarks (fourMarks z h a u) r s ↔
      x=r ∨ x=s ∨ x=z ∨ x=h ∨ x=a ∨ x=u := by simp [addMarks,fourMarks]
  refine ⟨count,freshS,freshR,?_,?_⟩
  · intro x hx hx'
    rcases (cases x).mp hx with rfl | rfl | rfl | rfl | rfl | rfl
    all_goals
      first
      | rfl
      | exfalso; linarith only [hx',zr,rh,ha,as',su]
  · intro x hx hx'
    rcases (cases x).mp hx with rfl | rfl | rfl | rfl | rfl | rfl
    all_goals
      first
      | rfl
      | exfalso; linarith only [hx',zr,rh,ha,as',su]

/-- Interface at actual crossed marks, after selecting the two root
factors and choosing the orientation. The only residual sign inputs
are the fixed rational grids/samples. -/
theorem crossed_interior_positive_tail_contradiction
    (z r h a s u : K) (q B : K[X]) (μ : K → K)
    (z0 : 0<z) (zr : z<r) (rh : r<h) (ha : h<a) (as' : a<s) (su : s<u) (u1 : u<1)
    (factor : q=B*((X-C r)*(X-C s)))
    (Bmonic : B.Monic) (Bdegree : B.natDegree=2) (oriented : B.eval 1 ≤ B.eval 0)
    (samples : ∀ y ∈ rationalSamples K, 0 ≤ B.eval (uncenterPoint y))
    (unitGrid : ∀ i : Fin 19, 0 ≤ B.eval (intervalPoint (0:K) 1 i))
    (tailGrid : ∀ i : Fin 19, 0 ≤ B.eval (intervalPoint u 1 i))
    (law : ExactRule (unitMoment q) (fourMarks z h a u) id μ 9)
    (end₁ : integral 0 u (X*q) = 0) (end₂ : integral 0 u (X^2*q) = 0) :
    False := by
  obtain ⟨A,k,pull⟩ := centeredResidual_of_monic_quadratic B Bmonic Bdegree
  obtain ⟨count,freshS,freshR,leftRank,rightRank⟩ := crossed_mark_data z r h a s u zr rh ha as' su
  have ru : r<u := rh.trans (ha.trans (as'.trans su))
  exact crossed_tail_contradiction_with_marks (fourMarks z h a u) z r s u A k q B μ
    count freshS freshR leftRank rightRank (z0.trans (zr.trans ru)) u1 ru su
    factor pull Bmonic.ne_zero (le_of_eq Bdegree) unitGrid tailGrid
    (coeffTests_of_rational_samples A k B pull oriented samples) law end₁ end₂

end
end RKCert.ReviewedNative.CrossedGaussianEndpointBridge
