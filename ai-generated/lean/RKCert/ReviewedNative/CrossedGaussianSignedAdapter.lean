module

public import RKCert.ReviewedNative.FiniteGaussianGridPositivity
public import RKCert.ReviewedNative.CrossedGaussianCheckedMoments
import Lean.Elab.Tactic.Omega
import Mathlib.Tactic.Linarith
import Mathlib.Tactic.NormNum
import Mathlib.Tactic.Ring

@[expose] public section

/-! # Signed degree-nine four-node input to the centered six-node rule

Draft. The only residual positivity used to make positive atomic masses
is on the audited fixed unit grid. Centering is a separate change of
variables, and node rank bounds are purely finite order.
-/
namespace RKCert.ReviewedNative.CrossedGaussianSignedAdapter

open Polynomial
open RKCert.ReviewedNative.PositiveRule19
open RKCert.ReviewedNative.FiniteGaussianNodalLift
open RKCert.ReviewedNative.FiniteGaussianGridPositivity
open RKCert.ReviewedNative.FiniteGaussianLocalizer
open RKCert.ReviewedNative.CrossedGaussianMomentLift
open RKCert.ReviewedNative.CrossedGaussianCheckedMoments
open scoped BigOperators

noncomputable section
variable {K : Type*} [Field K] [LinearOrder K] [IsStrictOrderedRing K]

def unitMoment (B : K[X]) : K[X] →ₗ[K] K :=
  weighted (integral 0 1) (unitWeight K*B)

@[simp] theorem unitMoment_apply (B P : K[X]) :
    unitMoment B P = integral 0 1 ((unitWeight K*B)*P) := rfl

theorem unitMoment_factor (q B H : K[X]) (factor : q=B*H) :
    weighted (unitMoment B) H = unitMoment q := by
  apply LinearMap.ext
  intro P
  simp only [weighted_apply, unitMoment_apply]
  rw [factor]
  apply congrArg (fun F : K[X] => integral 0 1 F)
  ring

def addMarks (old : Finset K) (r s : K) : Finset K := insert r (insert s old)

theorem addMarks_count (old : Finset K) (r s : K)
    (freshS : s ∉ old) (freshR : r ∉ insert s old) :
    (addMarks old r s).card = old.card+2 := by
  unfold addMarks
  rw [Finset.card_insert_of_notMem freshR,Finset.card_insert_of_notMem freshS] <;> omega

/-- Degree-paid four-to-six exactness, prior to any sign assumption. -/
theorem six_exact_of_signed_four (old : Finset K) (r s : K) (q B : K[X])
    (count : old.card=4) (freshS : s ∉ old) (freshR : r ∉ insert s old)
    (factor : q=B*((X-C r)*(X-C s)))
    (μ : K → K) (law : ExactRule (unitMoment q) old id μ 9) :
    ExactRule (unitMoment B) (addMarks old r s) id
      (cardinalMass (unitMoment B) (addMarks old r s) id) 11 := by
  let H : K[X] := (X-C r)*(X-C s)
  have inLaw : ExactRule (weighted (unitMoment B) H) old id μ (2*old.card+1) := by
    rw [unitMoment_factor q B H factor,count]
    exact law
  have nf : Lagrange.nodal (addMarks old r s) id = H*Lagrange.nodal old id :=
    nodal_insert_two old id freshS freshR
  have h := gaussian_exact_of_two_marks inLaw Function.injective_id.injOn
    (addMarks_count old r s freshS freshR) nf
  simpa only [count] using h

/-- A separate positivity consumer for the canonical augmented masses. -/
theorem six_masses_pos (old : Finset K) (r s : K) (B : K[X])
    (count : old.card=4) (freshS : s ∉ old) (freshR : r ∉ insert s old)
    (Bne : B ≠ 0) (Bdeg : B.natDegree ≤ 2)
    (nn : ∀ i : Fin 19, 0 ≤ B.eval (intervalPoint (0:K) 1 i))
    (law : ExactRule (unitMoment B) (addMarks old r s) id
      (cardinalMass (unitMoment B) (addMarks old r s) id) 11)
    {x : K} (hx : x ∈ addMarks old r s) :
    0 < cardinalMass (unitMoment B) (addMarks old r s) id x := by
  have six := addMarks_count old r s freshS freshR
  rw [count] at six
  exact unit_gaussian_mass_pos B Bne Bdeg nn six Function.injective_id.injOn law hx

def centerPoint (x : K) : K := 2*x-1
def uncenterPoint (y : K) : K := (y+1)/2

theorem centerPoint_strictMono : StrictMono (centerPoint : K → K) := by
  intro x y xy
  unfold centerPoint
  linarith only [xy]

theorem uncenter_center (x : K) : uncenterPoint (centerPoint x) = x := by
  unfold uncenterPoint centerPoint
  ring

theorem center_uncenter (y : K) : centerPoint (uncenterPoint y) = y := by
  unfold uncenterPoint centerPoint
  ring

def centerEmbedding (K : Type*) [Field K] [LinearOrder K] [IsStrictOrderedRing K] : K ↪ K :=
  ⟨centerPoint,centerPoint_strictMono.injective⟩

def centerNodes (s : Finset K) : Finset K := s.map (centerEmbedding K)
def centerMass (μ : K → K) (y : K) : K := 24*μ (uncenterPoint y)

private theorem centerEmbedding_apply (x : K) : centerEmbedding K x = centerPoint x := rfl

theorem eval_centerMap (x : K) : (centerMap K).eval x = centerPoint x := by
  simp only [centerMap,centerPoint,eval_mul,eval_sub,eval_C,eval_X,eval_one]

theorem centerMap_degree : (centerMap K).natDegree ≤ 1 := by
  unfold centerMap
  apply (natDegree_sub_le _ _).trans
  exact max_le ((natDegree_C_mul_le _ _).trans (by simp)) (by simp)

theorem centeredResidual_eval_of_pull (A k : K) (B : K[X])
    (pull : (centeredResidual A k).comp (centerMap K) = C (4:K)*B) (y : K) :
    (centeredResidual A k).eval y = 4*B.eval (uncenterPoint y) := by
  have he := congrArg (Polynomial.eval (uncenterPoint y)) pull
  simpa only [eval_comp,eval_centerMap,center_uncenter,eval_mul,eval_C] using he

/-- Every monic quadratic has the residual normalization, before any
orientation or positivity claim about the resulting coefficients. -/
theorem centeredResidual_of_monic_quadratic (B : K[X]) (hM : B.Monic)
    (hD : B.natDegree=2) :
    ∃ A k : K, (centeredResidual A k).comp (centerMap K) = C (4:K)*B := by
  have h₂ : B.coeff 2 = 1 := by simpa only [hD] using hM.coeff_natDegree
  have repr : B = C (B.coeff 0)+C (B.coeff 1)*X+X^2 := by
    calc
      B = ∑ i ∈ Finset.range 3, C (B.coeff i)*X^i :=
        B.as_sum_range_C_mul_X_pow' (by omega)
      _ = C (B.coeff 0)+C (B.coeff 1)*X+X^2 := by
        simp [Finset.sum_range_succ,h₂]
  refine ⟨4*B.coeff 0+1+2*B.coeff 1,-2-2*B.coeff 1,?_⟩
  conv_rhs => rw [repr]
  simp only [centeredResidual,centerMap,add_comp,sub_comp,mul_comp,pow_comp,C_comp,
    X_comp,one_comp,neg_comp,ofNat_comp,map_add,map_sub,map_mul,map_neg,C_1]
  norm_num [C_ofNat] <;> ring

/-- The exact pullback of the quadratic residual rescales the masses by
24 and sends each node x to 2x−1. The degree cutoff does not increase. -/
theorem centered_exact_of_unit_rule {s : Finset K} {μ : K → K}
    (B : K[X]) (A k : K)
    (pull : (centeredResidual A k).comp (centerMap K) = C (4:K)*B)
    (law : ExactRule (unitMoment B) s id μ 11) :
    CenteredExact (centerRef K) (centerNodes s) (centerMass μ) A k := by
  intro P pd
  let Q := P.comp (centerMap K)
  have qd : Q.natDegree ≤ 11 :=
    natDegree_comp_le.trans (by simpa only [Nat.mul_one] using
      (Nat.mul_le_mul pd (centerMap_degree (K := K))))
  have hp :
      X*(1-X)*((centeredResidual A k*P).comp (centerMap K)) =
        C (4:K)*((unitWeight K*B)*Q) := by
    simp only [mul_comp,pull,Q,unitWeight]
    ring
  calc
    centerRef K (centeredResidual A k*P) =
        24*unitMoment B Q := by
      rw [centerRef_pullback,hp,moment_C_mul,unitMoment_apply]
      ring
    _ = ∑ y ∈ centerNodes s, centerMass μ y * P.eval y := by
      rw [law Q qd,centerNodes,Finset.sum_map,Finset.mul_sum]
      apply Finset.sum_congr rfl
      intro x _
      simp only [Q,id_eq,eval_comp,eval_centerMap,centerEmbedding_apply,
        centerMass,uncenter_center,mul_assoc]

theorem centerMass_pos_of_unit {s : Finset K} {μ : K → K}
    (positive : ∀ x ∈ s, 0 < μ x) :
    ∀ y ∈ centerNodes s, 0 < centerMass μ y := by
  intro y hy
  obtain ⟨x,hx,rfl⟩ := Finset.mem_map.mp hy
  unfold centerMass
  rw [centerEmbedding_apply,uncenter_center]
  exact mul_pos (by norm_num) (positive x hx)

/-- Finite order: if at most one original mark lies below r, two
centered nodes below a cut force the centered r below that cut. -/
theorem centered_second_exit {s : Finset K} (z r : K)
    (only : ∀ x ∈ s, x<r → x=z) (d : K)
    (two : 2 ≤ ((centerNodes s).filter (fun y => y<d)).card) :
    centerPoint r<d := by
  by_contra h
  have dr : d ≤ centerPoint r := le_of_not_gt h
  have each (y : K) (hy : y ∈ (centerNodes s).filter (fun y => y<d)) :
      y = centerPoint z := by
    obtain ⟨x,hx,xeq⟩ := Finset.mem_map.mp (Finset.mem_filter.mp hy).1
    have hxy : centerPoint x < centerPoint r := by
      rw [← xeq] at hy
      exact ((Finset.mem_filter.mp hy).2).trans_le dr
    have xr : x<r := lt_of_not_ge fun hr => not_lt_of_ge (centerPoint_strictMono.monotone hr) hxy
    rw [← xeq,centerEmbedding_apply,only x hx xr]
  have one : ((centerNodes s).filter (fun y => y<d)).card ≤ 1 :=
    Finset.card_le_one.mpr fun i hi j hj => (each i hi).trans (each j hj).symm
  omega

/-- Reflection of the finite order exit for the penultimate node. -/
theorem centered_penultimate_exit {s : Finset K} (p u : K)
    (only : ∀ x ∈ s, p<x → x=u) (e : K)
    (two : 2 ≤ ((centerNodes s).filter (fun y => e<y)).card) :
    e<centerPoint p := by
  by_contra h
  have pe : centerPoint p ≤ e := le_of_not_gt h
  have each (y : K) (hy : y ∈ (centerNodes s).filter (fun y => e<y)) :
      y = centerPoint u := by
    obtain ⟨x,hx,xeq⟩ := Finset.mem_map.mp (Finset.mem_filter.mp hy).1
    have hxy : centerPoint p < centerPoint x := by
      rw [← xeq] at hy
      exact pe.trans_lt ((Finset.mem_filter.mp hy).2)
    have px : p<x := lt_of_not_ge fun hp => not_lt_of_ge (centerPoint_strictMono.monotone hp) hxy
    rw [← xeq,centerEmbedding_apply,only x hx px]
  have one : ((centerNodes s).filter (fun y => e<y)).card ≤ 1 :=
    Finset.card_le_one.mpr fun i hi j hj => (each i hi).trans (each j hj).symm
  omega

end
end RKCert.ReviewedNative.CrossedGaussianSignedAdapter
