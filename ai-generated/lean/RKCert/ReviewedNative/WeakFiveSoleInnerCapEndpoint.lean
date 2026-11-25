module

public import RKCert.ReviewedNative.WeakFiveSoleInnerCapCages
public import RKCert.ReviewedNative.WeakFiveSoleInnerPaidNodeEnclosure

import Mathlib.Tactic.FieldSimp
import Mathlib.Tactic.NormNum
import Mathlib.Tactic.Ring

@[expose] public section

/-! # Direct cap contradiction for each genuine SoleInner phase

No chronology is assumed to follow from the classifier automatically.
This consumer preserves the same monic quartic, literal exterior root,
original three unit clocks, and actual six sorted product roots. -/
namespace RKCert.ReviewedNative.WeakFiveSoleInnerUniform

open Polynomial
open RKCert.ReviewedNative.PositiveRule19
open RKCert.ReviewedNative.FiniteGaussianGridPositivity

noncomputable section
variable {K : Type*} [Field K] [LinearOrder K] [IsStrictOrderedRing K]

def Phase.rightWeight (p : Phase) (z : K) : K[X] :=
  match p with
  | .A => (1-X)*(X-C z)
  | .B => (1-X)^2

theorem right_phase_zero (p : Phase) {q : K[X]} {z : K}
    (m1 : integral z 1 ((1-X)*q)=0) (m2 : integral z 1 ((1-X)^2*q)=0) :
    integral z 1 (p.rightWeight z*q)=0 := by
  cases p
  · have e : (1-X)*(X-C z)*q = C (1-z)*((1-X)*q)-(1-X)^2*q := by
      simp only [map_sub,map_one]
      ring
    change integral z 1 ((1-X)*(X-C z)*q)=0
    rw [e,map_sub,←Polynomial.smul_eq_C_mul,map_smul,m1,m2,smul_zero,sub_zero]
  · exact m2

private def tailGamma (z e : K) : K := (1-compactExterior e)*(1-z)

private theorem root_affine_comp {z x : K} (z1 : z < 1) :
    (X-C x).comp (C (1-z)*X+C z) = C (1-z)*(X+C (rootShift z x)) := by
  have he : (1-z)*rootShift z x=z-x := by
    unfold rootShift
    rw [mul_comm,div_mul_cancel₀ _ (sub_pos.mpr z1).ne']
  have rootC : C (1-z)*C (rootShift z x)=C z-C x := by
    calc
      _ = C ((1-z)*rootShift z x) := by rw [map_mul]
      _ = _ := by rw [he,map_sub]
  simp only [sub_comp,X_comp,C_comp,mul_add,rootC]
  ring

private theorem exterior_affine_comp {z e : K} (e0 : e < 0) :
    (X-C e).comp (C (1-z)*X+C z) = C (1-e)*gammaPolynomial (tailGamma z e) := by
  have den : 1-e≠0 := (sub_pos.mpr (e0.trans zero_lt_one)).ne'
  have hg : (1-e)*tailGamma z e=1-z := by
    unfold tailGamma compactExterior
    field_simp [den] <;> ring
  have hd : (1-e)*(1-tailGamma z e)=z-e := by
    calc
      _ = (1-e)-(1-e)*tailGamma z e := by ring
      _ = _ := by rw [hg]; ring
  have constC : C (1-e)*C (1-tailGamma z e)=C z-C e := by
    calc
      _ = C ((1-e)*(1-tailGamma z e)) := by rw [map_mul]
      _ = _ := by rw [hd,map_sub]
  have linC : C (1-e)*C (tailGamma z e)=C (1-z) := by
    calc
      _ = C ((1-e)*tailGamma z e) := by rw [map_mul]
      _ = _ := by rw [hg]
  simp only [sub_comp,X_comp,C_comp,gammaPolynomial,mul_add,←mul_assoc,constC,linC]
  ring

private theorem right_weight_affine (p : Phase) (z : K) :
    (p.rightWeight z).comp (C (1-z)*X+C z) = C ((1-z)^2)*p.weight := by
  cases p <;> simp only [Phase.rightWeight,Phase.weight,unitWeight,mul_comp,sub_comp,pow_comp,
    one_comp,C_comp,X_comp,map_pow,map_sub,map_one] <;> ring

/-- The normalized right test has the exact positive prefactor
((1-e)(1-z)^6), including the Jacobian of the oriented primitive. -/
theorem right_phase_scaling (p : Phase) {z e x₀ x₁ x₂ : K} (z1 : z < 1) (e0 : e < 0) :
    integral z 1 (p.rightWeight z*((X-C e)*((X-C x₀)*(X-C x₁)*(X-C x₂)))) =
      ((1-e)*(1-z)^6)*signedTest p ((1-compactExterior e)*(1-z))
        (rootShift z x₀) (rootShift z x₁) (rootShift z x₂) := by
  rw [integral_affine]
  have shape : (p.rightWeight z*((X-C e)*((X-C x₀)*(X-C x₁)*(X-C x₂)))).comp
      (C (1-z)*X+C z) =
      C ((1-e)*(1-z)^5)*(p.weight*gammaPolynomial (tailGamma z e)*
        ((X+C (rootShift z x₀))*(X+C (rootShift z x₁))*(X+C (rootShift z x₂)))) := by
    rw [mul_comp,right_weight_affine]
    simp only [mul_comp]
    rw [exterior_affine_comp e0]
    simp only [root_affine_comp z1,map_mul,map_pow]
    ring
  rw [shape,←Polynomial.smul_eq_C_mul,map_smul,smul_eq_mul,test_eq_integral]
  unfold tailGamma
  ring

/-- Exact consumption of either alternating layout, with phase index
identities for the actual right mark and the three actual quartic roots. -/
theorem no_paid_sole_inner_phase (p : Phase) {a e u h z : K} {q R : K[X]}
    (a0 : a < 0) (e0 : e < 0) (z1 : z < 1)
    (ratioLo : (2 : K)/3≤e/a) (ratioHi : e/a≤(6 : K)/7)
    (factor : q=(X-C e)*R) (mR : R.Monic) (dR : R.natDegree=3)
    (paid : ∀ H : K[X], H.natDegree≤5 →
      integral 0 1 (unitWeight K*(X-C a)*q*((X-C z)*(X-C h)*(X-C u))*H)=0)
    (m1 : integral z 1 ((1-X)*q)=0) (m2 : integral z 1 ((1-X)^2*q)=0)
    (v : Fin 6 → K) (strict : StrictMono v) (inside : ∀ i, v i ∈ Set.Ioo (0 : K) 1)
    (roots : ∀ i, (R*((X-C z)*(X-C h)*(X-C u))).IsRoot (v i))
    (zIndex : v p.zIndex=z)
    (rootIndices : R=(X-C (v (p.rootIndex 0)))*(X-C (v (p.rootIndex 1)))*
        (X-C (v (p.rootIndex 2)))) : False := by
  obtain ⟨cell,lo,hi,cage⟩ := weakFive_paid_product_cell_cages a0 e0 ratioLo ratioHi
    factor mR dR paid v strict inside roots
  have neg := compact_cell_cap p cell v (compactExterior_unit a0) lo hi ratioLo ratioHi
    (compactExterior_ratio a0 e0) cage
  rw [zIndex] at neg
  have eq := right_phase_zero p m1 m2
  rw [factor,rootIndices,right_phase_scaling p z1 e0] at eq
  have scale : 0 < (1-e)*(1-z)^6 :=
    mul_pos (sub_pos.mpr (e0.trans zero_lt_one)) (pow_pos (sub_pos.mpr z1) _)
  exact (mul_neg_of_pos_of_neg scale neg).ne eq

end
end RKCert.ReviewedNative.WeakFiveSoleInnerUniform
