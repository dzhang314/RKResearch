module

public import RKCert.ReviewedNative.WeakFiveSoleInnerCornerEnclosure

import Mathlib.Tactic.FieldSimp
import Mathlib.Tactic.Linarith
import Mathlib.Tactic.NormNum
import Mathlib.Tactic.Ring

@[expose] public section

/-! # The actual paid weak-five sextic meets the literal corner cages

Only the published physical exterior scale and the six paid global tests
are consumed. No right-test cap or phase exclusion is assumed or claimed. -/
namespace RKCert.ReviewedNative.WeakFiveSoleInnerUniform

open Polynomial
open RKCert.ReviewedNative.PositiveRule19
open RKCert.ReviewedNative.FiniteGaussianGridPositivity

noncomputable section
variable {K : Type*} [Field K] [LinearOrder K] [IsStrictOrderedRing K]

/-- The actual compact parameter of a negative exterior clock/root. -/
def compactExterior (a : K) : K := -a/(1-a)

private theorem one_sub_pos_of_negative {a : K} (neg : a < 0) : 0 < 1-a :=
  sub_pos.mpr (neg.trans zero_lt_one)

theorem compactExterior_unit {a : K} (neg : a < 0) :
    compactExterior a ∈ Set.Icc (0 : K) 1 := by
  have h := one_sub_pos_of_negative neg
  unfold compactExterior
  refine ⟨(div_pos (neg_pos.mpr neg) h).le,?_⟩
  apply (div_le_iff₀ h).mpr
  simp only [one_mul]
  linarith

private theorem compact_affine {a : K} (neg : a < 0) :
    affineWeight (compactExterior a) = C ((1-a)⁻¹)*(X-C a) := by
  have ha : 1-a≠0 := (one_sub_pos_of_negative neg).ne'
  have e : 1-compactExterior a=(1-a)⁻¹ := by
    unfold compactExterior
    rw [←one_div]
    field_simp [ha] <;> ring
  rw [affineWeight,e,compactExterior]
  simp only [div_eq_mul_inv,map_mul,map_neg]
  ring

theorem compactExterior_ratio {a α : K} (a0 : a < 0) (α0 : α < 0) :
    compactExterior α = normalizedRight (compactExterior a) (α/a) := by
  have ha : 1-a≠0 := (one_sub_pos_of_negative a0).ne'
  have hα : 1-α≠0 := (one_sub_pos_of_negative α0).ne'
  have numerator : (α/a)*compactExterior a = -α/(1-a) := by
    unfold compactExterior
    field_simp [a0.ne,ha] <;> ring
  have denominator : 1-compactExterior a+(α/a)*compactExterior a=(1-α)/(1-a) := by
    rw [numerator,compactExterior]
    field_simp [ha] <;> ring
  rw [normalizedRight,denominator,numerator,compactExterior]
  field_simp [ha,hα] <;> ring

/-- Orthogonality of the actual monic product at its own normalized
density. The only change to the paid globals is a constant factor. -/
theorem compact_orthogonal_of_exterior_globals {a α : K} (a0 : a < 0) (α0 : α < 0)
    {P : K[X]} (paid : ∀ H : K[X], H.natDegree≤5 →
      integral 0 1 (unitWeight K*(X-C a)*(X-C α)*P*H)=0) :
    SixOrthogonal (compactExterior a) (compactExterior α) P := by
  intro H hd
  have e : density (compactExterior a) (compactExterior α)*P*H =
      C ((1-a)⁻¹*(1-α)⁻¹)*(unitWeight K*(X-C a)*(X-C α)*P*H) := by
    rw [density,compact_affine a0,compact_affine α0]
    simp only [map_mul]
    ring
  rw [e,←Polynomial.smul_eq_C_mul,map_smul,paid H hd,smul_zero]

/-- The actual quartic and the three interior weak-five masks give the
literal monic comparison polynomial (R D), with no re-selection or
replacement of its six ordered roots. -/
theorem weakFive_paid_product_cell_cages {a α z h u : K}
    (a0 : a < 0) (α0 : α < 0) (ratioLo : (2 : K)/3≤α/a) (ratioHi : α/a≤(6 : K)/7)
    {q R : K[X]} (factor : q=(X-C α)*R) (mR : R.Monic) (dR : R.natDegree=3)
    (paid : ∀ H : K[X], H.natDegree≤5 →
      integral 0 1 (unitWeight K*(X-C a)*q*((X-C z)*(X-C h)*(X-C u))*H)=0)
    (v : Fin 6 → K) (strict : StrictMono v) (inside : ∀ i, v i ∈ Set.Ioo (0 : K) 1)
    (roots : ∀ i, (R*((X-C z)*(X-C h)*(X-C u))).IsRoot (v i)) :
    ∃ cell : Fin 15, (cellBreaks cell.castSucc : K)/64≤compactExterior a ∧
      compactExterior a≤(cellBreaks cell.succ : K)/64 ∧
      ∀ i : Fin 6, (highCellCorner cell).lowerEndpoint K i < v i ∧
        v i < (lowCellCorner cell).upperEndpoint K i := by
  let D : K[X] := (X-C z)*(X-C h)*(X-C u)
  let P := R*D
  have md : D.Monic := ((monic_X_sub_C z).mul (monic_X_sub_C h)).mul (monic_X_sub_C u)
  have dd : D.natDegree=3 := by
    unfold D
    rw [natDegree_mul ((monic_X_sub_C z).mul (monic_X_sub_C h)).ne_zero (monic_X_sub_C u).ne_zero,
      natDegree_mul (monic_X_sub_C z).ne_zero (monic_X_sub_C h).ne_zero]
    simp only [natDegree_X_sub_C]
  have dp : P.natDegree=6 := by
    unfold P
    rw [natDegree_mul mR.ne_zero md.ne_zero,dR,dd]
  have orth : SixOrthogonal (compactExterior a) (compactExterior α) P := by
    apply compact_orthogonal_of_exterior_globals a0 α0
    intro H hH
    simpa only [factor,P,D,mul_assoc] using paid H hH
  exact exists_actual_cell_cages
    (SixNodes.ofMonic (compactExterior_unit a0) (compactExterior_unit α0) (mR.mul md)
      dp orth v strict inside roots) ratioLo ratioHi (compactExterior_ratio a0 α0)

end
end RKCert.ReviewedNative.WeakFiveSoleInnerUniform
