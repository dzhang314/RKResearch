module

public import RKCert.ReviewedNative.SDIRK118ScalarQuadrature

import Mathlib.Tactic.FinCases
import Mathlib.Tactic.Ring
import Lean.Elab.Tactic.Omega

@[expose] public section

noncomputable section

namespace RKResearch.Certified.PaidDefectBridge.SDIRK118.ScalarMasses

open RKResearch
open RKResearch.Certified.PaidDefectBridge.SDIRK118 (PolyBound)
open RKResearch.Certified.PaidDefectBridge.SDIRK118.ClaimPin
open RKResearch.Certified.PaidDefectBridge.SDIRK118.ScalarBindings
open RKResearch.Certified.PaidDefectBridge.SDIRK118.ScalarQuadrature
open Polynomial
open scoped Matrix Polynomial BigOperators

local notation "ℙ" => Polynomial ℝ

theorem beta_factor (M : MonomialBasis) (s t c : ℝ) (hc : quadraticAt M s t c = 0) :
    Bstar M s t = linearFactor (bStar M s t c) * linearFactor c := by
  apply Polynomial.funext
  intro X0
  simpa only [Bstar, quadraticAt, linearFactor, eval_add, eval_mul, Polynomial.eval_pow,
    eval_X, eval_C, eval_sub] using quadratic_factors M s t c hc X0

theorem raw_rule_exact7 (M : MonomialBasis) (hm : standardPowers M)
    (s t c : ℝ) (h : ExactScalarSeed M s t c) (P : ℙ) (hp : PolyBound 7 P) :
    weightedEval (scalarWeights M (yAt M s t c)) (rawNodes M s t c) P =
      avg M (zAt s) P := by
  let z := zAt s
  let y := yAt M s t c
  let u := rawNodes M s t c
  let W := scalarWeights M y
  have hz := (literal_z_pos M s t c h).ne'
  have sz : (z • (X : ℙ)).natDegree ≤ 1 := by
    simpa only [natDegree_X] using natDegree_smul_le z (X : ℙ)
  have hp' : PolyBound 7 (P.comp (z • X)) := by
    apply natDegree_le_iff_coeff_eq_zero.mp
    calc
      _ ≤ P.natDegree * (z • (X : ℙ)).natDegree := natDegree_comp_le
      _ ≤ 7 * 1 := Nat.mul_le_mul (natDegree_le_iff_coeff_eq_zero.mpr hp) sz
      _ = 7 := rfl
  have he := (literal_rule_exact7 M hm s t c h _ hp').trans (mean_scale M hm z hz P)
  change weightedEval W y (P.comp (z • X)) = avg M z P at he
  have clock (i : Fin 6) : (P.comp (z • X)).eval (y i) = P.eval (u i) := by
    rw [eval_comp, Polynomial.eval_smul, eval_X, smul_eq_mul]
    change P.eval (z * yAt M s t c i) = P.eval (rawNodes M s t c i)
    rw [norm_nodes, mul_comm z, div_mul_cancel₀ _ hz]
  simpa only [weightedEval_apply, clock] using he

def oldSite (i : Fin 4) : Fin 6 := ⟨i.val, by have h := i.isLt; omega⟩

theorem raw_at_old (M : MonomialBasis) (s t c : ℝ) (i : Fin 4) :
    rawNodes M s t c (oldSite i) = uAt s t i := by fin_cases i <;> rfl

private theorem old_mass (M : MonomialBasis) (hm : standardPowers M)
    (s t c : ℝ) (h : ExactScalarSeed M s t c) (i : Fin 4) :
    scalarWeights M (yAt M s t c) (oldSite i) ≠ 0 := by
  let u := rawNodes M s t c
  let W := scalarWeights M (yAt M s t c)
  let S := ∏ j ∈ Finset.univ.erase i, linearFactor (uAt s t j)
  let P := Bstar M s t * S
  have hB := beta_factor M s t c h.cRoot
  have dB : (Bstar M s t).natDegree ≤ 2 := by
    rw [hB]
    exact natDegree_mul_le.trans (by simp [linearFactor, natDegree_X_sub_C])
  have dS : S.natDegree ≤ 4 := by
    change (Lagrange.nodal (Finset.univ.erase i) (uAt s t)).natDegree ≤ 4
    rw [Lagrange.natDegree_nodal]
    calc
      _ ≤ (Finset.univ : Finset (Fin 4)).card := Finset.card_le_card (Finset.erase_subset i _)
      _ = 4 := by simp
  have dp : PolyBound 7 P :=
    natDegree_le_iff_coeff_eq_zero.mp (natDegree_mul_le.trans (by omega))
  have hz (j : Fin 6) (hj : j ≠ oldSite i) : P.eval (u j) = 0 := by
    by_cases hx : j.val < 4
    · let k : Fin 4 := ⟨j.val,hx⟩
      have ej : oldSite k = j := Fin.ext rfl
      have hki : k ≠ i := fun e => hj (ej.symm.trans (congrArg oldSite e))
      have hz : S.eval (uAt s t k) = 0 := by
        change (Lagrange.nodal (Finset.univ.erase i) (uAt s t)).eval (uAt s t k) = 0
        exact Lagrange.eval_nodal_at_node (Finset.mem_erase.mpr ⟨hki, Finset.mem_univ k⟩)
      change (Bstar M s t * S).eval (rawNodes M s t c j) = 0
      rw [←ej, raw_at_old, eval_mul, hz, mul_zero]
    · have hsplit : j = (4 : Fin 6) ∨ j = (5 : Fin 6) := by
        have hj := j.isLt
        have hv : j.val = 4 ∨ j.val = 5 := by omega
        rcases hv with hv | hv
        · exact Or.inl (Fin.ext hv)
        · exact Or.inr (Fin.ext hv)
      rcases hsplit with rfl | rfl
      · change (Bstar M s t * S).eval (bStar M s t c) = 0
        rw [hB]
        simp [linearFactor, eval_mul, eval_sub]
      · change (Bstar M s t * S).eval c = 0
        rw [hB]
        simp [linearFactor, eval_mul, eval_sub]
  have pay := raw_rule_exact7 M hm s t c h P dp
  change weightedEval W u P = omegaOld M s t i at pay
  rw [weightedEval_apply, Finset.sum_eq_single (oldSite i)] at pay
  · intro hw
    change W (oldSite i) = 0 at hw
    rw [hw, zero_mul] at pay
    exact h.omegaNe i pay.symm
  · intro j _ hj
    rw [hz j hj, mul_zero]
  · simp

private theorem exterior_moment (M : MonomialBasis) (hm : standardPowers M)
    (s t c : ℝ) (h : ExactScalarSeed M s t c) (j : ℕ) (hj : j ≤ 2) :
    let W := scalarWeights M (yAt M s t c)
    let b := bStar M s t c
    μ M s t j =
      W 4 * (Zpoly s t).eval b * b ^ j + W 5 * (Zpoly s t).eval c * c ^ j := by
  let W := scalarWeights M (yAt M s t c)
  let P := X ^ j * Zpoly s t
  have dZ : (Zpoly s t).natDegree ≤ 4 := by
    have lin (x : ℝ) : (linearFactor x).natDegree ≤ 1 := by simp [linearFactor]
    have d₂ : (linearFactor s * linearFactor t).natDegree ≤ 2 :=
      natDegree_mul_le_of_le (lin s) (lin t)
    have d₃ : (linearFactor s * linearFactor t * linearFactor (1 : ℝ)).natDegree ≤ 3 :=
      natDegree_mul_le_of_le d₂ (lin 1)
    change (linearFactor (aAt s) * (linearFactor s * linearFactor t * linearFactor (1 : ℝ))).natDegree ≤ 4
    exact natDegree_mul_le_of_le (lin (aAt s)) d₃
  have dp : PolyBound 7 P := by
    apply natDegree_le_iff_coeff_eq_zero.mp
    exact natDegree_mul_le.trans (by rw [natDegree_X_pow]; omega)
  have e := (raw_rule_exact7 M hm s t c h P dp).symm
  change μ M s t j = weightedEval W (rawNodes M s t c) P at e
  simpa [weightedEval_apply, P, rawNodes, Fin.sum_univ_succ, eval_mul, Polynomial.eval_pow,
    eval_X, Zpoly, Jpoly, cubic, linearFactor, eval_sub, mul_assoc, mul_left_comm, mul_comm] using e

theorem exterior_det (M : MonomialBasis) (hm : standardPowers M)
    (s t c : ℝ) (h : ExactScalarSeed M s t c) :
    let W := scalarWeights M (yAt M s t c)
    let b := bStar M s t c
    momentDet M s t =
      W 4 * W 5 * (Zpoly s t).eval b * (Zpoly s t).eval c * (c - b) ^ 2 := by
  dsimp only
  rw [momentDet, exterior_moment M hm s t c h 0 (by decide),
    exterior_moment M hm s t c h 1 (by decide),
    exterior_moment M hm s t c h 2 (by decide)]
  ring

/-- The four old guards apply to their actual nonzero cardinal numerators.
The two exterior masses follow from the nonzero exact moment determinant. -/
theorem literal_mass_nonzero (M : MonomialBasis) (hm : standardPowers M)
    (s t c : ℝ) (h : ExactScalarSeed M s t c) :
    ∀ i, (geometry M s t c).W i ≠ 0 := by
  let W := scalarWeights M (yAt M s t c)
  have det := exterior_det M hm s t c h
  change momentDet M s t =
    W 4 * W 5 * (Zpoly s t).eval (bStar M s t c) * (Zpoly s t).eval c *
      (c - bStar M s t c) ^ 2 at det
  have e4 : W 4 ≠ 0 := by
    intro hz
    simp only [hz, zero_mul] at det
    exact h.momentPivotPos.ne' det
  have e5 : W 5 ≠ 0 := by
    intro hz
    simp only [hz, mul_zero, zero_mul] at det
    exact h.momentPivotPos.ne' det
  intro i
  change W i ≠ 0
  fin_cases i
  · exact old_mass M hm s t c h 0
  · exact old_mass M hm s t c h 1
  · exact old_mass M hm s t c h 2
  · exact old_mass M hm s t c h 3
  · exact e4
  · exact e5

end RKResearch.Certified.PaidDefectBridge.SDIRK118.ScalarMasses
