module

public import RKCert.ReviewedNative.PaidDefectBridge
public import RKCert.ReviewedNative.DiagonalTwin

import Mathlib.Tactic.FieldSimp
import Mathlib.Tactic.Ring

@[expose] public section

namespace RKResearch.Certified.PaidDefectBridge.SDIRK149

open RKResearch RKResearch.FiniteRootedTree
open RKResearch.Certified.Graded (row mergeCoefficient)
open RKResearch.Certified.DiagonalTwin (DiagonalTwins contractMatrix contract_strict_sdirk)
open scoped Matrix

variable {K : Type*} [Field K]

/-- The second live row's single available incoming tap is sufficient precisely
when its required two responses are proportional to the first live evaluation. -/
theorem singleTap {e₀ e₁ r₀ r₁ : K} (he : e₀ ≠ 0)
    (h : r₀ * e₁ - r₁ * e₀ = 0) :
    (r₀ / e₀) * e₀ = r₀ ∧ (r₀ / e₀) * e₁ = r₁ := by
  constructor
  · exact div_mul_cancel₀ r₀ he
  · rw [div_mul_eq_mul_div]
    exact (div_eq_iff he).2 (sub_eq_zero.mp h)

/-- A later live row uses two already chronological independent evaluations. -/
theorem doubleTap {a b c d r s : K} (hdet : a * d - b * c ≠ 0) :
    let x := (d * r - b * s) / (a * d - b * c)
    let y := (a * s - c * r) / (a * d - b * c)
    a * x + b * y = r ∧ c * x + d * y = s := by
  dsimp
  set Δ : K := a * d - b * c with hΔd
  have hΔ : Δ ≠ 0 := hdet
  constructor
  · calc
      a * ((d * r - b * s) / Δ) + b * ((a * s - c * r) / Δ)
          = (a * (d * r - b * s) + b * (a * s - c * r)) / Δ := by
              simp only [div_eq_mul_inv, add_mul, mul_assoc]
      _ = r := (div_eq_iff hΔ).2 (by rw [hΔd]; ring)
  · calc
      c * ((d * r - b * s) / Δ) + d * ((a * s - c * r) / Δ)
          = (c * (d * r - b * s) + d * (a * s - c * r)) / Δ := by
              simp only [div_eq_mul_inv, add_mul, mul_assoc]
      _ = s := (div_eq_iff hΔ).2 (by rw [hΔd]; ring)

/-- The field conversion is needed when taps paid in raw weighted coordinates
are applied to normalized means. -/
theorem raw_to_mean {wi wj a t : K} (hwi : wi ≠ 0) :
    wi * ((wj / wi * a) * t) = a * (wj * t) := by
  field_simp [hwi]

/-- At order nine and a four-grade forward read, the sole longest payment
has a size-five source and three actual exterior letters. The conclusion
ranges over every reviewed ordinary rooted tree, not just clock words. -/
theorem orderNine_of_split_payments [CharZero K]
    (A : Matrix (Fin 6 ⊕ Fin 10) (Fin 6 ⊕ Fin 10) K) (w ξ : Fin 10 → K)
    (hquad : HasQuadratureOrder 9 w ξ)
    (hzero : ∀ t, treeSize t ≤ 4 → primitiveSeed A ξ t = 0)
    (hshort : ∀ (t : FiniteRootedTree) (W : List Letter), 4 < treeSize t →
      W.length + treeSize t < 9 → W.length ≤ 2 →
      row w (wordMap (suffixBlock A) ξ W (primitiveSeed A ξ t)) = 0)
    (htop : ∀ (t : FiniteRootedTree) (W : List Letter), treeSize t = 5 →
      W.length = 3 →
      row w (wordMap (suffixBlock A) ξ W (primitiveSeed A ξ t)) = 0) :
    HasOrder 9 A (Sum.elim (0 : Fin 6 → K) w) := by
  refine hasOrder_of_paid_defect_words (p := 9) (q := 4) A w ξ (by decide) hquad
    (fun t ht _ => hzero t ht) ?_
  intro t W ht hb
  by_cases hs : W.length ≤ 2
  · exact hshort t W ht hb hs
  · exact htop t W (by omega) (by omega)

/-- In the virtual chronology, delete stage 7 into stage 4 and then stage 6
into stage 5 (zero-based). Both exact diagonal-twin hypotheses concern whole
strict rows; the second one is tested after the first literal redirect. -/
theorem contractChronologicalPorts
    (A : Matrix (Fin 16) (Fin 16) K) (b : Fin 16 → K) (γ : K)
    (hA : A.IsLowerTriangular) (hdiag : ∀ k, A k k = γ) (hγ : γ ≠ 0)
    (hov : HasOrder 9 A b)
    (h₁ : DiagonalTwins (7 : Fin 16) (4 : Fin 15) γ A)
    (h₂ : DiagonalTwins (6 : Fin 15) (5 : Fin 14) γ (contractMatrix 7 4 A)) :
    let A₁ := contractMatrix (7 : Fin 16) (4 : Fin 15) A
    let b₁ := mergeCoefficient (7 : Fin 16) (4 : Fin 15) b
    let A₂ := contractMatrix (6 : Fin 15) (5 : Fin 14) A₁
    let b₂ := mergeCoefficient (6 : Fin 15) (5 : Fin 14) b₁
    A₂.IsLowerTriangular ∧ (∀ k, A₂ k k = γ) ∧ γ ≠ 0 ∧ HasOrder 9 A₂ b₂ := by
  have hc₁ : (7 : Fin 16).succAbove (4 : Fin 15) < 7 := by decide
  have hc₂ : (6 : Fin 15).succAbove (5 : Fin 14) < 6 := by decide
  obtain ⟨hlo, hdc, hgc, hoc⟩ := contract_strict_sdirk hc₁ hA hdiag hγ h₁ hov
  exact contract_strict_sdirk hc₂ hlo hdc hgc h₂ hoc

end RKResearch.Certified.PaidDefectBridge.SDIRK149
