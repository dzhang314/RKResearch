module

public import RKCert.ReviewedNative.PaidDefectBridge
public import RKCert.ReviewedNative.DiagonalTwin

import Mathlib.Tactic.FieldSimp
import Mathlib.Tactic.Ring

@[expose] public section

namespace RKResearch.Certified.PaidDefectBridge.SDIRK9TriplePort

open RKResearch RKResearch.FiniteRootedTree
open RKResearch.Certified.Graded (row mergeCoefficient)
open RKResearch.Certified.DiagonalTwin (DiagonalTwins contractMatrix contract_strict_sdirk)
open scoped Matrix

section Shape

variable {K : Type*} [CommRing K]

/-- The primitive shape has double zeros at both old protected ports. -/
def portPrimitive (v w x : K) : K := x * (x - v)^2 * (x - w)^2

/-- Explicit derivative shape; the field-level arithmetic supplies this
polynomial to the rank-one decoder update. -/
def portShape (v w x : K) : K :=
  (x - v)^2 * (x - w)^2 + 2 * x * (x - v) * (x - w)^2 +
    2 * x * (x - v)^2 * (x - w)

def thirdGate (v w x : K) : K :=
  x^3 - (v + w + 5) * x^2 + (v * w + 3 * (v + w)) * x - v * w

theorem factor_shifted_primitive (v w x : K) :
    portPrimitive v w x - portShape v w x =
      (x - v) * (x - w) * thirdGate v w x := by
  dsimp [portPrimitive, portShape, thirdGate]
  ring

theorem oldPort_shape (v w : K) :
    portShape v w v = 0 ∧ portShape v w w = 0 ∧
    portPrimitive v w v = 0 ∧ portPrimitive v w w = 0 := by
  simp [portShape, portPrimitive]

end Shape

section Read

variable {K : Type*} [Field K]
variable {V P : Type*} [AddCommGroup V] [Module K V] [AddCommGroup P] [Module K P]

/-- The new response is an actual specific coordinate minus its old decoder
evaluation. This update is exact wherever that contrast vanishes. -/
def extendRead (D : V →ₗ[K] P) (χ : V →ₗ[K] K) (shape : P) : V →ₗ[K] P :=
  D + χ.smulRight shape

theorem retain_read (D : V →ₗ[K] P) (χ : V →ₗ[K] K)
    (shape : P) (E : P →ₗ[K] K) (h : E shape = 0) :
    E.comp (extendRead D χ shape) = E.comp D := by
  ext x
  simp [extendRead, h]

theorem install_read (D : V →ₗ[K] P) (e : V →ₗ[K] K)
    (shape : P) (E : P →ₗ[K] K) (h : E shape = 1) :
    E.comp (extendRead D (e - E.comp D) shape) = e := by
  ext x
  simp only [LinearMap.comp_apply, extendRead, LinearMap.add_apply, map_add,
    LinearMap.smulRight_apply, LinearMap.sub_apply, map_smul, smul_eq_mul, h, mul_one]
  ring

end Read

variable {K : Type*} [Field K]

/-- Typed ordinary order-eight completion with a size-four forward return and
the special two-letter top gate. All physical trees are covered. -/
theorem orderEight_of_split_payments [CharZero K]
    (A : Matrix (Fin 7 ⊕ Fin 9) (Fin 7 ⊕ Fin 9) K) (w ξ : Fin 9 → K)
    (hquad : HasQuadratureOrder 8 w ξ)
    (hzero : ∀ t, treeSize t ≤ 4 → primitiveSeed A ξ t = 0)
    (hshort : ∀ (t : FiniteRootedTree) (W : List Letter), 4 < treeSize t →
      W.length + treeSize t < 8 → W.length ≤ 1 →
      row w (wordMap (suffixBlock A) ξ W (primitiveSeed A ξ t)) = 0)
    (htop : ∀ (t : FiniteRootedTree) (W : List Letter), treeSize t = 5 →
      W.length = 2 →
      row w (wordMap (suffixBlock A) ξ W (primitiveSeed A ξ t)) = 0) :
    HasOrder 8 A (Sum.elim (0 : Fin 7 → K) w) := by
  refine hasOrder_of_paid_defect_words (p := 8) (q := 4) A w ξ (by decide) hquad
    (fun t ht _ => hzero t ht) ?_
  intro t W ht hb
  by_cases hs : W.length ≤ 1
  · exact hshort t W ht hb hs
  · exact htop t W (by omega) (by omega)

/-- Delete virtual v, w, z in reverse virtual chronology, keeping every
strict coefficient and its output share via the exact diagonal-twin law. -/
theorem contractThreePorts
    (A : Matrix (Fin 16) (Fin 16) K) (b : Fin 16 → K) (γ : K)
    (hA : A.IsLowerTriangular) (hdiag : ∀ k, A k k = γ) (hγ : γ ≠ 0)
    (hov : HasOrder 8 A b)
    (h₁ : DiagonalTwins (9 : Fin 16) (4 : Fin 15) γ A)
    (h₂ : DiagonalTwins (8 : Fin 15) (5 : Fin 14) γ (contractMatrix 9 4 A))
    (h₃ : DiagonalTwins (7 : Fin 14) (6 : Fin 13) γ
      (contractMatrix 8 5 (contractMatrix 9 4 A))) :
    let A₁ := contractMatrix (9 : Fin 16) (4 : Fin 15) A
    let b₁ := mergeCoefficient (9 : Fin 16) (4 : Fin 15) b
    let A₂ := contractMatrix (8 : Fin 15) (5 : Fin 14) A₁
    let b₂ := mergeCoefficient (8 : Fin 15) (5 : Fin 14) b₁
    let A₃ := contractMatrix (7 : Fin 14) (6 : Fin 13) A₂
    let b₃ := mergeCoefficient (7 : Fin 14) (6 : Fin 13) b₂
    A₃.IsLowerTriangular ∧ (∀ k, A₃ k k = γ) ∧ γ ≠ 0 ∧ HasOrder 8 A₃ b₃ := by
  have hc₁ : (9 : Fin 16).succAbove (4 : Fin 15) < 9 := by decide
  have hc₂ : (8 : Fin 15).succAbove (5 : Fin 14) < 8 := by decide
  have hc₃ : (7 : Fin 14).succAbove (6 : Fin 13) < 7 := by decide
  obtain ⟨hlo, hdc, hgc, hoc⟩ := contract_strict_sdirk hc₁ hA hdiag hγ h₁ hov
  obtain ⟨hl₂, hd₂, hg₂, ho₂⟩ := contract_strict_sdirk hc₂ hlo hdc hgc h₂ hoc
  exact contract_strict_sdirk hc₃ hl₂ hd₂ hg₂ h₃ ho₂

end RKResearch.Certified.PaidDefectBridge.SDIRK9TriplePort
