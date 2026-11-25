module

public import RKCert.ReviewedNative.SDIRK118SubfieldBasic

import Mathlib.Tactic.FinCases

@[expose] public section

noncomputable section

namespace RKResearch.Certified.PaidDefectBridge.SDIRK118.Subfield

open LiteralAssembly
open RKResearch.Certified.DiagonalTwin (contractMatrix)
open RKResearch.Certified.Graded (mat mergeCoefficient)
open scoped BigOperators Matrix

variable (F : IntermediateField ℚ ℝ)

/-- Closure data for a geometry, independent of how its parameters are supplied.
No equation, nonvanishing fact, or tree order is included. -/
structure GeometryIn (g : Geometry ℝ) : Prop where
  G : MatIn F g.G
  R : MatIn F g.R
  W : VecIn F g.W
  gamma : g.γ ∈ F
  Ex : ∀ P, CoeffsIn F P → VecIn F (g.Ex P)
  Ey : ∀ P, CoeffsIn F P → VecIn F (g.Ey P)
  primitive : ∀ P, CoeffsIn F P → CoeffsIn F (g.I P)
  forward : ∀ v, VecIn F v → CoeffsIn F (g.Projf v)
  reverse : ∀ v, VecIn F v → CoeffsIn F (g.Projr v)
  HF : ∀ i, CoeffsIn F (g.HF i)
  KR : ∀ i, CoeffsIn F (g.KR i)

theorem splitMass_mem {W : Vec 6 ℝ} (hW : VecIn F W) : VecIn F (splitMass W) := by
  have h2 : (2 : ℝ) ∈ F := ofNat_mem F 2
  intro i
  fin_cases i
  · exact F.div_mem (hW 1) h2
  · exact hW 5
  · exact hW 4
  · exact F.div_mem (hW 0) h2
  · exact hW 3
  · exact hW 2
  · exact F.div_mem (hW 1) h2
  · exact F.div_mem (hW 0) h2

private theorem aggregate_mem {v : Vec 8 ℝ} (hv : VecIn F v) :
    VecIn F (LiteralAssembly.C v) := by
  have hhalf : (1 / 2 : ℝ) ∈ F := F.div_mem F.one_mem (ofNat_mem F 2)
  intro i
  fin_cases i
  · exact F.mul_mem hhalf (F.add_mem (hv 3) (hv 7))
  · exact F.mul_mem hhalf (F.add_mem (hv 0) (hv 6))
  · exact hv 5
  · exact hv 4
  · exact hv 2
  · exact hv 1

private theorem tap_mem {v : Vec 6 ℝ} (hv : VecIn F v) {γ a b c : ℝ}
    (hγ : γ ∈ F) (ha : a ∈ F) (hb : b ∈ F) (hc : c ∈ F) :
    VecIn F (LiteralAssembly.S γ a b c v) := by
  intro i
  fin_cases i
  · exact F.mul_mem hγ (hv 0)
  · exact F.mul_mem hγ (hv 1)
  · exact F.mul_mem hγ (hv 2)
  · exact F.mul_mem hγ (hv 3)
  · exact F.add_mem (F.mul_mem hγ (hv 4)) (F.mul_mem ha (hv 0))
  · exact F.add_mem (F.add_mem (F.mul_mem hγ (hv 5)) (F.mul_mem hb (hv 0)))
      (F.mul_mem hc (hv 4))

namespace GeometryIn

variable {F} {g : Geometry ℝ}

theorem pairing_mem (h : GeometryIn F g) {H J : Polynomial ℝ}
    (hH : CoeffsIn F H) (hJ : CoeffsIn F J) : g.pairing H J ∈ F := by
  have h1 := h.Ex H hH
  have h2 := h.Ey _ (h.primitive J hJ)
  have h3 := vec_smul F h.gamma (h.Ey J hJ)
  change (∑ i : Fin 6, g.W i * (g.Ex H) i *
    (g.Ey (g.I J) - g.γ • g.Ey J) i) ∈ F
  exact F.sum_mem fun i _ => F.mul_mem (F.mul_mem (h.W i) (h1 i)) (vec_sub F h2 h3 i)

theorem U_mem (h : GeometryIn F g) {v : Vec 8 ℝ} (hv : VecIn F v) :
    VecIn F (g.U v) := by
  let P := g.Projr (pull oldIx v)
  have hP : CoeffsIn F P := h.reverse _ (pull_mem F oldIx hv)
  have ha : g.t40 ∈ F := F.div_mem (h.pairing_mem (h.HF 0) (h.KR 0)) (h.W 4)
  have hb : g.t50 ∈ F := F.div_mem (h.pairing_mem (h.HF 1) (h.KR 0)) (h.W 5)
  have hc : g.t54 ∈ F := F.div_mem (h.pairing_mem (h.HF 1) (h.KR 1)) (h.W 5)
  change VecIn F (g.Ey (g.I P) +
    LiteralAssembly.S g.γ g.t40 g.t50 g.t54 (LiteralAssembly.C v - g.Ey P))
  exact vec_add F (h.Ey _ (h.primitive P hP))
    (tap_mem F (vec_sub F (aggregate_mem F hv) (h.Ey P hP)) h.gamma ha hb hc)

theorem L_mem (h : GeometryIn F g) : MatIn F g.L := by
  change MatIn F (matrixOf (revRows g.R g.U))
  apply matrixOf_mem F
  intro v hv
  have hO : VecIn F (mat g.R (pull oldIx v)) :=
    mulVec_mem F h.R (pull_mem F oldIx hv)
  have hU := h.U_mem hv
  have h2 : (2 : ℝ) ∈ F := ofNat_mem F 2
  intro i
  fin_cases i
  · exact F.sub_mem (F.mul_mem h2 (hU 1)) (hO 1)
  · exact hU 5
  · exact hU 4
  · exact F.sub_mem (F.mul_mem h2 (hU 0)) (hO 0)
  · exact hO 3
  · exact hO 2
  · exact hO 1
  · exact hO 0

theorem T_mem (h : GeometryIn F g) : MatIn F g.T := by
  intro i j
  have hw := splitMass_mem F h.W
  change (splitMass g.W j / splitMass g.W i) * g.L j i ∈ F
  exact F.mul_mem (F.div_mem (hw j) (hw i)) (h.L_mem j i)

theorem D_mem (h : GeometryIn F g) : MatIn F g.D := by
  change MatIn F (matrixOf (crossOperator g.T g.Ex g.I g.Projf))
  apply matrixOf_mem F
  intro v hv
  let P := g.Projf v
  have hP : CoeffsIn F P := h.forward v hv
  change VecIn F (pull site (g.Ex (g.I P)) - g.T *ᵥ pull site (g.Ex P))
  exact vec_sub F (pull_mem F site (h.Ex _ (h.primitive P hP)))
    (mulVec_mem F h.T_mem (pull_mem F site (h.Ex P hP)))

theorem A_mem (h : GeometryIn F g) : MatIn F g.A := by
  intro i j
  cases i with
  | inl i =>
    cases j with
    | inl j => exact h.G i j
    | inr _ => exact F.zero_mem
  | inr i =>
    cases j with
    | inl j => exact h.D_mem i j
    | inr j => exact h.T_mem i j

theorem b_mem (h : GeometryIn F g) : VecIn F g.b := by
  intro i
  cases i with
  | inl _ => exact F.zero_mem
  | inr i => exact splitMass_mem F h.W i

/-- Same exact relabeling and retained stage as ClaimPin.LiteralStrictOrder8. -/
theorem fin11_mem (h : GeometryIn F g) (e : (Fin 4 ⊕ Fin 8) ≃ Fin 12) :
    let A12 := g.A.submatrix e.symm e.symm
    let b12 := g.b ∘ e.symm
    let A11 := contractMatrix (4 : Fin 12) (2 : Fin 11) A12
    let b11 := mergeCoefficient (4 : Fin 12) (2 : Fin 11) b12
    MatIn F A11 ∧ VecIn F b11 ∧ g.γ ∈ F := by
  dsimp only
  exact ⟨contractMatrix_mem F 4 2 (submatrix_mem F h.A_mem _ _),
    mergeCoefficient_mem F 4 2 (fun i => h.b_mem (e.symm i)), h.gamma⟩

end GeometryIn
end RKResearch.Certified.PaidDefectBridge.SDIRK118.Subfield
