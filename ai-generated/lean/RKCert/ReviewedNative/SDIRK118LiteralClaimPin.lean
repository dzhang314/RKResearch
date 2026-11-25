module

public import RKCert.ReviewedNative.SDIRK118ExactScalarDonorBinding

@[expose] public section

noncomputable section

namespace RKResearch.Certified.PaidDefectBridge.SDIRK118.ClaimPin

open RKResearch
open RKResearch.Certified.DiagonalTwin (contractMatrix)
open RKResearch.Certified.Graded (mergeCoefficient)
open RKResearch.Certified.PaidDefectBridge.SDIRK118.ScalarBindings
open scoped Matrix BigOperators

abbrev MonomialBasis := Module.Basis ℕ ℝ (Polynomial ℝ)

def standardPowers (M : MonomialBasis) : Prop :=
  ∀ n, M n=Polynomial.X^n

def Bstar (M : MonomialBasis) (s t : ℝ) : Polynomial ℝ :=
  Polynomial.X^2+Polynomial.C (beta1 M s t)*Polynomial.X+Polynomial.C (beta0 M s t)

def omegaOld (M : MonomialBasis) (s t : ℝ) (i : Fin 4) : ℝ :=
  avg M (zAt s) (Bstar M s t *
    (∏ j ∈ Finset.univ.erase i, linearFactor (uAt s t j)))

def residualJ0 (M : MonomialBasis) (s t : ℝ) : ℝ :=
  avg M (zAt s) (linearFactor (aAt s)*Bstar M s t*coefficientPrimitive M (Jpoly s t))

/-- Only real root semantics and exact scalar inequalities. No matrix,
weight, rank, quadrature, word payment, or chosen d is a field. -/
structure ExactScalarSeed (M : MonomialBasis) (s t cStar : ℝ) : Prop where
  sLower : (13/32 : ℝ)<s
  sUpper : s<(14/32 : ℝ)
  sRoot : s^3-9*s^2+18*s-6=0
  tLower : (1/8 : ℝ)<t
  tUpper : t<(13/100 : ℝ)
  tRoot : qSeed s t=0
  momentPivotPos : 0<momentDet M s t
  quadAtZeroNeg : quadraticAt M s t 0<0
  cRight : zAt s<cStar
  cRoot : quadraticAt M s t cStar=0
  omegaNe : ∀ i : Fin 4, omegaOld M s t i ≠ 0
  residualPos : 0<residualJ0 M s t
  affineLowerNeg : affineAt M s t cStar (15/4)<0
  affineUpperPos : 0<affineAt M s t cStar 4

def orderedBlocks (e : (Fin 4 ⊕ Fin 8) ≃ Fin 12) : Prop :=
  (∀ i : Fin 4, (e (.inl i)).val=i.val) ∧
  (∀ j : Fin 8, (e (.inr j)).val=4+j.val)

/-- This is the literal archived chart and literal deleted column, not
an arbitrary existential tableau. -/
def LiteralStrictOrder8 (M : MonomialBasis) (s t cStar : ℝ)
    (e : (Fin 4 ⊕ Fin 8) ≃ Fin 12) : Prop :=
  let g := geometry M s t cStar
  let A12 := g.A.submatrix e.symm e.symm
  let b12 := g.b ∘ e.symm
  let A11 := contractMatrix (4 : Fin 12) (2 : Fin 11) A12
  let b11 := mergeCoefficient (4 : Fin 12) (2 : Fin 11) b12
  0<g.γ ∧ A11.IsLowerTriangular ∧ (∀ i : Fin 11,A11 i i=g.γ) ∧
    HasOrder 8 A11 b11

/-- Kernel audit target for the conditional literal producer. -/
def ConditionalTarget : Prop :=
  ∀ (M : MonomialBasis), standardPowers M →
    ∀ (e : (Fin 4 ⊕ Fin 8) ≃ Fin 12), orderedBlocks e →
      ∀ (s t cStar : ℝ), ExactScalarSeed M s t cStar →
        LiteralStrictOrder8 M s t cStar e

/-- Separate real-polynomial theorem: existence follows from the exact
signed guards and IVT, not from a numerical value of a stage. -/
def ScalarExistenceTarget : Prop :=
  ∀ (M : MonomialBasis), standardPowers M →
    ∃ (s t cStar : ℝ), ExactScalarSeed M s t cStar

/-- Only after this closed target is checked can the new native upper
endpoint be counted. No positive-clock or exact-order-9 statement. -/
def ClosedTarget : Prop :=
  ∃ (A : Matrix (Fin 11) (Fin 11) ℝ) (b : Fin 11 → ℝ) (γ : ℝ),
    0<γ ∧ A.IsLowerTriangular ∧ (∀ i : Fin 11,A i i=γ) ∧ HasOrder 8 A b

/-- Final orchestration only: supply the selected standard basis and canonical
block equivalence; this theorem proves no scalar sign or conditional chart
premise by assumption hidden in the target. -/
theorem close_from_two_proofs (hcond : ConditionalTarget) (hex : ScalarExistenceTarget)
    (M : MonomialBasis) (hm : standardPowers M)
    (e : (Fin 4 ⊕ Fin 8) ≃ Fin 12) (he : orderedBlocks e) : ClosedTarget := by
  obtain ⟨s,t,c,hseed⟩ := hex M hm
  have h := hcond M hm e he s t c hseed
  let g := geometry M s t c
  let A12 := g.A.submatrix e.symm e.symm
  let b12 := g.b ∘ e.symm
  exact ⟨contractMatrix (4 : Fin 12) (2 : Fin 11) A12,
    mergeCoefficient (4 : Fin 12) (2 : Fin 11) b12,g.γ,h⟩

end RKResearch.Certified.PaidDefectBridge.SDIRK118.ClaimPin
