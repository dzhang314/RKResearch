import RKCert.ReviewedNative.RationalFirstBankQuietGain

open RKResearch RKResearch.Certified.Graded
open RKResearch.Certified.Graded.TerminalDeformation
open RKResearch.Certified.RationalDonorChain
open RKResearch.Certified.RationalFirstBankQuietGain
open scoped FiniteRootedTree Matrix

example {ι : Type*} [Fintype ι] (A : Matrix ι ι ℚ) (i : ι) :
    rootStageResidual A (.leaf ◂ .leaf) i =
      2 * (A *ᵥ (A *ᵥ (1 : ι → ℚ))) i - ((A *ᵥ (1 : ι → ℚ)) i)^2 :=
  twoNode_residual_formula A i

example {d n : ℕ} (wide : 3 ≤ n) :
    let A := pureBankMatrix d (fun j : Fin n => (j.val : ℚ))
    let η := contrast d wide
    Quiet A η 2 ∧
      row η (normTree A .leaf) = 0 ∧
      row η (normTree A (.leaf ◂ .leaf)) = 0 ∧
      row η (rootStageResidual A (.leaf ◂ .leaf)) = -2 ∧
      row η (monomialStageDefect A 1) = -2 := by
  have h := contrast_quiet_gain d wide
  exact ⟨h.1, h.1 .leaf (by decide), h.1 (.leaf ◂ .leaf) (by decide), h.2.1, h.2.2⟩

#print axioms RKResearch.Certified.RationalFirstBankQuietGain.twoNode_residual_formula
#print axioms RKResearch.Certified.RationalFirstBankQuietGain.contrast_quiet_gain
