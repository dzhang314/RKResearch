module

public import RKCert.ReviewedNative.RationalFirstBankQuietGain
public import RKCert.ReviewedNative.RationalDonorTerminalBridge

@[expose] public section

/-! Conditional terminal assembly on the actual chronological zero-seed
prefix and labelled output copies. This module does not pack the final
labels onto a single Fin index. -/

namespace RKResearch.Certified.RationalLabelledTerminalAssembly

open RKResearch RKResearch.Certified.Graded
open RKResearch.Certified.Graded.TerminalDeformation
open RKResearch.Certified.RationalDonorChain
open RKResearch.Certified.RationalDonorTerminalBridge
open RKResearch.Certified.RationalFirstBankQuietGain
open RKResearch.Certified.RationalMoments
open RKResearch.Certified.RationalTerminalMass
open scoped BigOperators FiniteRootedTree

abbrev PrefixIndex (d n : ℕ) := Fin (1 + (d + 1) * n)
abbrev LabelledSite (d n m p : ℕ) := PrefixIndex d n ⊕ (Fin m × Fin p)

variable {n m : ℕ}

/-- Literal appended rows: final-bank baseline plus the first-bank
contrast on the old prefix. Both blocks that read terminal copies
are zero. -/
noncomputable def labelledMatrix (p d : ℕ) (wide : 3 ≤ n) (c : Fin m → ℚ) :
    Matrix (LabelledSite d n m p) (LabelledSite d n m p) ℚ :=
  terminalMatrix (pureBankMatrix d (naturalSamples n))
    (primitiveRows (lastBankIndex 1 d n) (naturalSamples n) c)
    (contrast d wide) (naturalSamples p)

/-- Exact bridge weights, including zero weights on the old prefix.
Keep the division by the actual contrast action in the definition. -/
noncomputable def labelledWeight (p d : ℕ) (wide : 3 ≤ n) (c ω : Fin m → ℚ) :
    LabelledSite d n m p → ℚ :=
  let A := pureBankMatrix d (naturalSamples n)
  let η := contrast d wide
  let a := fun j => ω j / row η (monomialStageDefect A 1)
  terminalWeight (ι := PrefixIndex d n)
    (copyWeights (naturalSamples p) (primitiveWeights c 1) a)

/-- Conditional native order and literal denominator-cleared outgoing
mass on the concrete labelled block. The independent first-bank result
pays both quietness and nonzero gain, and the actual final old bank
pays the baseline. The size, distinct output clocks and target moment
conditions remain explicit. -/
theorem labelled_hasOrder_clocks_and_mass (p d : ℕ)
    (wide : 3 ≤ n) (p4 : 4 ≤ p) (chainCap : 2 + d ≤ n + 1)
    (momentCap : p ≤ n + 1) (donorPay : p ≤ 2 + d + 1)
    (c : Fin m → ℚ) (outInj : Function.Injective c) (outCap : p ≤ m)
    (ω : Fin m → ℚ) (ann : ∀ k, k + 4 ≤ p → powerMass c ω k = 0) :
    let M := labelledMatrix p d wide c
    let b := labelledWeight p d wide c ω
    RKResearch.HasOrder p M b ∧
      (∀ (j : Fin m) (l : Fin p), nodes M (Sum.inr (j, l)) = c j) ∧
      ∀ x : ℚ, clockMass M b (mat M (rootStageResidual M (.leaf ◂ .leaf))) x =
        ∑ j, if c j = x then ω j else 0 := by
  let z : Fin n → ℚ := naturalSamples n
  let A := pureBankMatrix d z
  let η := contrast d wide
  let D := primitiveRows (lastBankIndex 1 d n) z c
  let M := labelledMatrix p d wide c
  let b := labelledWeight p d wide c ω
  change RKResearch.HasOrder p M b ∧
    (∀ (j : Fin m) (l : Fin p), nodes M (Sum.inr (j, l)) = c j) ∧
    ∀ x : ℚ, clockMass M b (mat M (rootStageResidual M (.leaf ◂ .leaf))) x =
      ∑ j, if c j = x then ω j else 0

  have zInj : Function.Injective z := naturalSamples_injective n
  have seedLaw : RowLaw oneSeed (oneSeedRows z) z 2 := oneSeed_rowLaw z
  have contrastPay := contrast_quiet_gain d wide
  have quiet : Quiet A η 2 := contrastPay.1
  have gainValue : row η (monomialStageDefect A 1) = -2 := contrastPay.2.2
  have gain : row η (monomialStageDefect A 1) ≠ 0 := by
    rw [gainValue]
    decide

  have quadPay : 3 ≤ 2 + d :=
    Nat.add_one_le_add_one_iff.mp (show 3 + 1 ≤ (2 + d) + 1 from p4.trans donorPay)
  have baseline : RowLaw A D c p ∧ ∀ j, row (D j) (monomialStageDefect A 1) = 0 :=
    chain_lastBank_baseline (s := 1) (d := d) (n := n) (r₀ := 2) (p := p)
      (A₀ := oneSeed) (D₀ := oneSeedRows z) (z := z) zInj seedLaw c
      chainCap momentCap donorPay quadPay
  have p1 : 1 < p := lt_of_lt_of_le (by decide : (1 : ℕ) < 4) p4
  have clocks (j : Fin m) (l : Fin p) : nodes M (Sum.inr (j, l)) = c j := by
    change nodes (terminalMatrix A D η (naturalSamples p)) (Sum.inr (j, l)) = c j
    exact nodes_terminal_inr (h := 2) baseline.1 quiet p1 (by decide)
      (naturalSamples p) j l

  have paid : RKResearch.HasOrder p M b ∧
      ∀ x : ℚ, clockMass M b (mat M (monomialStageDefect M 1)) x =
        ∑ j, if c j = x then ω j else 0 :=
    realize_with_lastBank (s := 1) (d := d) (n := n) (r₀ := 2) (p := p)
      (A₀ := oneSeed) (D₀ := oneSeedRows z) (z := z) (c := c)
      p4 zInj seedLaw chainCap momentCap donorPay outInj outCap η quiet gain ω ann
  refine ⟨paid.1, clocks, ?_⟩
  intro x
  have sameDefect : rootStageResidual M (.leaf ◂ .leaf) = monomialStageDefect M 1 :=
    twoNode_residual_eq_monomial M
  rw [sameDefect]
  exact paid.2 x

end RKResearch.Certified.RationalLabelledTerminalAssembly
