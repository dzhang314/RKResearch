import RKCert.ReviewedNative.RationalDonorTerminalBridge

open RKResearch RKResearch.Certified.Graded
open RKResearch.Certified.Graded.TerminalDeformation
open RKResearch.Certified.RationalDonorChain
open RKResearch.Certified.RationalTerminalMass
open RKResearch.Certified.RationalMoments
open RKResearch.Certified.RationalDonorTerminalBridge
open scoped BigOperators Matrix

section

variable {s d n r₀ p : ℕ}
variable {A₀ : Matrix (Fin s) (Fin s) ℚ} {D₀ : Matrix (Fin n) (Fin s) ℚ}
variable {z : Fin n → ℚ}

example {σ : Type*} [Fintype σ] (inj : Function.Injective z)
    (base₀ : RowLaw A₀ D₀ z r₀) (c : σ → ℚ)
    (chainCap : r₀ + d ≤ n + 1) (momentCap : p ≤ n + 1)
    (donorPay : p ≤ r₀ + d + 1) (quadPay : 3 ≤ r₀ + d) :
    let A := chainFin (d := d) A₀ D₀ z
    let e := fun j : Fin n => chronology s d n (Sum.inr (⟨Fin.last d, j⟩ : Bank d n))
    let D := primitiveRows e z c
    RowLaw A D c p ∧ ∀ x, row (D x) (monomialStageDefect A 1) = 0 :=
  chain_lastBank_baseline (d := d) (p := p) inj base₀ c
    chainCap momentCap donorPay quadPay

example (inj : Function.Injective z) (base₀ : RowLaw A₀ D₀ z r₀)
    (chainCap : r₀ + d ≤ n + 1) (quadPay : 3 ≤ r₀ + d) (w : Fin n → ℚ) :
    let A := chainFin (d := d) A₀ D₀ z
    let e := fun j : Fin n => chronology s d n (Sum.inr (⟨Fin.last d, j⟩ : Bank d n))
    row (liftDonorWeights e w) (monomialStageDefect A 1) = 0 :=
  lastBank_lift_has_zero_gain (d := d) inj base₀ chainCap quadPay w

example {m : ℕ} {c : Fin m → ℚ}
    (p4 : 4 ≤ p) (inj : Function.Injective z) (base₀ : RowLaw A₀ D₀ z r₀)
    (chainCap : r₀ + d ≤ n + 1) (momentCap : p ≤ n + 1)
    (donorPay : p ≤ r₀ + d + 1) (outInj : Function.Injective c) (outCap : p ≤ m)
    (η : Fin (s + (d + 1) * n) → ℚ)
    (quiet : Quiet (chainFin (d := d) A₀ D₀ z) η 2)
    (gain : row η (monomialStageDefect (chainFin (d := d) A₀ D₀ z) 1) ≠ 0)
    (ω : Fin m → ℚ) (ann : ∀ k, k + 4 ≤ p → powerMass c ω k = 0) :
    let A := chainFin (d := d) A₀ D₀ z
    let e := fun j : Fin n => chronology s d n (Sum.inr (⟨Fin.last d, j⟩ : Bank d n))
    let D := primitiveRows e z c
    let β := primitiveWeights c 1
    let lam := naturalSamples p
    let a := fun x => ω x / row η (monomialStageDefect A 1)
    let M := terminalMatrix A D η lam
    let b := terminalWeight (ι := Fin (s + (d + 1) * n)) (copyWeights lam β a)
    RKResearch.HasOrder p M b ∧
      ∀ x, clockMass M b (mat M (monomialStageDefect M 1)) x =
        ∑ j, if c j = x then ω j else 0 :=
  realize_with_lastBank (d := d) (p := p) p4 inj base₀ chainCap momentCap donorPay
    outInj outCap η quiet gain ω ann

end

#print axioms RKResearch.Certified.RationalDonorTerminalBridge.chain_lastBank_baseline
#print axioms RKResearch.Certified.RationalDonorTerminalBridge.lastBank_lift_has_zero_gain
#print axioms RKResearch.Certified.RationalDonorTerminalBridge.realize_with_lastBank
