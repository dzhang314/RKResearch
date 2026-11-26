import RKCert.ReviewedNative.RationalLabelledTerminalAssembly

open RKResearch RKResearch.Certified.Graded
open RKResearch.Certified.Graded.TerminalDeformation
open RKResearch.Certified.RationalDonorChain
open RKResearch.Certified.RationalDonorTerminalBridge
open RKResearch.Certified.RationalFirstBankQuietGain
open RKResearch.Certified.RationalMoments
open RKResearch.Certified.RationalTerminalMass
open RKResearch.Certified.RationalLabelledTerminalAssembly
open scoped BigOperators FiniteRootedTree

example {n m : ℕ} (p d : ℕ)
    (wide : 3 ≤ n) (p4 : 4 ≤ p) (chainCap : 2 + d ≤ n + 1)
    (momentCap : p ≤ n + 1) (donorPay : p ≤ 2 + d + 1)
    (c : Fin m → ℚ) (outInj : Function.Injective c) (outCap : p ≤ m)
    (ω : Fin m → ℚ) (ann : ∀ k : ℕ, k + 4 ≤ p → (∑ j : Fin m, ω j * (c j)^k) = 0) :
    let z := naturalSamples n
    let A := pureBankMatrix d z
    let e := lastBankIndex 1 d n
    let D := primitiveRows e z c
    let η := contrast d wide
    let lam := naturalSamples p
    let β := primitiveWeights c 1
    let a := fun j => ω j / row η (monomialStageDefect A 1)
    let M := terminalMatrix A D η lam
    let b := terminalWeight (ι := Fin (1 + (d + 1) * n)) (copyWeights lam β a)
    RKResearch.HasOrder p M b ∧
      (∀ (j : Fin m) (l : Fin p), nodes M (Sum.inr (j, l)) = c j) ∧
      ∀ x : ℚ, clockMass M b (mat M (rootStageResidual M (.leaf ◂ .leaf))) x =
        ∑ j, if c j = x then ω j else 0 :=
  labelled_hasOrder_clocks_and_mass p d wide p4 chainCap momentCap donorPay c outInj outCap ω ann

#print axioms RKResearch.Certified.RationalLabelledTerminalAssembly.labelled_hasOrder_clocks_and_mass
