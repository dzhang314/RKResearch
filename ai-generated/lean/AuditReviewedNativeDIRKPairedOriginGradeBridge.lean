import RKCert.ReviewedNative.DIRKPairedOriginGradeBridge

/-! Standalone typed check of the actual centered grade bridge alone. -/
open Polynomial RKResearch
open RKResearch.Certified.Graded RKResearch.Certified.Graded.OneOff
open RKResearch.Certified.Graded.PairedOrigin
open scoped Classical Matrix

section
variable {K : Type*} [Field K] {s : ℕ}

example (A : Matrix (Fin s) (Fin s) K) (γ : K) (three : (3:K) ≠ 0) :
    originResidual A γ = (3:K) • mDef A 2 - (4*γ) • mDef A 1 :=
  originResidual_normalized A γ three

example (A : Matrix (Fin s) (Fin s) K) (γ : K)
    (two : (2:K) ≠ 0) (three : (3:K) ≠ 0) :
    nextResidual A γ = (4:K) • mDef A 3 - (6*γ) • mDef A 2 +
      (2*γ^2) • mDef A 1 :=
  nextResidual_normalized A γ two three

variable {A : Matrix (Fin (s+1)) (Fin (s+1)) K}

example (γ lam : K) (upper : ∀ i, (0 : Fin (s+1)) < i → A 0 i = 0)
    (diagonal : A 0 0 = γ) :
    pairedResidual A γ lam ∈ zeroSpace A 4 ∧ pairedResidual A γ lam 0 = 0 :=
  mem_centeredZeroSpace.mp (pairedResidual_mem_centered γ lam upper diagonal)

example {r d : ℕ} {v : Fin (s+1) → K} (grade : v ∈ zeroSpace A r) (origin : v 0 = 0)
    {P : K[X]} (degree : P.natDegree ≤ d) :
    diag v (evalNodes A P) ∈ zeroSpace A (r+d) ∧ diag v (evalNodes A P) 0 = 0 :=
  mem_centeredZeroSpace.mp (defectPolynomial_mem_centered
    (mem_centeredZeroSpace.mpr ⟨grade,origin⟩) degree)

example {j : ℕ} {v : Fin (s+1) → K}
    (upper : ∀ i, (0 : Fin (s+1)) < i → A 0 i = 0)
    (units : ∀ t : FiniteRootedTree, (t.order:ℕ) ≤ j+1 → IsUnit (((t.order:ℕ):K)))
    (grade : v ∈ zeroSpace A j) (origin : v 0 = 0) :
    mat A v ∈ zeroSpace A (j+1) ∧ mat A v 0 = 0 :=
  mem_centeredZeroSpace.mp (mat_mem_centered_of_unit upper units
    (mem_centeredZeroSpace.mpr ⟨grade,origin⟩))

example {γ lam : K} {k : Fin (s+1)} {d : ℕ}
    (upper : ∀ i, (0 : Fin (s+1)) < i → A 0 i = 0) (diagonal : A 0 0 = γ)
    (units : ∀ t : FiniteRootedTree, (t.order:ℕ) ≤ 4+d+1 → IsUnit (((t.order:ℕ):K)))
    (kills : ∀ v ∈ zeroSpace A (4+d+1), v 0 = 0 → v k = 0) :
    ∀ P : K[X], P.natDegree ≤ d →
      mat A (diag (pairedResidual A γ lam) (evalNodes A P)) k = 0 := by
  refine paid_pairedResidue_of_centered_annihilation upper diagonal units ?_
  intro v hv
  have h := mem_centeredZeroSpace.mp hv
  exact kills v h.1 h.2

end

#print axioms RKResearch.Certified.Graded.PairedOrigin.originResidual_normalized
#print axioms RKResearch.Certified.Graded.PairedOrigin.nextResidual_normalized
#print axioms RKResearch.Certified.Graded.PairedOrigin.pairedResidual_mem_centered
#print axioms RKResearch.Certified.Graded.PairedOrigin.defectPolynomial_mem_centered
#print axioms RKResearch.Certified.Graded.PairedOrigin.mat_mem_centered_of_unit
#print axioms RKResearch.Certified.Graded.PairedOrigin.paid_pairedResidue_of_centered_annihilation
