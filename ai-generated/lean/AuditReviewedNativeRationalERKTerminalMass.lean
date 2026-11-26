import RKCert.ReviewedNative.RationalERKTerminalMass

open RKResearch RKResearch.Certified.Graded
open RKResearch.Certified.Graded.TerminalDeformation
open RKResearch.Certified.RationalTerminalMass
open scoped BigOperators Matrix

section

variable {ι σ : Type*} [Fintype ι] [Fintype σ] {p : ℕ}

example {A : Matrix ι ι ℚ} {D : Matrix σ ι ℚ} {c β ω : σ → ℚ}
    (p4 : 4 ≤ p) (law : RowLaw A D c p) {η : ι → ℚ} (quiet : Quiet A η 2)
    {lam : Fin p → ℚ} (inj : Function.Injective lam)
    (base : ∀ x, row (D x) (monomialStageDefect A 1) = 0)
    (gain : row η (monomialStageDefect A 1) ≠ 0)
    (ann : ∀ k, k + 4 ≤ p → (∑ x, ω x * c x ^ k) = 0)
    (quad : ∀ k, k + 1 ≤ p → ((k + 1 : ℕ) : ℚ) * (∑ x, β x * c x ^ k) = 1) :
    ∃ (M : Matrix (ι ⊕ (σ × Fin p)) (ι ⊕ (σ × Fin p)) ℚ)
      (b : ι ⊕ (σ × Fin p) → ℚ),
      M = Matrix.fromBlocks A (0 : Matrix ι (σ × Fin p) ℚ)
        (fun j i => D j.1 i + lam j.2 * η i) (0 : Matrix (σ × Fin p) (σ × Fin p) ℚ) ∧
      b = Sum.elim (fun _ => 0) (fun j : σ × Fin p =>
        copyWeights lam β (fun x => ω x / row η (monomialStageDefect A 1)) j.1 j.2) ∧
      RKResearch.HasOrder p M b ∧
      ∀ z : ℚ,
        let cM := M *ᵥ (1 : ι ⊕ (σ × Fin p) → ℚ)
        let qM : ι ⊕ (σ × Fin p) → ℚ := fun i =>
          (2 : ℚ) * (M *ᵥ cM) i - cM i ^ 2
        (∑ i, if cM i = z then b i * (M *ᵥ qM) i else 0) =
          ∑ x, if c x = z then ω x else 0 := by
  let a : σ → ℚ := fun x => ω x / row η (monomialStageDefect A 1)
  let M := terminalMatrix A D η lam
  let b : ι ⊕ (σ × Fin p) → ℚ := Sum.elim (fun _ => 0)
    (fun j => copyWeights lam β a j.1 j.2)
  have actual := realize_quadratic_outgoing_mass p4 law quiet inj base gain ann quad
  change RKResearch.HasOrder p M b ∧
    (∀ z : ℚ, clockMass M b (mat M (monomialStageDefect M 1)) z =
      ∑ x, if c x = z then ω x else 0) at actual
  refine ⟨M, b, rfl, rfl, actual.1, ?_⟩
  intro z
  let v := M *ᵥ (1 : ι ⊕ (σ × Fin p) → ℚ)
  let q : ι ⊕ (σ × Fin p) → ℚ := fun i => (2 : ℚ) * (M *ᵥ v) i - v i ^ 2
  change (∑ i, if v i = z then b i * (M *ᵥ q) i else 0) = _
  have hq : q = monomialStageDefect M 1 := by
    funext i
    simp [q, v, monomialStageDefect]
  rw [hq]
  calc
    _ = clockMass M b (mat M (monomialStageDefect M 1)) z := by
      unfold clockMass
      apply Finset.sum_congr rfl
      intro i _
      by_cases hi : (M *ᵥ (1 : ι ⊕ (σ × Fin p) → ℚ)) i = z
      · simp [v, nodes, mat_apply, hi]
      · simp [v, nodes, hi]
    _ = _ := actual.2 z

end

#print axioms RKResearch.Certified.RationalTerminalMass.realize_quadratic_outgoing_mass
