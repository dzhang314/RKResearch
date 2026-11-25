import RKCert.ReviewedNative.ERKTerminalDeformation

open RKResearch RKResearch.Certified.Graded
open RKResearch.Certified.Graded.TerminalDeformation
open scoped BigOperators Matrix Classical

section

variable {ι σ τ K : Type*} [Fintype ι] [Fintype σ] [Fintype τ] [CommRing K]
variable {A : Matrix ι ι K} {D : Matrix σ ι K} {c : σ → K}
variable {p h : ℕ} {η : ι → K} {lam : τ → K} {w : σ → τ → K}
variable {β a : σ → K}

example (law : RowLaw A D c p) (quiet : Quiet A η h)
    (copy : CopyMoments lam w β a p)
    (ann : ∀ k, k + h + 2 ≤ p → (∑ x, a x * c x ^ k) = 0)
    (quad : ∀ k, k + 1 ≤ p → ((k + 1 : ℕ) : K) * (∑ x, β x * c x ^ k) = 1) :
    RKResearch.HasOrder p (terminalMatrix A D η lam)
      (Sum.elim (fun _ => 0) (fun j : σ × τ => w j.1 j.2)) :=
  terminal_hasOrder law quiet copy ann quad

example (law : RowLaw A D c p) (quiet : Quiet A η h)
    (copy : CopyMoments lam w β a p) (p1 : 1 < p) (h1 : 1 ≤ h)
    (q : ι ⊕ (σ × τ) → K) (z : K) :
    let M := terminalMatrix A D η lam
    let B : ι ⊕ (σ × τ) → K := Sum.elim (fun _ => 0) (fun j => w j.1 j.2)
    (∑ i, if (M *ᵥ 1) i = z then B i * (M *ᵥ q) i else 0) =
      ∑ x, if c x = z then
        β x * (D x ⬝ᵥ (q ∘ Sum.inl)) + a x * (η ⬝ᵥ (q ∘ Sum.inl)) else 0 := by
  simpa only [clockMass, terminalWeight, mat_apply, row_apply] using
    terminal_clockMass law quiet copy p1 h1 q z

end

#print axioms RKResearch.Certified.Graded.TerminalDeformation.terminal_hasOrder
#print axioms RKResearch.Certified.Graded.TerminalDeformation.terminal_clockMass
