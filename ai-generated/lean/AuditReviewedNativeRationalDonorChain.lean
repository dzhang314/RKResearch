import RKCert.ReviewedNative.RationalDonorChain

open RKResearch RKResearch.Certified.Graded
open RKResearch.Certified.Graded.TerminalDeformation
open RKResearch.Certified.RationalDonorChain
open RKResearch.Certified.RationalMoments
open scoped BigOperators Matrix

section

variable {s d n r₀ : ℕ}

example (A₀ : Matrix (Fin s) (Fin s) ℚ) (D₀ : Matrix (Fin n) (Fin s) ℚ)
    (z : Fin n → ℚ) (t : FiniteRootedTree) (i : Fin s) :
    RKResearch.Φ t (chain (d := d) A₀ D₀ z) (Sum.inl i) = RKResearch.Φ t A₀ i :=
  congrFun (phi_chain_inl (d := d) A₀ D₀ z t) i

example (A₀ : Matrix (Fin s) (Fin s) ℚ) (D₀ : Matrix (Fin n) (Fin s) ℚ)
    (z : Fin n → ℚ) (v : Site s d n → ℚ) (i : Bank d n)
    (k : Fin (d + 1)) (parent : k.val + 1 = i.1.val) :
    (chain (d := d) A₀ D₀ z *ᵥ v) (Sum.inr i) =
      ∑ j : Fin n, primitiveWeights z (z i.2) j * v (Sum.inr ⟨k, j⟩) :=
  chain_mulVec_parent A₀ D₀ z v i k parent

example {A₀ : Matrix (Fin s) (Fin s) ℚ} (strict₀ : ∀ i j, i ≤ j → A₀ i j = 0)
    (D₀ : Matrix (Fin n) (Fin s) ℚ) (z : Fin n → ℚ) :
    ∀ i j : Fin (s + (d + 1) * n), i ≤ j → chainFin (d := d) A₀ D₀ z i j = 0 :=
  chainFin_strict (d := d) strict₀ D₀ z

example {A₀ : Matrix (Fin s) (Fin s) ℚ} {D₀ : Matrix (Fin n) (Fin s) ℚ}
    {z : Fin n → ℚ} (inj : Function.Injective z) (base : RowLaw A₀ D₀ z r₀)
    (cap : r₀ + d ≤ n + 1) (i : Bank d n) (t : FiniteRootedTree)
    (pay : (t.order : ℕ) ≤ r₀ + i.1.val) :
    ((t.forestFactorial : ℕ) : ℚ) •
      RKResearch.Φ t (chainFin (d := d) A₀ D₀ z) (chronology s d n (Sum.inr i)) =
      z i.2 ^ ((t.order : ℕ) - 1) := by
  change normTree (chainFin (d := d) A₀ D₀ z) t (chronology s d n (Sum.inr i)) =
    z i.2 ^ (ord t - 1)
  exact chainFin_pure (d := d) inj base cap i t pay

example {A₀ : Matrix (Fin s) (Fin s) ℚ} {D₀ : Matrix (Fin n) (Fin s) ℚ}
    {z : Fin n → ℚ} (inj : Function.Injective z) (base : RowLaw A₀ D₀ z r₀)
    (cap : r₀ + d ≤ n + 1) (h₂ : 2 ≤ r₀) (i : Bank d n) :
    (chainFin (d := d) A₀ D₀ z *ᵥ (1 : Fin (s + (d + 1) * n) → ℚ))
      (chronology s d n (Sum.inr i)) = z i.2 :=
  chainFin_clock (d := d) inj base cap h₂ i

example (z : Fin n → ℚ) (inj : Function.Injective z) (cap : 2 + d ≤ n + 1) :
    (∀ i j : Fin (1 + (d + 1) * n), i ≤ j → pureBankMatrix d z i j = 0) ∧
      ∀ (x : Fin n) (t : FiniteRootedTree), (t.order : ℕ) ≤ 2 + d →
        ((t.forestFactorial : ℕ) : ℚ) •
          RKResearch.Φ t (pureBankMatrix d z)
            (chronology 1 d n (Sum.inr ⟨Fin.last d, x⟩)) =
          z x ^ ((t.order : ℕ) - 1) := by
  refine ⟨pureBankMatrix_strict d z, ?_⟩
  intro x t pay
  change normTree (pureBankMatrix d z) t (chronology 1 d n (Sum.inr ⟨Fin.last d, x⟩)) =
    z x ^ (ord t - 1)
  exact pureBankMatrix_last d inj cap x t pay

end

#print axioms RKResearch.Certified.RationalDonorChain.phi_chain_inl
#print axioms RKResearch.Certified.RationalDonorChain.chain_mulVec_parent
#print axioms RKResearch.Certified.RationalDonorChain.chainFin_strict
#print axioms RKResearch.Certified.RationalDonorChain.chainFin_pure
#print axioms RKResearch.Certified.RationalDonorChain.chainFin_clock
#print axioms RKResearch.Certified.RationalDonorChain.pureBankMatrix_strict
#print axioms RKResearch.Certified.RationalDonorChain.pureBankMatrix_last
