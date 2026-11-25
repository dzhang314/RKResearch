module

import RKCert.ReviewedNative.AdjacentLayerRows

open RKResearch RKResearch.FiniteSeries.AdjacentLayerRows
open scoped Matrix

section

variable {D : ℕ} {L : Fin (D+1) → Type*} {R : Type*}
variable [∀ h, Fintype (L h)] [CommSemiring R]

example (A : Matrix (Sigma L) (Sigma L) R) (i j : Sigma L) :
    ((j.1 : ℕ)+1 = (i.1 : ℕ) → adjacentMask A i j = A i j) ∧
      ((j.1 : ℕ)+1 ≠ (i.1 : ℕ) → adjacentMask A i j = 0) :=
  ⟨adjacentMask_on A i j, adjacentMask_off A i j⟩

example (A : Matrix (Sigma L) (Sigma L) R) (v : Sigma L → R)
    (i : Sigma L) (h : Fin (D+1)) (parent : (h : ℕ)+1 = (i.1 : ℕ))
    (x : L h → R) (z : R) (agree : layerSlice v h = x)
    (paid : layerSlice (A i) h ⬝ᵥ x = z) :
    ((adjacentMask A *ᵥ v) i = layerSlice (A i) h ⬝ᵥ layerSlice v h) ∧
      ((adjacentMask A *ᵥ v) i = z) :=
  ⟨mulVec_adjacentMask_eq_on_parent A v i h parent,
    mulVec_adjacentMask_eq_of_paid A v i h parent agree paid⟩

example (A : Matrix (Sigma L) (Sigma L) R) (v : Sigma L → R)
    (i : Sigma L) (first : (i.1 : ℕ) = 0) : (adjacentMask A *ᵥ v) i = 0 :=
  mulVec_adjacentMask_eq_zero_first A v i first

example (b v : Sigma L → R) (h : Fin (D+1))
    (off : ∀ i : Sigma L, i.1 ≠ h → b i = 0) :
    b ⬝ᵥ v = layerSlice b h ⬝ᵥ layerSlice v h :=
  dotProduct_eq_on_layer b v h off

/- Precisely one literal graft, with the parent row payment supplied. -/
example {ι : Type*} [Fintype ι] (M : Matrix ι ι R)
    (A : Matrix (Sigma L) (Sigma L) R)
    (base branch : FiniteRootedTree) (i : Sigma L) (k : ι)
    (h : Fin (D+1)) (parent : (h : ℕ)+1 = (i.1 : ℕ))
    (base_eq : Φ base (adjacentMask A) i = Φ base M k)
    (x : L h → R) (branch_eq : layerSlice (Φ branch (adjacentMask A)) h = x)
    (paid : layerSlice (A i) h ⬝ᵥ x = (M *ᵥ Φ branch M) k) :
    Φ (.butcherProduct base branch) (adjacentMask A) i =
      Φ (.butcherProduct base branch) M k :=
  phi_graft_eq_of_parent M A base branch i k h parent base_eq branch_eq paid

end

#print axioms RKResearch.FiniteSeries.AdjacentLayerRows.adjacentMask_on
#print axioms RKResearch.FiniteSeries.AdjacentLayerRows.adjacentMask_off
#print axioms RKResearch.FiniteSeries.AdjacentLayerRows.mulVec_adjacentMask_eq_on_parent
#print axioms RKResearch.FiniteSeries.AdjacentLayerRows.mulVec_adjacentMask_eq_of_paid
#print axioms RKResearch.FiniteSeries.AdjacentLayerRows.mulVec_adjacentMask_eq_zero_first
#print axioms RKResearch.FiniteSeries.AdjacentLayerRows.dotProduct_eq_on_layer
#print axioms RKResearch.FiniteSeries.AdjacentLayerRows.phi_graft_eq_of_parent
