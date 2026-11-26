module

import RKCert.ReviewedNative.LayerMonomialPropagation

open RKResearch
open RKResearch.FiniteSeries.AdjacentLayerRows (layerSlice)
open RKResearch.Certified.LayerMonomialPropagation
open scoped Matrix

section
variable {D : ℕ} {R : Type*} [CommSemiring R]

example (A : Matrix (LayerStage D) (LayerStage D) R) (x : LayerStage D → R)
    (step : ∀ (h k : Fin (D+1)), k.val + 1 = h.val →
      ∀ d : ℕ, d < h.val →
        ∀ v : LayerStage D → R,
          layerSlice v h = (fun i : Fin (h.val+1) => x ⟨h,i⟩ ^ d) →
          layerSlice v k = (fun j : Fin (k.val+1) => x ⟨k,j⟩ ^ d) →
          ∀ i : Fin (h.val+1),
            ((d+1 : ℕ) : R) * (A *ᵥ v) ⟨h,i⟩ = x ⟨h,i⟩ ^ (d+1))
    (t : FiniteRootedTree) (h : Fin (D+1)) (paid : (t.order : ℕ) ≤ h.val + 1) :
    layerSlice (((t.forestFactorial : ℕ) : R) • Φ t A) h =
      fun i : Fin (h.val+1) => x ⟨h,i⟩ ^ ((t.order : ℕ) - 1) :=
  layerSlice_forestFactorial_smul_phi A x step t h paid

end

#print axioms RKResearch.Certified.LayerMonomialPropagation.layerSlice_forestFactorial_smul_phi
