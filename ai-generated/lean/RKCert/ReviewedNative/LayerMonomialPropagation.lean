module
public import RKCert.ReviewedNative.AdjacentLayerRows

@[expose] public section

/-! # Native forest-scaled columns from a paid adjacent-layer action

The premise concerns the action of the actual matrix on any column
with the specified monomial values on the receiving and parent fibres.
Neither the matrix construction nor an output row is needed here.
-/

namespace RKResearch.Certified.LayerMonomialPropagation

open RKResearch.FiniteSeries.AdjacentLayerRows (layerSlice layerSlice_apply)
open scoped Matrix FiniteRootedTree

/-- Layer ℓ has ℓ+1 stage coordinates. -/
abbrev LayerStage (D : ℕ) :=
  Σ h : Fin (D+1), Fin (h.val+1)

variable {D : ℕ} {R : Type*} [CommSemiring R]

/-- These are assigned labels, not an assumption about the tableau clocks. -/
def layerPowers (x : LayerStage D → R) (h : Fin (D+1)) (d : ℕ) :
    Fin (h.val+1) → R :=
  fun i => x ⟨h,i⟩ ^ d

/-- On the two actual fibres, a matched monomial column pays one
denominator-cleared step of the physical multiplication by A. -/
def LayerMonomialStep (A : Matrix (LayerStage D) (LayerStage D) R)
    (x : LayerStage D → R) : Prop :=
  ∀ (h k : Fin (D+1)), k.val+1 = h.val →
    ∀ d : ℕ, d < h.val →
      ∀ v : LayerStage D → R,
        layerSlice v h = layerPowers x h d →
        layerSlice v k = layerPowers x k d →
        ∀ i : Fin (h.val+1),
          ((d+1 : ℕ) : R) * (A *ᵥ v) ⟨h,i⟩ = x ⟨h,i⟩ ^ (d+1)

/-- A paid layer contains the literal forest-factor-scaled native tree columns.
Induct over trees simultaneously for all layers, so a proper branch is
available on the receiving layer as well as its parent. -/
theorem layerSlice_forestFactorial_smul_phi
    (A : Matrix (LayerStage D) (LayerStage D) R) (x : LayerStage D → R)
    (step : LayerMonomialStep A x) (t : FiniteRootedTree) :
    ∀ h : Fin (D+1), (t.order : ℕ) ≤ h.val+1 →
      layerSlice (((t.forestFactorial : ℕ) : R) • Φ t A) h =
        layerPowers x h ((t.order : ℕ)-1) := by
  unfold LayerMonomialStep at step
  induction t with
  | leaf =>
    intro h _
    funext i
    simp [layerPowers, Φ, FiniteRootedTree.order, FiniteRootedTree.forestFactorial]
  | butcherProduct a u ihA ihU =>
    intro h paid
    have ha_pos : 0 < (a.order : ℕ) := a.order.pos
    have hu_pos : 0 < (u.order : ℕ) := u.order.pos
    have total : (a.order : ℕ) + (u.order : ℕ) ≤ h.val+1 := by
      simpa only [FiniteRootedTree.order, PNat.add_coe] using paid
    have ha : (a.order : ℕ) ≤ h.val+1 := by omega
    have hu : (u.order : ℕ) ≤ h.val := by omega
    let k : Fin (D+1) := ⟨h.val-1, lt_of_le_of_lt (Nat.sub_le _ _) h.isLt⟩
    have hk : k.val+1 = h.val := by
      change h.val-1+1 = h.val
      omega
    have hu_here : (u.order : ℕ) ≤ h.val+1 := hu.trans (Nat.le_succ _)
    have hu_parent : (u.order : ℕ) ≤ k.val+1 := by simpa only [hk] using hu
    have hdeg : (u.order : ℕ)-1 < h.val := by omega
    have d_succ : (u.order : ℕ)-1+1 = (u.order : ℕ) := by omega
    have power_index :
        (a.order : ℕ)-1+(u.order : ℕ) = ((a ◂ u).order : ℕ)-1 := by
      simp only [FiniteRootedTree.order, PNat.add_coe]
      omega
    funext i
    have base :
        ((a.forestFactorial : ℕ) : R) * Φ a A ⟨h,i⟩ =
          x ⟨h,i⟩ ^ ((a.order : ℕ)-1) := by
      simpa only [layerSlice_apply, layerPowers, Pi.smul_apply, smul_eq_mul]
        using congrFun (ihA h ha) i
    have branch :
        ((u.factorial : ℕ) : R) * (A *ᵥ Φ u A) ⟨h,i⟩ =
          x ⟨h,i⟩ ^ (u.order : ℕ) := by
      have observed := step h k hk ((u.order : ℕ)-1) hdeg
        (((u.forestFactorial : ℕ) : R) • Φ u A) (ihU h hu_here) (ihU k hu_parent) i
      simpa only [d_succ, Matrix.mulVec_smul, Pi.smul_apply, smul_eq_mul,
        FiniteRootedTree.factorial, PNat.mul_coe, Nat.cast_mul, mul_assoc] using observed
    calc
      _ = (((a.forestFactorial : ℕ) : R) * Φ a A ⟨h,i⟩) *
          (((u.factorial : ℕ) : R) * (A *ᵥ Φ u A) ⟨h,i⟩) := by
        simp only [layerSlice_apply, Pi.smul_apply, smul_eq_mul,
          FiniteRootedTree.forestFactorial, FiniteRootedTree.factorial, PNat.mul_coe,
          Nat.cast_mul, Φ, Pi.mul_apply]
        exact mul_mul_mul_comm _ _ _ _
      _ = x ⟨h,i⟩ ^ ((a.order : ℕ)-1) * x ⟨h,i⟩ ^ (u.order : ℕ) := by
        rw [base, branch]
      _ = _ := by
        simp only [layerPowers, ← pow_add, power_index]

end RKResearch.Certified.LayerMonomialPropagation
