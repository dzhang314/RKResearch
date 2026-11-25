module

public import RKCert.ReviewedNative.CoordinateRankFrame
public import RKCert.ReviewedNative.AdjacentLayerRows
public import RKCert.ReviewedNative.CommonDiagonalHeight

import Lean.Elab.Tactic.Omega

@[expose] public section

/-! # Finite band unrolling of a dense reference

Each fibre uses an actual coordinate frame of the native height/order
span. Only the preceding fibre acts in a matrix row. The scalar series
agrees with the dense reference on the specified band and is zero above
the terminal height. The reference itself need not be causal or have
zero taller outputs.
-/

namespace RKResearch.FiniteSeries.RankUnroll

open RKResearch FiniteRootedTree Module
open RKResearch.Certified.Graded
open RKResearch.Certified.Graded.RankCoordinates
open RKResearch.FiniteSeries.AdjacentLayerRows
open scoped BigOperators Matrix

noncomputable section

variable {ι K : Type*} [Fintype ι] [Field K]

/-- A native band at layer h contains trees of height ≤ h and
literal order ≤ lead+h. -/
abbrev Band (M : Matrix ι ι K) (lead h : ℕ) : Submodule K (ι → K) :=
  heightOrderSpace M h (lead+h)

abbrev Layer (M : Matrix ι ι K) (lead h : ℕ) : Type :=
  Fin (finrank K (Band M lead h))

abbrev Stage (M : Matrix ι ι K) (lead D : ℕ) : Type :=
  Σ h : Fin (D+1), Layer M lead (h : ℕ)

abbrev Frames (M : Matrix ι ι K) (lead D : ℕ) :=
  ∀ h : Fin (D+1), CoordinateFrame (Band M lead (h : ℕ))

/-- No externally supplied pivot or rank hypothesis is needed. -/
def chosenFrames (M : Matrix ι ι K) (lead D : ℕ) : Frames M lead D :=
  fun h => Classical.choice (exists_coordinateFrame (Band M lead (h : ℕ)))

variable {M : Matrix ι ι K} {lead D : ℕ}

/-- Original reference label of a physical stage in its frame. -/
def originalIndex (F : Frames M lead D) (i : Stage M lead D) : ι :=
  (F i.1).labels i.2

/-- Compute the transferred row on whatever source fibre is requested.
The strict adjacent mask is applied separately. -/
def rawRows (F : Frames M lead D) :
    Matrix (Stage M lead D) (Stage M lead D) K :=
  fun i j => (F j.1).rowOver
    ((row (M (originalIndex F i))).comp (Band M lead (j.1 : ℕ)).subtype) j.2

def unrollMatrix (F : Frames M lead D) :
    Matrix (Stage M lead D) (Stage M lead D) K :=
  adjacentMask (rawRows F)

def unrollWeights (F : Frames M lead D) (w : ι → K) : Stage M lead D → K :=
  fun j => if j.1 = Fin.last D then
    (F j.1).rowOver ((row w).comp (Band M lead (j.1 : ℕ)).subtype) j.2
  else 0

private theorem unrollWeights_off (F : Frames M lead D) (w : ι → K)
    (i : Stage M lead D) (away : i.1 ≠ Fin.last D) :
    unrollWeights F w i = 0 :=
  ite_eq_right away

private theorem phi_agrees (F : Frames M lead D) (t : FiniteRootedTree)
    (i : Stage M lead D) (ht : treeHeight t ≤ (i.1 : ℕ))
    (ord : (t.order : ℕ) ≤ lead + (i.1 : ℕ)) :
    Φ t (unrollMatrix F) i = Φ t M (originalIndex F i) := by
  induction t generalizing i with
  | leaf => rfl
  | butcherProduct base branch ihBase ihBranch =>
    have heights : max (treeHeight base) (treeHeight branch+1) ≤ (i.1 : ℕ) :=
      ht
    have baseHeight : treeHeight base ≤ (i.1 : ℕ) := (max_le_iff.mp heights).1
    have branchStep : treeHeight branch+1 ≤ (i.1 : ℕ) := (max_le_iff.mp heights).2
    have allOrder : (base.order : ℕ)+(branch.order : ℕ) ≤ lead+(i.1 : ℕ) := by
      simpa only [FiniteRootedTree.order, PNat.add_coe] using ord
    have baseOrder : (base.order : ℕ) ≤ lead+(i.1 : ℕ) := by omega
    have basePos : 0 < (base.order : ℕ) := base.order.pos
    let h : Fin (D+1) := ⟨(i.1 : ℕ)-1, (Nat.sub_le _ _).trans_lt i.1.isLt⟩
    have parent : (h : ℕ)+1 = (i.1 : ℕ) := by
      change (i.1 : ℕ)-1+1 = (i.1 : ℕ)
      omega
    have branchHeight : treeHeight branch ≤ (h : ℕ) := by omega
    have branchOrder : (branch.order : ℕ) ≤ lead+(h : ℕ) := by omega
    let x : Band M lead (h : ℕ) :=
      ⟨Φ branch M, Φ_mem_heightOrderSpace M branch branchHeight branchOrder⟩
    have base_eq : Φ base (unrollMatrix F) i = Φ base M (originalIndex F i) :=
      ihBase i baseHeight baseOrder
    have branch_eq : layerSlice (Φ branch (unrollMatrix F)) h = (F h).restrictEquiv x := by
      funext j
      rw [layerSlice_apply, CoordinateFrame.restrictEquiv_apply]
      exact ihBranch ⟨h,j⟩ branchHeight branchOrder
    have paid : layerSlice (rawRows F i) h ⬝ᵥ (F h).restrictEquiv x =
        (M *ᵥ Φ branch M) (originalIndex F i) := by
      exact (F h).row_rowOver
        ((row (M (originalIndex F i))).comp (Band M lead (h : ℕ)).subtype) x
    exact phi_graft_eq_of_parent M (rawRows F) base branch i (originalIndex F i)
      h parent base_eq branch_eq paid

private theorem phi_zero_above
    (A : Matrix (Stage M lead D) (Stage M lead D) K) (t : FiniteRootedTree)
    (i : Stage M lead D) (high : (i.1 : ℕ) < treeHeight t) :
    Φ t (adjacentMask A) i = 0 := by
  induction t generalizing i with
  | leaf =>
    have impossible : (i.1 : ℕ) < 0 := high
    omega
  | butcherProduct base branch ihBase ihBranch =>
    have gtMax : (i.1 : ℕ) < max (treeHeight base) (treeHeight branch+1) := high
    change Φ base (adjacentMask A) i * (adjacentMask A *ᵥ Φ branch (adjacentMask A)) i = 0
    rcases lt_max_iff.mp gtMax with hb | hu
    · rw [ihBase i hb, zero_mul]
    · have act : (adjacentMask A *ᵥ Φ branch (adjacentMask A)) i = 0 := by
        rw [Matrix.mulVec_apply_eq_sum]
        apply Finset.sum_eq_zero
        intro j _
        by_cases edge : (j.1 : ℕ)+1 = (i.1 : ℕ)
        · have tooHigh : (j.1 : ℕ) < treeHeight branch := by omega
          rw [ihBranch j tooHigh, mul_zero]
        · rw [adjacentMask_off A i j edge, zero_mul]
      rw [act, mul_zero]

/-- Every paid tree in the band has exactly the dense reference readout. -/
theorem readout_eq_on_band (F : Frames M lead D) (w : ι → K) (t : FiniteRootedTree)
    (ht : treeHeight t ≤ D) (ord : (t.order : ℕ) ≤ lead+D) :
    unrollWeights F w ⬝ᵥ Φ t (unrollMatrix F) = w ⬝ᵥ Φ t M := by
  let x : Band M lead D := ⟨Φ t M, Φ_mem_heightOrderSpace M t ht ord⟩
  let f : Module.Dual K (Band M lead D) := (row w).comp (Band M lead D).subtype
  have col : layerSlice (Φ t (unrollMatrix F)) (Fin.last D) =
      (F (Fin.last D)).restrictEquiv x := by
    funext j
    rw [layerSlice_apply, CoordinateFrame.restrictEquiv_apply]
    exact phi_agrees F t ⟨Fin.last D,j⟩ ht ord
  have read : layerSlice (unrollWeights F w) (Fin.last D) = (F (Fin.last D)).rowOver f := by
    funext j
    change (if Fin.last D = Fin.last D then (F (Fin.last D)).rowOver f j else 0) =
      (F (Fin.last D)).rowOver f j
    exact ite_eq_left rfl
  rw [dotProduct_eq_on_layer (unrollWeights F w) _ (Fin.last D) (unrollWeights_off F w),
    read, col]
  exact (F (Fin.last D)).row_rowOver f x

/-- An unrolled readout kills all taller trees, independently of order. -/
theorem readout_zero_of_height (F : Frames M lead D) (w : ι → K) (t : FiniteRootedTree)
    (high : D < treeHeight t) :
    unrollWeights F w ⬝ᵥ Φ t (unrollMatrix F) = 0 := by
  have zero : layerSlice (Φ t (unrollMatrix F)) (Fin.last D) = 0 := by
    funext j
    change Φ t (adjacentMask (rawRows F)) ⟨Fin.last D,j⟩ = 0
    exact phi_zero_above (rawRows F) t ⟨Fin.last D,j⟩ high
  rw [dotProduct_eq_on_layer (unrollWeights F w) _ (Fin.last D) (unrollWeights_off F w),
    zero, dotProduct_zero]

end

end RKResearch.FiniteSeries.RankUnroll
