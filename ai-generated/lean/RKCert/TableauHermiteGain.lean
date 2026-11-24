module
public import RKCert.NodalHermiteRank
public import RKCert.CauchyKnots
public import RKCert.NodeCompletion

@[expose] public section

/-! # Actual forward Hermite rank for Runge--Kutta tableaux
Only explicit lower-triangularity, all-tree order, the indicated grade budget,
and node invariance of the chosen subspace are assumed. Detected nodes,
prefix lifts, formal primitive defects and the entire gain are derived. -/
namespace RKCert.Endpoint
open RKCert.Paired
open Polynomial
open scoped Classical
variable {K : Type*} [Field K] [CharZero K] {s p : ℕ}

omit [CharZero K] in
/-- Exact compatibility between two independently constructed formal primitive APIs. -/
theorem formalPrimitive_eq_treePrimitive (P : K[X]) : formalPrimitive P = Paired.primitive P := by
  change (∑ i ∈ P.support, monomial (i+1) (P.coeff i / (i+1:K))) =
    ∑ i ∈ P.support, monomial (i+1) (P.coeff i / ((i+1:ℕ):K))
  simp

omit [CharZero K] in
theorem strictlyCausal_mat {A : Fin s → Fin s → K} (ha : StrictLower A) : StrictlyCausal (mat A) := by
  intro i u w hp
  have hh := causal_mat ha i (u-w) (fun j hj => by
    change u j - w j=0
    exact sub_eq_zero.mpr (hp j hj))
  simpa only [map_sub,Pi.sub_apply,sub_eq_zero] using hh

omit [CharZero K] in
theorem maskInvariant_of_diag {A : Fin s → Fin s → K} {U : Submodule K (Vec K s)}
    (hC : ∀ v∈U, diag (nodes A) v∈U) : MaskInvariant (nodes A) U := by
  intro a v hv
  have eq : blockMask (nodes A) a v=diag (nodeMask A a) v := by
    ext i; by_cases h : nodes A i=a <;> simp [blockMask,mask_apply,h]
  rw [eq]; exact nodeMask_mem hC a hv

omit [CharZero K] in
private theorem weightedEval_one (A : Fin s → Fin s → K) (P : K[X]) :
    weightedEval (nodes A) 1 P = evalNodes A P := by ext i; simp

omit [CharZero K] in
/-- Every nonzero node with nonzero net output weight detects the constant
column on its full block, despite arbitrary repeated nodes and signed weights. -/
theorem activeNodes_detect {A : Fin s → Fin s → K} {b : Vec K s}
    (ho : HasTreeOrderAtLeast A b p) {j : ℕ} (hj : j+1≤p)
    {U : Submodule K (Vec K s)} (hUF : U≤zeroSpace A j)
    (hmask : MaskInvariant (nodes A) U) :
    activeNonzero (nodes A) b ⊆ failedNodes (nodes A) 1 U s := by
  classical
  intro a ha
  obtain ⟨_,han,hnet⟩ := Finset.mem_filter.mp ha
  apply mem_failedNodes.mpr
  refine ⟨han,fun ⟨v,hv,hm⟩ => hnet ?_⟩
  have hh : probe A b 0 (blockMask (nodes A) a v)=0 :=
    probe_zeroSpace ho (by omega : 0+j+1≤p) (hUF (hmask a v hv))
  have eq : probe A b 0 (blockMask (nodes A) a v) = combinedMass (nodes A) b a := by
    simp only [probe,row_apply,pow_zero,mul_one,combinedMass,Finset.sum_filter]
    apply Finset.sum_congr rfl
    intro i _
    by_cases hc : nodes A i=a
    · simp [blockMask,hc,hm i i.isLt hc]
    · simp [blockMask,hc]
  rwa [eq] at hh

/-- For actual tableau defects and *any* C-invariant subspace U⊆F_j, exact
classical order through p≥j+1 forces the outgoing floor((j+1)/2) gain. -/
theorem forward_invariant_hermite_rank {A : Fin s → Fin s → K} {b : Vec K s}
    (ha : StrictLower A) (ho : HasTreeOrderAtLeast A b p) {j : ℕ} (hj : j+1≤p)
    (U : Submodule K (Vec K s)) (hUF : U≤zeroSpace A j)
    (hC : ∀ v∈U, diag (nodes A) v∈U) :
    Module.finrank K U + (j+1)/2 ≤ Module.finrank K (zeroSpace A (j+1)) := by
  have hmask := maskInvariant_of_diag hC
  apply outgoing_nodal_gain (nodes A) (1 : Vec K s) U (zeroSpace A (j+1)) (mat A)
    (strictlyCausal_mat ha) hmask (hUF.trans (zeroSpace_mono A (Nat.le_succ j)))
    (fun v hv => mat_zeroSpace_charZero A j (hUF hv))
  · have h1 := activeNonzero_card_of_treeOrder ho
    have h2 := Finset.card_le_card (activeNodes_detect ho hj hUF hmask)
    omega
  · intro P hP
    rw [weightedEval_one,weightedEval_one,formalPrimitive_eq_treePrimitive]
    exact primitive_defect A P (by omega)

/-- If the HIGHER actual defect space itself is C-invariant, one obtains
the full incoming gain as well. The order budget is stated at grade j+1. -/
theorem forward_invariant_incoming_rank {A : Fin s → Fin s → K} {b : Vec K s}
    (ha : StrictLower A) (ho : HasTreeOrderAtLeast A b p) {j : ℕ} (hj : j+2≤p)
    (hC : ∀ v∈zeroSpace A (j+1), diag (nodes A) v∈zeroSpace A (j+1)) :
    Module.finrank K (zeroSpace A j) + (j+1)/2 ≤ Module.finrank K (zeroSpace A (j+1)) := by
  have hmask := maskInvariant_of_diag hC
  apply incoming_nodal_gain (nodes A) (1 : Vec K s) (zeroSpace A j) (zeroSpace A (j+1)) (mat A)
    (strictlyCausal_mat ha) hmask (zeroSpace_mono A (Nat.le_succ j))
    (fun v hv => mat_zeroSpace_charZero A j hv)
  · have h1 := activeNonzero_card_of_treeOrder ho
    have h2 := Finset.card_le_card (activeNodes_detect ho hj (le_refl (zeroSpace A (j+1))) hmask)
    omega
  · intro P hP
    rw [weightedEval_one,weightedEval_one,formalPrimitive_eq_treePrimitive]
    exact primitive_defect A P (by omega)

end RKCert.Endpoint
