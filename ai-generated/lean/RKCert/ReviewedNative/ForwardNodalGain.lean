module

public import RKCert.ReviewedNative.ClockBlockDetection
public import RKCert.ReviewedNative.OrderedNodalGain

@[expose] public section

/-! # Clock-invariant gain inside native reviewed defect spaces

The Hermite rank lemma is pure linear algebra on a finite ordered index set:
its import closure contains neither a rooted-tree type nor an RK order predicate.
To connect it to the actual tableau, use polynomial separation itself to count
failed node blocks. No positivity, selected abscissae, or aggregate-mass
assumption enters. -/
namespace RKResearch.Certified.Graded

open RKResearch Polynomial Module
open RKCert.Endpoint
open scoped Classical

variable {K : Type*} [Field K] {s j : ℕ} {A : Matrix (Fin s) (Fin s) K}

private theorem strict_nodal_mat (ha : ∀ i k, i ≤ k → A i k=0) :
    StrictlyCausal (mat A) := by
  intro i x y pre
  have z := causal_mat ha i (x-y) (fun k hk => sub_eq_zero.mpr (pre k hk))
  simpa only [map_sub,Pi.sub_apply,sub_eq_zero] using z

/-- If fewer than j clock blocks failed to match the constant column,
their nodal polynomial multiplied by X would lift into this actual defect
space, contradicting native degree-j separation. -/
theorem failed_nodes_of_separation (sep : PolySeparated A j)
    {U : Submodule K (Fin s → K)} (sub : U ≤ zeroSpace A j)
    (hm : MaskInvariant (nodes A) U) :
    j ≤ (failedNodes (nodes A) 1 U s).card := by
  by_contra! small
  let S := failedNodes (nodes A) (1 : Fin s→K) U s
  let P : K[X] := X*nodalHull S
  have nz : P ≠ 0 := (monic_X.mul (monic_nodalHull S)).ne_zero
  have deg : P.natDegree ≤ j := by
    rw [show P=X*nodalHull S from rfl,natDegree_X_mul (monic_nodalHull S).ne_zero,natDegree_nodalHull]
    exact Nat.succ_le_of_lt small
  obtain ⟨w,hw,h⟩ := exists_masked_prefix_lift (nodes A) (1 : Fin s→K) hm s P
    (by simp [P]) (fun x hx=>by simp [P,nodalHull_eval_of_mem (S:=S) hx])
  have eq : w=evalNodes A P := by
    ext i
    simpa only [Pi.one_apply,mul_one,evalNodes_apply] using h i i.isLt
  exact nz (sep P deg (sub (eq ▸ hw)))

private theorem hermite_eval (A : Matrix (Fin s) (Fin s) K) (P : K[X]) :
    weightedEval (nodes A) 1 P = evalNodes A P := by
  ext i
  simp

/-- Outgoing cost of any clock-stable portion of the native homogeneous
defect space. Only native degree-j separation is required. -/
theorem clock_invariant_outgoing [CharZero K] (ha : ∀ i k, i ≤ k → A i k=0)
    (sep : PolySeparated A j) {U : Submodule K (Fin s → K)}
    (sub : U ≤ zeroSpace A j) (stable : U.map (diag (nodes A)) ≤ U) :
    finrank K U + (j+1)/2 ≤ finrank K (zeroSpace A (j+1)) := by
  have hm := clock_mask_invariant (fun _ hv => stable (Submodule.mem_map_of_mem hv))
  apply ordered_hermite_outgoing (Equiv.refl _) (mat A) (causal_mat ha) (nodes A) 1 U (zeroSpace A (j+1))
    hm (sub.trans (zeroSpace_mono A (Nat.le_succ j)))
    (fun _ h => mat_zeroSpace_charZero A j (sub h))
  · exact (show (j+1)/2≤j by omega).trans (failed_nodes_of_separation sep sub hm)
  · intro P hP
    rw [hermite_eval,hermite_eval]
    exact primitive_defect A P (by omega)

/-- Incoming cost when the higher defect space is clock-stable; the lower
space need not itself be stable. -/
theorem clock_invariant_incoming [CharZero K] (ha : ∀ i k, i ≤ k → A i k=0)
    (sep : PolySeparated A (j+1))
    (stable : (zeroSpace A (j+1)).map (diag (nodes A)) ≤ zeroSpace A (j+1)) :
    finrank K (zeroSpace A j) + (j+1)/2 ≤ finrank K (zeroSpace A (j+1)) := by
  have hm := clock_mask_invariant (fun _ hv => stable (Submodule.mem_map_of_mem hv))
  apply incoming_nodal_gain (nodes A) 1 (zeroSpace A j) (zeroSpace A (j+1)) (mat A)
    (strict_nodal_mat ha) hm (zeroSpace_mono A (Nat.le_succ j))
    (fun _ h=>mat_zeroSpace_charZero A j h)
  · exact (show (j+1)/2≤j+1 by omega).trans (failed_nodes_of_separation sep le_rfl hm)
  · intro P hP
    rw [hermite_eval,hermite_eval,formalPrimitive_eq_native]
    exact primitive_defect A P (by omega)

end RKResearch.Certified.Graded
