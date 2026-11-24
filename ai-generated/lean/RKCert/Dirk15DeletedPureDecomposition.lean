module

public import RKCert.Dirk15DeletedScalarReduction

@[expose] public section

/-! # A true pure lift for each deleted head decomposition

Every scalar component is constrained by the original all-tree pairings,
with the terminal killed by the single factor 1-X. The numerical
decomposition never assumes any original weight is nonzero off the terminal.
-/
namespace RKCert.Paired
open Module Polynomial RKCert.OneEscape RKCert.Endpoint
open scoped Classical
noncomputable section
variable {K : Type*} [Field K] [CharZero K]
variable {A : Fin 20 → Fin 20 → K} {b : Vec K 20}

namespace Order15MinimalHead
variable (h : Order15MinimalHead A b)

omit [CharZero K] in
theorem chain_genuine {j : ℕ} (lo : 7≤j) :
    chain (diag (nodes A)) h.U h.w (h.length+(j-7))≤zeroSpace A j := by
  let T := diag (nodes A)
  let C := chain T h.U h.w
  have core (k : ℕ) : C (h.length+k)≤zeroSpace A (7+k) := by
    induction k with
    | zero => exact h.seven.ge
    | succ k ih =>
      have s : C (h.length+k)⊔(C (h.length+k)).map T=C (h.length+k+1) :=
        chain_sup_map h.maximal.2.1 (by have := h.length_pos; omega)
      change C (h.length+k+1)≤zeroSpace A (7+k+1)
      rw [←s]
      exact sup_le (ih.trans (zeroSpace_mono A (by omega)))
        (Submodule.map_le_iff_le_comap.mpr (ih.trans (diag_zeroSpace A (7+k))))
  have e := core (j-7)
  rwa [Nat.add_sub_of_le lo] at e

/-- If both scalar and head parts fit the true grade budget, the scalar
part of any pure column satisfies the endpoint-weighted moment tests. -/
theorem pure_parts (ho : HasTreeOrderAtLeast A b 15) (H : Order15MinimalMarkedChart A b)
    {j q n : ℕ} (lo : 7≤j) (qj : q≤j) (nj : n≤h.length+(j-7))
    (shape : deletedTreeSpace A j=deletedScalarOrbit A q⊔deletedHeadOrbit A h.U h.w n)
    {x : Vec K 20} (hx : x∈zeroSpace A j) :
    ∃ P : K[X], P.natDegree≤q ∧ P.eval 0=0 ∧
      (∀ Q : K[X],j+Q.natDegree+2≤15 → unitIntegral (P*((1-X)*Q))=0) ∧
      ∃ t∈chain (diag (nodes A)) h.U h.w n,
        deleteTerminal K 19 x=deleteTerminal K 19 (evalNodes A P+t) := by
  have hm : deleteTerminal K 19 x∈deletedTreeSpace A j :=
    Submodule.mem_map_of_mem (zeroSpace_le_treeSpace A j hx)
  rw [shape,deletedHeadOrbit_eq] at hm
  obtain ⟨p,hp,z,hz,eq⟩ := Submodule.mem_sup.mp hm
  obtain ⟨P,dP,rfl⟩ := deletedScalarOrbit_decompose hp
  obtain ⟨v,hv,rfl⟩ := hz
  have vj : v∈zeroSpace A j := h.chain_genuine lo (clock_chain_mono nj hv)
  have rel : deleteTerminal K 19 (evalNodes A P)=deleteTerminal K 19 (x-v) := by
    rw [map_sub,←eq,add_sub_cancel_right]
  have pay := deleted_scalar_pure_tests ho H (dP.trans qj) ((zeroSpace A j).sub_mem hx vj) rel
  exact ⟨P,dP,pay.1,pay.2,v,hv,(by rw [map_add]; exact eq.symm)⟩

end Order15MinimalHead
end
end RKCert.Paired
