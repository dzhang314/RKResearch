module
import RKCert.ReviewedNative.ERKOrder15ForwardEdge

open RKResearch.Certified.Graded
#check @order15_clock_escapes
#check @order15_head_of_grade_five
#check @ordered_hermite_outgoing
#print axioms clock_chain_le_iff
#print axioms clock_chain_next
#print axioms zeroSpace_clock_step_of_unit
#print axioms formalPrimitive_eq_native
#print axioms ordered_hermite_outgoing
#print axioms failed_nodes_of_separation
#print axioms clock_invariant_outgoing
#print axioms clock_invariant_incoming
#print axioms order15_clock_escapes
#print axioms order15_head_of_grade_five

/-- Compile an independent consumer using only this public entrance. -/
example {K : Type*} [Field K] [CharZero K] {n : ℕ}
    {A : Matrix (Fin n) (Fin n) K} {b : Fin n → K}
    (hA : ∀ i k, i ≤ k → A i k=0) (ho : RKResearch.HasOrder 15 A b)
    (hs : n ≤ 22) :
    ∃ x ∈ zeroSpace A 7, diag (nodes A) x ∉ zeroSpace A 7 := by
  by_contra! all
  exact order15_clock_escapes hA ho hs (j:=7) (by decide) (by decide)
    (Submodule.map_le_iff_le_comap.mpr (fun x hx=>all x hx))
