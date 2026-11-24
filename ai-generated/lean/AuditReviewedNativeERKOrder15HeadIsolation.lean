module
import RKCert.ReviewedNative.ERKOrder15LargeHeadFactor

open RKResearch RKResearch.Certified.Graded RKResearch.Certified.Graded.Reverse Polynomial Module
#check @Order15PaidStaircase.ten_leak_free_all
#check @Order15PaidStaircase.clean_head
#check @Order15PaidStaircase.large_head_factor
#check @order15_alias_terminal_eight
#print axioms chargedProbe_clock
#print axioms chargedProbe_paid
#print axioms charged_coeff_separated
#print axioms charged_polynomial_separated
#print axioms extend_charged_probe_window
#print axioms clock_chain_rank_le
#print axioms Order15PaidStaircase.base_degree
#print axioms Order15PaidStaircase.band_direct_rank
#print axioms Order15PaidStaircase.band_separated
#print axioms Order15PaidStaircase.band_next
#print axioms Order15PaidStaircase.mesh_in_band
#print axioms Order15PaidStaircase.band_paid
#print axioms order15_alias_terminal_eight
#print axioms order15_absent_terminal_grade_eight_rigid
#print axioms Order15PaidStaircase.ten_poly_decompose
#print axioms Order15PaidStaircase.ten_leak_free_all
#print axioms Order15PaidStaircase.ten_leak_free
#print axioms marked_defect_mul
#print axioms Order15PaidStaircase.ten_has_escape_sites
#print axioms Order15PaidStaircase.core_times_five
#print axioms Order15PaidStaircase.clean_head
#print axioms Order15PaidStaircase.large_head_profile
#print axioms Order15PaidStaircase.large_head_factor

/-- No assumed rank or scalar mesh in this actual disjoint-head consumer. -/
example {K : Type*} [Field K] [CharZero K] {s : ℕ}
    {A : Matrix (Fin (s+1)) (Fin (s+1)) K} {b : Fin (s+1)→K}
    (ha : ∀ i j,i ≤ j → A i j=0) (ho : HasOrder 15 A b) (cap : s+1≤22) :
    ∃ (a : ℕ) (G : K[X]) (r : ℕ) (U : Submodule K (Fin (s+1)→K)) (v : Fin (s+1)→K),
      Order15PaidStaircase A b a G r U v ∧ (∀ i, (∃ u∈U,u i≠0) → v i=0) ∧
        (∀ u∈U,∀ z∈U,u*z∈U) := by
  obtain ⟨a,G,r,U,w,S⟩ := order15_physical_staircase ha ho cap
  obtain ⟨v,C,dis,closed⟩ := S.clean_head ha ho
  exact ⟨a,G,r,U,v,C,dis,closed⟩
