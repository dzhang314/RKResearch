import RKCert.ReviewedNative.OneOffMaximal

open RKResearch RKResearch.Certified.Graded RKResearch.Certified.Graded.OneOff
open Module
open scoped Classical Matrix

#print axioms order9_forward_chart
#print axioms order9_constant_amplitude
#print axioms order9_receiver_order_two
#print axioms exists_merge_equal_rows
#print axioms global_normal_from_amplitude
#print axioms order9_global_normal
#print axioms order9_clean_clock_chain
#print axioms order9_no_identical_rows
#print axioms order9_first_four
#print axioms anchored_radau_span
#print axioms wide_kernel_poly
#print axioms order9_rank_five_full_terminal
#print axioms rank_five_full_terminal_defect
#print axioms order9_defects_separate
#print axioms normal_profile_rank_nine
#print axioms order9_fifth_feature
#print axioms order9_maximal_normal_profile
#print axioms order9_one_off_maximal_chart

-- The final native consumer needs no assumed shape, rank, or weights.
example {K : Type*} [Field K] [CharZero K]
    {A : Matrix (Fin 12) (Fin 12) K} {b : Fin 12 → K}
    (ha : ∀ i j, i ≤ j → A i j = 0) (ho : HasOrder 9 A b)
    (off : (offKnots A).card = 1) :
    finrank K (treeSpace A 5) = 10 ∧ b (Fin.last 11) ≠ 0 ∧
      nodes A (Fin.last 11) = 1 ∧ h A (Fin.last 11) = 0 := by
  obtain ⟨a,d,i,j,D,F,feat,full,_,_,_⟩ := order9_one_off_maximal_chart ha ho off
  obtain ⟨live,atOne,_,_⟩ := order9_rank_five_full_terminal ha ho full
  exact ⟨full,live,atOne,rank_five_full_terminal_defect ha ho full (h_in_grade_three A)⟩
