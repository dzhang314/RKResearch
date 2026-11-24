module
import RKCert.ReviewedNative.ERKOrder15EscapeMoments

open RKResearch RKResearch.Certified.Graded RKResearch.Certified.Graded.Reverse Polynomial
#check @order15_paid_frame
#check @order15_paid_head
#check @order15_first_escape_chart
#check @order15_first_escape_alias_line
#check @order15_escape_adjacent_packet
#print axioms terminalDebit_balance
#print axioms terminalMark_clock
#print axioms rank_sup_terminalMark
#print axioms last_coordinate_not_defect
#print axioms marked_defect_rank
#print axioms mark_paid_by_backward
#print axioms marked_tree_backward_room
#print axioms probe_terminalMark_equal
#print axioms paid_probe_marked_defect
#print axioms origin_marked_defect
#print axioms marked_coeff_separated
#print axioms eval_eq_zero_of_coeff_separated
#print axioms rank_coeff_sup_of_separated
#print axioms order15_short_last_active
#print axioms order15_paid_frame
#print axioms order15_paid_head
#print axioms order15_escape_separated_six
#print axioms order15_unmarked_escape_separated_seven
#print axioms order15_first_escape_chart_of_frame
#print axioms order15_first_escape_alias_line
#print axioms order15_first_escape_chart
#print axioms order15_escape_origin
#print axioms order15_escape_adjacent_packet
#print axioms order15_unmarked_escape_moments

/-- Public single-import witness combining the structural and scalar
payoff directly on the physical tableau. -/
example {K : Type*} [Field K] [CharZero K] {s : ℕ}
    {A : Matrix (Fin (s+1)) (Fin (s+1)) K} {b : Fin (s+1)→K}
    (ha : ∀ i j,i ≤ j → A i j=0) (ho : HasOrder 15 A b) (cap : s+1≤22) :
    ∃ (a : ℕ) (G D : K[X]), Order15FirstEscapeChart A b a G ∧ G=X*D ∧
      D.natDegree ≤ 7 ∧ RKCert.ReviewedNative.JacobiMoments.MomentDifferences D 5 := by
  obtain ⟨a,G,F,C⟩ := order15_first_escape_chart ha ho cap
  have d : G.natDegree≤8 := by
    rcases C.chartType with eq|⟨eq,_⟩ <;> have := C.degree <;> omega
  obtain ⟨D,e,h,m⟩ := order15_escape_adjacent_packet ha ho F G d C.paid
  exact ⟨a,G,D,C,e,h,m⟩
