module
import RKCert.ReviewedNative.ERKOrder15Staircase

open RKResearch RKResearch.Certified.Graded RKResearch.Certified.Graded.Reverse Polynomial Module
#check @marked_clock_invariant_debit
#check @order15_grade7_clock_debit
#check @order15_physical_staircase
#check @order15_marked_high_ranks
#print axioms primitive_mark_paid
#print axioms primitiveBack_le_marked_annih
#print axioms primitiveBack_eq_marked_annih_of_rank
#print axioms marked_annih_reflected_stable
#print axioms marked_clock_invariant_debit
#print axioms marked_tree_clock_le
#print axioms order15_marked_clock_debit
#print axioms order15_grade7_clock_debit
#print axioms order15_grade7_clock_escapes
#print axioms order15_paid_clock_step
#print axioms order15_paid_staircase_of_first
#print axioms order15_physical_staircase
#print axioms order15_marked_high_ranks

/-- A single public import yields the actual final rank and the unchanged
shared arithmetic packet; no arithmetic theorem is applied here. -/
example {K : Type*} [Field K] [CharZero K] {s : ℕ}
    {A : Matrix (Fin (s+1)) (Fin (s+1)) K} {b : Fin (s+1)→K}
    (ha : ∀ i j,i ≤ j → A i j=0) (ho : HasOrder 15 A b) (cap : s+1≤22) :
    finrank K (markedTreeSpace A b 12)=20+terminalDebit A b ∧
      ∃ (a : ℕ) (G D : K[X]), Order15FirstEscapeChart A b a G ∧ G=X*D ∧
        D.natDegree≤7 ∧ RKCert.ReviewedNative.JacobiMoments.MomentDifferences D 5 := by
  obtain ⟨a,G,r,U,w,S⟩ := order15_physical_staircase ha ho cap
  have pd : G.natDegree≤8 := by
    rcases S.first.chartType with eq|⟨eq,_⟩ <;> have := S.first.degree <;> omega
  obtain ⟨D,e,d,m⟩ := order15_escape_adjacent_packet ha ho S.frame G pd S.first.paid
  exact ⟨order15_marked_high_ranks ha ho cap (j:=12) (by decide) (by decide),
    a,G,D,S.first,e,d,m⟩
