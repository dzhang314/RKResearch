import RKCert.ReviewedNative.ERKOrder13ReverseWindow
open Module RKResearch RKResearch.Certified.Graded RKResearch.Certified.Graded.Reverse
#check @explicit_order_thirteen_at_least_nineteen
#check @order13_paid_mesh
#check @order13_physical_staircase
#check @order13_reverse_window
#print axioms explicit_order_thirteen_at_least_nineteen
#print axioms order13_saturated_defects
#print axioms order13_paid_frame
#print axioms order13_paid_head
#print axioms order13_paid_mesh
#print axioms order13_first_mesh_of_frame
#print axioms order13_physical_staircase
#print axioms order13_reverse_window
#print axioms order13_marked_reverse_ranks

example {K : Type*} [Field K] [CharZero K] {A : Matrix (Fin 19) (Fin 19) K}
    {b : Fin 19 → K} (ha : ∀ i j,i≤j → A i j=0) (ho : RKResearch.HasOrder A b 13) :
    finrank K (markedTreeSpace A b 10)=17+terminalDebit A b :=
  order13_paid_high_ranks ha ho (j:=10) (by decide) (by decide)

example {K : Type*} [Field K] [CharZero K] {A : Matrix (Fin 19) (Fin 19) K}
    {b : Fin 19 → K} (ha : ∀ i j,i≤j → A i j=0) (ho : RKResearch.HasOrder A b 13) :
    back A b 1=annih (markedTreeSpace A b 10) :=
  (order13_reverse_window ha ho (by decide : 1≤1) (by decide)).1
