module
import RKCert.ReviewedNative.DIRKUniform

open RKResearch
universe u

section Consumer
variable {R : Type u} [CommRing R] [Nontrivial R] {p s : ℕ}
variable {A : Matrix (Fin s) (Fin s) R} {b : Fin s → R}
variable (ha : A.IsLowerTriangular)

example (h : HasOrder p A b) : dirkUniformFloor p ≤ s :=
  h.dirk_uniform_floor_le_stages ha

example (h : HasOrder 6 A b) : 5 ≤ s := h.dirk_uniform_stages ha (by decide)
example (h : HasOrder 7 A b) : 7 ≤ s := h.dirk_order_seven_stages ha
example (h : HasOrder 8 A b) : 8 ≤ s := h.dirk_order_eight_stages ha
example (h : HasOrder 9 A b) : 10 ≤ s := h.dirk_uniform_stages ha (by decide)
example (h : HasOrder 10 A b) : 11 ≤ s := h.dirk_uniform_stages ha (by decide)
example (h : HasOrder 11 A b) : 13 ≤ s := h.dirk_uniform_stages ha (by decide)
example (h : HasOrder p A b) (hp : 7 ≤ p) : 7 ≤ s :=
  (show HasOrder 7 A b from fun t ht => h t (ht.trans hp)).dirk_order_seven_stages ha
end Consumer

#check RKResearch.HasOrder.dirk_uniform_stages
#check RKResearch.HasOrder.dirk_order_seven_stages
#check RKResearch.HasOrder.dirk_order_eight_stages
#print axioms RKResearch.Certified.Graded.Reverse.dirk_primitiveBack_lt_succ
#print axioms RKResearch.Certified.Graded.Reverse.dirk_primitiveBack_rank_gain
#print axioms RKResearch.Certified.Graded.Reverse.dirk_terminal_rank_budget
#print axioms RKResearch.Certified.Graded.Reverse.dirk_two_ended_stage_count
#print axioms RKResearch.HasOrder.dirk_uniform_stages_field
#print axioms RKResearch.HasOrder.dirk_uniform_stages
#print axioms RKResearch.HasOrder.dirk_order_seven_stages
#print axioms RKResearch.HasOrder.dirk_order_eight_stages
#print axioms RKResearch.HasOrder.dirk_uniform_floor_le_stages
#print axioms RKResearch.dirkUniformFloor_through_twenty
