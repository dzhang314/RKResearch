import RKCert.ReviewedNative.DIRKOrderElevenThirteenCubicRank

open RKResearch RKResearch.Certified.Graded RKResearch.Certified.Graded.OrderElevenThirteen
open scoped Matrix

variable {K : Type*} [Field K] {A : Matrix (Fin 13) (Fin 13) K} {b : Fin 13 → K}
variable (ha : A.IsLowerTriangular) (ho : HasOrder 11 A b) (N : Normalized A b)

example : RankCensus A b := rank_census ha ho N

example (nz : b*monomialStageDefect A 2≠0) :
    ∃ a : K, a≠0 ∧ reflectedStageRow A b 2 = a • (b*monomialStageDefect A 2) :=
  reflected_cubic_proportional ha ho N nz

example {i j : Fin 13} (hi : (b*monomialStageDefect A 2) i≠0)
    (hj : (b*monomialStageDefect A 2) j≠0) (diff : nodes A i≠nodes A j) :
    let w := b*monomialStageDefect A 2
    let f : Fin 2 → (Fin 13 → K) := Fin.cases (diag (nodes A) w) (fun _ => w)
    Submodule.span K (Set.range f) = Reverse.annih (treeSpace A 6) :=
  annih_six_eq_cubic_pair ha ho N hi hj diff

#print axioms rank_census
#print axioms reflected_cubic_proportional
#print axioms annih_six_eq_cubic_pair
