import RKCert.ReviewedNative.ERKOrder13MarkedEndpoint

open RKResearch RKResearch.Certified.Graded RKResearch.Certified.Graded.Reverse

#print axioms order13_marked_reverse_first_escapes
#print axioms order13_marked_grade_eleven

example {K : Type*} [Field K] [CharZero K]
    {A : Matrix (Fin 19) (Fin 19) K} {b : Fin 19 → K}
    (ha : ∀ i j, i ≤ j → A i j = 0) (ho : RKResearch.HasOrder A b 13)
    (seedZero : firstSeed A b = 0) :
    markedTreeSpace A b 11 = ⊤ ∧
    markedTreeSpace A b 11 = markedTreeSpace A b 10 ⊔
      (markedTreeSpace A b 10).map (diag (nodes A)) :=
  order13_marked_grade_eleven ha ho seedZero
