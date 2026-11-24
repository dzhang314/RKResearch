import RKCert.ReviewedNative.ERKOrder16PaidFrame
open RKResearch Module RKResearch.Certified.Graded RKResearch.Certified.Graded.Reverse
open RKResearch.Certified.ERK16

example {K : Type*} [Field K] [LinearOrder K] [IsStrictOrderedRing K]
    {s : ℕ} {A : Matrix (Fin s) (Fin s) K} {w : Fin s → K}
    (hA : ∀ i j, i ≤ j → A i j = 0) (ho : HasOrder A w 16) :
    24 ≤ s := ordered_stage_floor24 hA ho

example {K : Type*} [Field K] [LinearOrder K] [IsStrictOrderedRing K]
    {A : Matrix (Fin 24) (Fin 24) K} {w : Fin 24 → K}
    (hA : ∀ i j, i ≤ j → A i j = 0) (ho : HasOrder A w 16) :
    firstSeed A w = 0 ∧ nodes A (Fin.last 23) = 1 ∧
      primitiveBack A w 6 = annih (treeSpace A 8) := by
  let h := width24_paid_frame hA ho
  exact ⟨h.seedZero,h.lastClock,h.full⟩

#print axioms RKResearch.Certified.ERK16.ordered_stage_budget
#print axioms RKResearch.Certified.ERK16.ordered_stage_floor24
#print axioms RKResearch.Certified.ERK16.ordered_stage_floor25_of_nonzero_first
#print axioms RKResearch.Certified.ERK16.width24_paid_frame
