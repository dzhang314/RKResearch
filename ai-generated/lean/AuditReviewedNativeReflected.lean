import RKCert.ReviewedNative.ReflectedMoments

open RKResearch RKResearch.Certified.Graded
open scoped Matrix

#print axioms RKResearch.Certified.Graded.reflectedProbe_succ_right
#print axioms RKResearch.Certified.Graded.reflectedProbe_norm_shift
#print axioms RKResearch.Certified.Graded.reflectedProbe_unary_eq_clock
#print axioms RKResearch.Certified.Graded.reflectedStageRow_pair
#print axioms RKResearch.Certified.Graded.reflectedStageRow_normTree
#print axioms RKResearch.Certified.Graded.reflectedStageRow_Φ
#print axioms RKResearch.Certified.Graded.reflectedStageRow_treeSpace

-- The three physical reverse seeds paid by exact order six.
example {R : Type*} [CommRing R] {s : ℕ}
    {A : Matrix (Fin s) (Fin s) R} {b : Fin s → R} (h : HasOrder A b 6) :
    treeSpace A 4 ≤ (row (reflectedStageRow A b 0)).ker ∧
    treeSpace A 3 ≤ (row (reflectedStageRow A b 1)).ker ∧
    treeSpace A 2 ≤ (row (reflectedStageRow A b 2)).ker :=
  ⟨reflectedStageRow_treeSpace h 4 0 (by decide),
    reflectedStageRow_treeSpace h 3 1 (by decide), reflectedStageRow_treeSpace h 2 2 (by decide)⟩

-- Order fifteen pays the seventh reverse seed even on the full grade-seven space.
example {R : Type*} [CommRing R] {s : ℕ}
    {A : Matrix (Fin s) (Fin s) R} {b x : Fin s → R} (h : HasOrder A b 15)
    (hx : x ∈ treeSpace A 7) : (reflectedStageRow A b 6) ⬝ᵥ x = 0 :=
  reflectedStageRow_treeSpace h 7 6 (by decide) hx
