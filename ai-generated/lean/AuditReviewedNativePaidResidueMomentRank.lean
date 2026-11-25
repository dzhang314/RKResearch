import RKCert.ReviewedNative.PaidResidueMomentRank

/-! Standalone typed audit of the literal stock-only residue rank API. -/
open Polynomial
open RKResearch.Certified.Graded.ResidueMomentRank
open scoped Classical Matrix

section
variable {K ι : Type*} [Field K] [Fintype ι]
variable {S : Finset K} {w : K → ι → K} {d : ℕ}

example (paid : ∀ (i : ι) (P : K[X]), P.natDegree ≤ d →
    (∑ x ∈ S, P.eval x * w x i) = 0) :
    min S.card (d+1) + Module.finrank K (LinearMap.range
      (Matrix.mulVecLin (show Matrix (↥S) ι K from fun x i => w x.1 i))) ≤ S.card :=
  min_add_residueRank_le_card (show PaidMoments S w d from paid)

example (paid : PaidMoments S w d) (b : ι) (P : K[X]) (degree : P.natDegree ≤ d) :
    (∑ x ∈ activeFibres S w, P.eval x * w x b) = 0 :=
  paidMoments_active paid b P degree

example {x : K} {i : ι} (hx : x ∈ S) (entry : w x i ≠ 0) :
    0 < residueRank S w :=
  residueRank_pos_of_entry hx entry

example (paid : PaidMoments S w d) (pos : 0 < residueRank (activeFibres S w) w) :
    d+1+residueRank (activeFibres S w) w ≤ (activeFibres S w).card :=
  active_card_of_paid_rank_pos paid pos

end

section
variable {K : Type*} [Field K] {S : Finset K} {v : K → Fin 2 → K} {d : ℕ}

example (paid : ∀ (b : Fin 2) (P : K[X]), P.natDegree ≤ d →
    (∑ x ∈ S, P.eval x * v x b) = 0) {x : K} {b : Fin 2}
    (hx : x ∈ S) (entry : v x b ≠ 0) :
    d+1+residueRank (activeFibres S v) v ≤ (activeFibres S v).card :=
  active_card_of_paid_nonzero_entry (show PaidMoments S v d from paid) hx entry

end

#print axioms RKResearch.Certified.Graded.ResidueMomentRank.min_add_residueRank_le_card
#print axioms RKResearch.Certified.Graded.ResidueMomentRank.paidMoments_active
#print axioms RKResearch.Certified.Graded.ResidueMomentRank.residueRank_pos_of_entry
#print axioms RKResearch.Certified.Graded.ResidueMomentRank.active_card_of_paid_rank_pos
#print axioms RKResearch.Certified.Graded.ResidueMomentRank.active_card_of_paid_nonzero_entry
