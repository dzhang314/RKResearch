module
public import RKCert.ReverseHermiteRank
public import RKCert.OrderTwelveStaircase

@[expose] public section
/-! # Exact E7–E9 propagation and backward annihilator chart at order twelve -/
namespace RKCert.Paired.OrderTwelve
open RKCert.Paired RKCert.Paired.ReverseHull Module
variable {K : Type*} [Field K] [CharZero K] {s : ℕ}

omit [CharZero K] in
/-- Actual strict growth of the tree columns along an escaping clock image. -/
theorem tree_rank_lt_of_clock_escape (A : Fin s → Fin s → K) (j : ℕ)
    (h : ¬(treeSpace A j).map (diag (nodes A))≤treeSpace A j) :
    finrank K (treeSpace A j)<finrank K (treeSpace A (j+1)) := by
  apply Submodule.finrank_lt_finrank_of_lt
  refine lt_of_le_of_ne (treeSpace_mono A (Nat.le_succ j)) ?_
  intro he
  apply h
  exact (Submodule.map_le_iff_le_comap.mpr (diag_treeSpace A j)).trans he.ge

/-- The only forward input beyond the saturated elementary chart is the rank-fourteen E7;
the active-stage proof of this input can be passed directly. -/
structure ReverseSevenNine (A : Fin (s+1) → Fin (s+1) → K) (b : Vec K (s+1)) : Prop where
  back3 : back A b 3=annih (treeSpace A 7)
  noninvariant7 : ¬(treeSpace A 7).map (diag (nodes A))≤treeSpace A 7
  rank8 : finrank K (treeSpace A 8)=15
  back2 : back A b 2=annih (treeSpace A 8)
  noninvariant8 : ¬(treeSpace A 8).map (diag (nodes A))≤treeSpace A 8
  rank9 : finrank K (treeSpace A 9)=16
  back1 : back A b 1=annih (treeSpace A 9)
  noninvariantBack2 : ¬(back A b 2).map (diag (mirror A))≤back A b 2
  noninvariantBack3 : ¬(back A b 3).map (diag (mirror A))≤back A b 3

theorem reverse_seven_nine_of_e7 {A : Fin (s+1) → Fin (s+1) → K} {b : Vec K (s+1)}
    (ha : StrictLower A) (ho : HasTreeOrderAtLeast A b 12) (hs : Saturation A b)
    (he : finrank K (treeSpace A 7)=14) : ReverseSevenNine A b := by
  have size := hs.size
  have r1 := hs.backRank 1 (by decide)
  have r2 := hs.backRank 2 (by decide)
  have r3 := hs.backRank 3 (by decide)
  have r4 := hs.backRank 4 (by decide)
  have b3 : back A b 3=annih (treeSpace A 7) := backward_exact_of_ranks ho (by decide) (by omega)
  have ni7 := not_invariant_of_reverse_rank_two ha ho 6 3 (by decide) b3 hs.back4 (by change finrank K (back A b 4)≤finrank K (back A b 3)+1; omega)
  have l8 := tree_rank_lt_of_clock_escape A 7 ni7
  have c8 := hs.caps 8 (by decide)
  have e8 : finrank K (treeSpace A 8)=15 := by change finrank K (treeSpace A 7)<finrank K (treeSpace A 8) at l8; omega
  have b2 : back A b 2=annih (treeSpace A 8) := backward_exact_of_ranks ho (by decide) (by omega)
  have ni8 := not_invariant_of_reverse_rank_two ha ho 7 2 (by decide) b2 b3 (by change finrank K (back A b 3)≤finrank K (back A b 2)+1; omega)
  have l9 := tree_rank_lt_of_clock_escape A 8 ni8
  have c9 := hs.caps 9 (by decide)
  have e9 : finrank K (treeSpace A 9)=16 := by change finrank K (treeSpace A 8)<finrank K (treeSpace A 9) at l9; omega
  have b1 : back A b 1=annih (treeSpace A 9) := backward_exact_of_ranks ho (by decide) (by omega)
  refine ⟨b3,ni7,e8,b2,ni8,e9,b1,?_,?_⟩
  · intro h
    have r := backward_invariant_rank_jump ha ho 7 2 (by decide) b2.le b3.ge h
    change finrank K (back A b 2)+2≤finrank K (back A b 3) at r
    omega
  · intro h
    have r := backward_invariant_rank_jump ha ho 6 3 (by decide) b3.le hs.back4.ge h
    change finrank K (back A b 3)+2≤finrank K (back A b 4) at r
    omega

/-- A saturated true order-twelve tableau has this rank chart, even if its last
physical weight vanishes: select the actual last active stage. -/
theorem reverse_seven_nine {A : Fin (s+1) → Fin (s+1) → K} {b : Vec K (s+1)}
    (ha : StrictLower A) (ho : HasTreeOrderAtLeast A b 12) (hs : Saturation A b) :
    ReverseSevenNine A b := by
  obtain ⟨i,hi,hl⟩ := exists_last_weight ho (by decide)
  exact reverse_seven_nine_of_e7 ha ho hs (e7_rank ha ho hs hi hl)

end RKCert.Paired.OrderTwelve
