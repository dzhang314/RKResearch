module

public import RKCert.ReviewedNative.ERKGradeEightSurplus
public import RKCert.ReviewedNative.ERKUniform

@[expose] public section

/-! # The exact ordered order-16 payoff of the native grade-eight surplus

A nonzero output vector does not pay the initial reverse-seed rank.
The remaining width-24 case has zero first seed and an exact terminal
horizon; no unconditional 25-stage conclusion is asserted. -/
namespace RKResearch.Certified.ERK16
open RKResearch Module RKResearch.Certified.Graded RKResearch.Certified.Graded.Reverse

variable {K : Type*} [Field K] [LinearOrder K] [IsStrictOrderedRing K]
variable {s : ℕ} {A : Matrix (Fin s) (Fin s) K} {b : Fin s → K}

theorem ordered_stage_budget (ha : ∀ i j, i≤j → A i j=0) (ho : HasOrder A b 16) :
    24+finrank K (back A b 0) ≤ s := by
  have front := grade_eight_surplus_ordered_of_reviewed_order ha ho le_rfl
  have budget := erk_even_midpoint_budget ha ho (q:=8) (by decide) (by decide)
  change 15+finrank K (zeroSpace A 8)+finrank K (back A b 0) ≤ s at budget
  omega

theorem ordered_stage_floor24 (ha : ∀ i j, i≤j → A i j=0) (ho : HasOrder A b 16) :
    24≤s := (Nat.le_add_right 24 _).trans (ordered_stage_budget ha ho)

theorem ordered_stage_floor25_of_nonzero_first (ha : ∀ i j, i≤j → A i j=0)
    (ho : HasOrder A b 16) (hn : firstSeed A b≠0) : 25≤s := by
  have h := ordered_stage_budget ha ho
  rw [first_dim_one hn] at h
  exact h

structure Width24PaidFrame (T : Matrix (Fin 24) (Fin 24) K) (w : Fin 24 → K) : Prop where
  forward : finrank K (zeroSpace T 8)=9
  tree : finrank K (treeSpace T 8)=18
  lastLive : LastActive w (Fin.last 23)
  lastClock : nodes T (Fin.last 23)=1
  seedZero : firstSeed T w=0
  lastIn : coordinate (K:=K) (Fin.last 23)∈treeSpace T 8
  lastOut : coordinate (K:=K) (Fin.last 23)∉treeSpace T 7
  full : primitiveBack T w 6=annih (treeSpace T 8)
  flagExact : ∀ n ≤ 6, finrank K (back T w n)=n ∧ back T w n=primitiveBack T w n

set_option maxRecDepth 3500 in
set_option maxHeartbeats 600000 in
theorem width24_paid_frame {T : Matrix (Fin 24) (Fin 24) K} {w : Fin 24 → K}
    (ha : ∀ i j, i≤j → T i j=0) (ho : HasOrder T w 16) : Width24PaidFrame T w := by
  have lower := grade_eight_surplus_ordered_of_reviewed_order ha ho le_rfl
  have cap := erk_even_midpoint_budget ha ho (q:=8) (by decide) (by decide)
  change 15+finrank K (zeroSpace T 8)+finrank K (back T w 0) ≤ 24 at cap
  have d8 : finrank K (zeroSpace T 8)=9 := by omega
  have tree : finrank K (treeSpace T 8)=18 := by
    rw [erk_midpoint_tree_rank ha ho (q:=8) (by decide) (by decide),d8]
  have live : LastActive w (Fin.last 23) := by
    refine ⟨?_,fun i h => (not_lt_of_ge (Fin.le_last i) h).elim⟩
    intro vanish
    have d : 23≤24 := by decide
    have tail (i : Fin 24) (h : (23 : ℕ) ≤ i.val) : w i=0 := by
      have eq : i=Fin.last 23 := Fin.ext (by have := i.isLt; change i.val=23; omega)
      exact eq.symm ▸ vanish
    exact (by decide : ¬24≤23) (ordered_stage_floor24 (prefix_strict_lower ha d)
      (prefix_hasOrder_of_suffix_zero ha ho d tail))
  obtain ⟨zero,one,_,tail⟩ := reverse_capacity_terminal ha ho (j:=8) (n:=6)
    (by decide) (by omega) live
  obtain ⟨_,_,full⟩ := reverse_capacity_paid ha ho (j:=8) (n:=6) (by decide) (by omega)
  have d6 : finrank K (primitiveBack T w 6)=6 := by
    rw [full]
    have all := finrank_annih (treeSpace T 8)
    rw [Fintype.card_fin,tree] at all
    omega
  have flags (n : ℕ) (hn : n≤6) : finrank K (back T w n)=n ∧ back T w n=primitiveBack T w n := by
    have x := primitiveBack_interval ha ho n (6-n) (by omega)
    rw [show n+(6-n)=6 by omega,d6] at x
    have y := back_finrank ha ho n (by omega)
    rw [first_dim_zero zero,zero_add] at y
    have z := Submodule.finrank_mono (back_le_primitiveBack (A:=T) (b:=w) n)
    exact ⟨by omega,Submodule.eq_of_le_of_finrank_le (back_le_primitiveBack n) (by omega)⟩
  exact ⟨d8,tree,live,one,zero,tail _ le_rfl,
    endpoint_coordinate_out ha ho (q:=7) (by decide) _ live.live one,full,flags⟩

end RKResearch.Certified.ERK16
