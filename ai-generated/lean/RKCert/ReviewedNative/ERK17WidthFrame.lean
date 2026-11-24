module

public import RKCert.ReviewedNative.OddForwardBudget
public import RKCert.ReviewedNative.TerminalCapacity
public import RKCert.ReviewedNative.ERKGradeFiveSurplus
public import RKCert.ReviewedNative.ReverseClockGain

@[expose] public section

/-! # Exact native ERK17 midpoint and seed split at width twenty-six

Rank nine at the middle is an explicit input, not imported from an old
proof. The true last active index is earned without assuming the final
physical weight is live. A separate uniform surplus supplies that latter
fact using native prefix preservation. -/
namespace RKResearch.Certified.ERK17
open RKResearch Module
open RKResearch.Certified.Graded RKResearch.Certified.Graded.Reverse

section Floor
variable {K : Type*} [Field K] {m : ℕ}
variable {T : Matrix (Fin m) (Fin m) K} {w : Fin m → K}

/-- This is the shared remaining order-seventeen forward rank target. -/
def GradeEightSurplus (K : Type*) [Field K] : Prop :=
  ∀ {m : ℕ} {T : Matrix (Fin m) (Fin m) K} {w : Fin m → K},
    (∀ i j, i ≤ j → T i j=0) → HasOrder T w 17 → 9 ≤ finrank K (zeroSpace T 8)

theorem width_floor_of_grade_eight (ha : ∀ i j, i ≤ j → T i j=0)
    (ho : HasOrder T w 17) (forward : 9 ≤ finrank K (zeroSpace T 8)) : 26 ≤ m := by
  have fg := treeSpace_rank_eq_of_separation ho (q:=8) (by decide) (coeff_separated ho (by decide))
  have cnt := backward_endpoint_count ha ho 8 7 (by decide) (by decide)
  omega

variable [CharZero K]

theorem grade_seven_eight_lower (ha : ∀ i j, i ≤ j → T i j=0)
    (ho : HasOrder T w 17) :
    7 ≤ finrank K (zeroSpace T 7) ∧ 8 ≤ finrank K (zeroSpace T 8) := by
  have five := grade_five_surplus_of_reviewed_order ha ho (by decide : 10≤17)
  have sep := coeff_separated ho (q:=8) (by decide)
  have g56 := Submodule.finrank_lt_finrank_of_lt (zeroSpace_strict_of_separation ha sep (j:=5) (by decide) (by decide))
  have g67 := Submodule.finrank_lt_finrank_of_lt (zeroSpace_strict_of_separation ha sep (j:=6) (by decide) (by decide))
  have g78 := Submodule.finrank_lt_finrank_of_lt (zeroSpace_strict_of_separation ha sep (j:=7) (by decide) (by decide))
  change finrank K (zeroSpace T 5) < finrank K (zeroSpace T 6) at g56
  change finrank K (zeroSpace T 6) < finrank K (zeroSpace T 7) at g67
  change finrank K (zeroSpace T 7) < finrank K (zeroSpace T 8) at g78
  omega

theorem order17_width_floor25 (ha : ∀ i j, i ≤ j → T i j=0)
    (ho : HasOrder T w 17) : 25 ≤ m := by
  have fg := treeSpace_rank_eq_of_separation ho (q:=8) (by decide) (coeff_separated ho (by decide))
  have cnt := backward_endpoint_count ha ho 8 7 (by decide) (by decide)
  have g := (grade_seven_eight_lower ha ho).2
  omega

end Floor

section Tight
variable {K : Type*} [Field K]
variable {A : Matrix (Fin 26) (Fin 26) K} {b : Fin 26 → K}

theorem width26_frame (ha : ∀ i j, i ≤ j → A i j=0) (ho : HasOrder A b 17)
    (forward : 9 ≤ finrank K (zeroSpace A 8)) : OddBalancedFrame A b 8 2 :=
  odd_short_frame ha ho (by decide) (by decide) (by decide) forward

theorem width26_rank_cap (ha : ∀ i j, i ≤ j → A i j=0) (ho : HasOrder A b 17) :
    finrank K (zeroSpace A 8) ≤ 9 := by
  have fg := treeSpace_rank_eq_of_separation ho (q:=8) (by decide) (coeff_separated ho (by decide))
  have cnt := backward_endpoint_count ha ho 8 7 (by decide) (by decide)
  omega

/-- This extra fact needs the rank premise also for the shorter prefix,
rather than a rank-nine premise on the single 26-stage input. -/
theorem width26_last_live_of_uniform_surplus (ha : ∀ i j, i ≤ j → A i j=0)
    (ho : HasOrder A b 17) (surplus : GradeEightSurplus K) : LastActive b (Fin.last 25) := by
  refine ⟨?_,fun i h => (not_lt_of_ge (Fin.le_last i) h).elim⟩
  intro vanish
  have hk : 25 ≤ 26 := by decide
  have zero (i : Fin 26) (hi : 25 ≤ i.val) : b i = 0 := by
    have e : i = Fin.last 25 := Fin.ext (by have := i.isLt; change i.val=25; omega)
    exact e.symm ▸ vanish
  have h := prefix_hasOrder_of_suffix_zero ha ho hk zero
  have a := prefix_strict_lower ha hk
  exact (by decide : ¬ 26≤25) (width_floor_of_grade_eight a h (surplus a h))

/-- The computed zero/nonzero split on the actual width-26 method. -/
theorem width26_seed_split (ha : ∀ i j, i ≤ j → A i j=0) (ho : HasOrder A b 17)
    (forward : 9 ≤ finrank K (zeroSpace A 8)) :
    (firstSeed A b = 0 ∧ ∃ t : Fin 26, LastActive b t ∧ nodes A t = 1 ∧
      quadraticSeed A b t = 0 ∧ coordinate (K:=K) t ∉ treeSpace A 8 ∧
      primitiveBack A b 7 = zeroAt (annih (treeSpace A 8)) t) ∨
    (firstSeed A b ≠ 0 ∧ primitiveBack A b 7 = annih (treeSpace A 8)) := by
  let frame := width26_frame ha ho forward
  have eq : back A b 7 = primitiveBack A b 7 := (frame.reverse.flagExact 7 (by decide)).2
  by_cases z : firstSeed A b = 0
  · obtain ⟨t,L,one,out,only⟩ := frame.reverse.firstZero z
    have dz := mem_tailZero.mp (L.seed_tail ha z 1) t le_rfl
    exact Or.inl ⟨z,t,L,one,dz,out,eq.symm.trans only⟩
  · exact Or.inr ⟨z,eq.symm.trans (frame.reverse.firstNonzero z)⟩

variable [CharZero K]

theorem width26_defect_window (ha : ∀ i j, i ≤ j → A i j=0) (ho : HasOrder A b 17) :
    finrank K (zeroSpace A 8) = 8 ∨ finrank K (zeroSpace A 8) = 9 := by
  have lo := (grade_seven_eight_lower ha ho).2
  have hi := width26_rank_cap ha ho
  omega

omit [CharZero K] in
/-- An actually earned terminal mark costs one reverse dimension at
any earlier tree space from which the coordinate remains external. -/
private theorem primitiveBack_marked_cap {m p j n : ℕ} {T : Matrix (Fin m) (Fin m) K}
    {w : Fin m → K} (ha : ∀ i j, i ≤ j → T i j=0) (h : HasOrder T w p)
    (pay : j+n+2≤p) {t : Fin m} (last : LastActive w t) (z : firstSeed T w=0)
    (out : coordinate (K:=K) t ∉ treeSpace T j) :
    finrank K (primitiveBack T w n) + 1 ≤ finrank K (annih (treeSpace T j)) := by
  have tail : primitiveBack T w n ≤ tailZero t := last.primitiveBack_tail ha z n
  have ann : primitiveBack T w n ≤ annih (treeSpace T j) := primitiveBack_annih h j n pay
  have cut : primitiveBack T w n ≤ zeroAt (annih (treeSpace T j)) t := by
    intro v hv
    have vanish : v t=0 := (mem_tailZero.mp (tail hv)) t le_rfl
    exact mem_zeroAt.mpr ⟨ann hv,vanish⟩
  have f := finrank_zeroAt_annih (treeSpace T j) t out
  exact (Nat.add_le_add_right (Submodule.finrank_mono cut) 1).trans_eq f

set_option maxRecDepth 3500 in
set_option maxHeartbeats 600000 in
/-- Each reverse grade 2 through 7 must escape the actual reflected clock.
At the final grade the forced four-direction gain is charged against the
grade-seven space and, in the zero-seed branch, the real terminal mark. -/
theorem width26_reverse_clock_escape (ha : ∀ i j, i ≤ j → A i j=0) (ho : HasOrder A b 17)
    (frame : OddBalancedFrame A b 8 2) {n : ℕ} (lo : 2 ≤ n) (hi : n ≤ 7) :
    ¬ (primitiveBack A b n).map (diag (reflectedClock A)) ≤ primitiveBack A b n := by
  intro inv
  have gain := reverse_clock_invariant_gain ha ho n (by omega) inv
  have ranks (k : ℕ) (hk : k ≤ 7) :
      finrank K (primitiveBack A b k) = k + finrank K (back A b 0) := by
    obtain ⟨rank,e⟩ := frame.reverse.flagExact k hk
    rw [←e,rank]
  rw [ranks n hi] at gain
  by_cases n7 : n = 7
  · subst n
    have prev := treeSpace_rank_eq_of_separation ho (q:=7) (by decide) (coeff_separated ho (by decide))
    have grow := (grade_seven_eight_lower ha ho).1
    have amb := finrank_annih (treeSpace A 7)
    rw [Fintype.card_fin] at amb
    have inc := primitiveBack_annih ho 7 8 (by decide)
    by_cases z : firstSeed A b = 0
    · obtain ⟨t,L,_,out,_⟩ := frame.reverse.firstZero z
      have out7 : coordinate (K:=K) t ∉ treeSpace A 7 :=
        fun h => out (treeSpace_mono A (by decide : 7≤8) h)
      have lim := primitiveBack_marked_cap (j:=7) (n:=8) ha ho (by decide) L z out7
      rw [first_dim_zero z] at gain
      change 7+0+4 ≤ finrank K (primitiveBack A b 8) at gain
      omega
    · have lim := Submodule.finrank_mono inc
      rw [first_dim_one z] at gain
      change 7+1+4 ≤ finrank K (primitiveBack A b 8) at gain
      omega
  · rw [ranks (n+1) (by omega)] at gain
    omega

end Tight
end RKResearch.Certified.ERK17
