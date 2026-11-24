module

public import RKCert.ReviewedNative.ERKOrderTwelveRankThree
public import RKCert.ReviewedNative.ERKGradeEightOffCore

public section

/-! # Order twelve: the head length two, grade-four rank three branch

The only transfer needed is that the native fourth-grade space is the
already measured invariant core. Its genuine grade-eight products make
it a coordinatewise algebra, so the shared order-ten five-clock
obstruction applies unchanged.
-/
namespace RKResearch.Certified.Graded.ERK12

open RKResearch Polynomial Module
open scoped Matrix

variable {K : Type*} [Field K] [CharZero K] {s : ℕ}
variable {A : Matrix (Fin (s+1)) (Fin (s+1)) K} {b : Fin (s+1) → K}

/-- In the rank-(2,3) branch, the unit F3-to-F4 clock gain fills the
three-dimensional invariant core. -/
theorem fourth_grade_eq_core_of_rank_two_three
    (ha : ∀ i k, i≤k → A i k=0) (ho : HasOrder 12 A b)
    (S : Saturation A b) (T : TerminalBand A b)
    {U : Submodule K (Fin (s+1) → K)} {w : Fin (s+1) → K}
    (H : ForwardStaircase A 2 U w) (four : finrank K (zeroSpace A 4)=3) :
    zeroSpace A 4=U ∧ finrank K U=3 ∧ finrank K (zeroSpace A 3)=2 := by
  let D := diag (nodes A)
  have base := H.initial.baseRank
  change finrank K (zeroSpace A 5)=finrank K U+2 at base
  rw [S.f5] at base
  have dimU : finrank K U=3 := by omega
  have lower := zeroSpace_finrank ha ho (n:=2) (by decide)
  change 2≤finrank K (zeroSpace A 3) at lower
  have coeff := explicit_coeff_separated ha ho (q:=6) (by decide)
  have inc := Submodule.finrank_lt_finrank_of_lt
    (zeroSpace_strict_of_separation ha coeff (j:=3) (by decide) (by decide))
  change finrank K (zeroSpace A 3)<finrank K (zeroSpace A 4) at inc
  have dim3 : finrank K (zeroSpace A 3)=2 := by omega
  have esc : ¬(zeroSpace A 3).map D≤zeroSpace A 3 := by
    intro inv
    have sep := (PolySeparated.of_coeff coeff).mono (by decide : 3≤6)
    have gain := clock_invariant_outgoing ha sep le_rfl inv
    change finrank K (zeroSpace A 3)+(3+1)/2≤finrank K (zeroSpace A 4) at gain
    omega
  have eq : zeroSpace A 4=zeroSpace A 3⊔(zeroSpace A 3).map D :=
    zeroSpace_clock_step_of_unit (A:=A) (n:=3) (by
      change finrank K (zeroSpace A 4)≤finrank K (zeroSpace A 3)+1
      omega) esc
  have F := grade_three_in_core ha ho S T H
  have sub : zeroSpace A 4≤U := eq ▸ sup_le F ((Submodule.map_mono F).trans H.initial.coreStable)
  exact ⟨Submodule.eq_of_le_of_finrank_le sub (by omega),dimU,dim3⟩

/-- The whole rank-(2,3) branch contradicts reviewed order without any
new scalar arithmetic, because no more than five clocks can occur. -/
theorem exclude_two_three (ha : ∀ i k, i≤k → A i k=0) (ho : HasOrder 12 A b)
    (S : Saturation A b) (T : TerminalBand A b)
    {U : Submodule K (Fin (s+1) → K)} {w : Fin (s+1) → K}
    (H : ForwardStaircase A 2 U w) (four : finrank K (zeroSpace A 4)=3) : False := by
  obtain ⟨f4,dU,d3⟩ := fourth_grade_eq_core_of_rank_two_three ha ho S T H four
  have inside := f4.ge
  have closed (u : Fin (s+1) → K) (hu : u∈U) (v : Fin (s+1) → K) (hv : v∈U) :
      u*v∈U := by
    have inv : U.map (diag v)≤U :=
      grade_eight_multiplier_stable ha ho S T H inside (by decide) (inside hv)
    have eq : diag v u=u*v := by ext i; simp [mul_comm]
    exact eq ▸ inv (Submodule.mem_map_of_mem hu)
  exact no_rank_three_clock_core_at_order_ten ha ho (by decide) U
    H.initial.coreStable f4 dU d3 closed

/-- The remaining physical cap has head length two and fourth rank four. -/
theorem only_rank_two_four_at_cap (ha : ∀ i k, i≤k → A i k=0)
    (ho : HasOrder 12 A b) (cap : s+1≤17) :
    ∃ U w, ForwardStaircase A 2 U w ∧ finrank K (zeroSpace A 4)=4 := by
  have S := saturation_of_order ha ho cap
  have T := terminal_band ha ho S
  obtain ⟨r,U,w,H⟩ := forward_staircase ha ho S
  obtain ⟨rfl,four⟩ := remaining_rank_two_branches ha ho S T H
  exact ⟨U,w,H,four.resolve_left (exclude_two_three ha ho S T H)⟩

end RKResearch.Certified.Graded.ERK12

