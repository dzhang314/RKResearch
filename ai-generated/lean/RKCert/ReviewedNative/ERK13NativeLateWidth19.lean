module

public import RKCert.ReviewedNative.ERK13NativeLateRadiusTwo
public import RKCert.ReviewedNative.ERK13NativeLateRadiusThree
public import RKCert.ReviewedNative.ERK13OrdinaryWidth19
import Lean.Elab.Tactic.Omega

@[expose] public section

/-! # At order thirteen a width-19 tableau must pay the literal terminal by grade seven

This removes all placements of a later or missing terminal on the original
row space. It does not exclude the true early-terminal branch. -/
namespace RKResearch.Certified.Graded.ERK13NativeFirst

open RKResearch Reverse Module ERK13NativeLatePhysicalFold
open scoped Classical Matrix
noncomputable section

variable {K : Type*} [Field K] [CharZero K]
variable {A : Matrix (Fin 19) (Fin 19) K} {b : Fin 19 → K}

theorem native_late_width19_impossible
    (ha : ∀ i j,i≤j → A i j=0) (ho : HasOrder 13 A b) (seed : firstSeed A b=0)
    (late : coordinate (K:=K) (Fin.last 18)∉treeSpace A 7) : False := by
  obtain ⟨r,U,w,H⟩ := paid_head_of_order ha ho
  obtain ⟨a,G,F⟩ := firstEscape_of_paid_rank ha ho H.paidRanks
  rcases F.width with six | ⟨five,_⟩
  · subst a
    have C := native_marked_escape_chart ha ho seed H F
    obtain ⟨_,rad,_⟩ := C.late_rank_radius ha ho late
    rcases rad with rfl|rfl
    · exact late_radius_two_impossible ha ho C late
    · exact native_late_radius_three_impossible ha ho C late
  · subst a
    exact late (terminal_enters_seven_of_first_degree_six13 ha ho seed F)

/-- No first-seed premise: the other seed case already has a native
unrestricted width-19 obstruction. -/
theorem width19_pays_terminal_by_seven
    (ha : ∀ i j,i≤j → A i j=0) (ho : HasOrder 13 A b) :
    coordinate (K:=K) (Fin.last 18)∈treeSpace A 7 := by
  by_contra late
  by_cases seed : firstSeed A b=0
  · exact native_late_width19_impossible ha ho seed late
  · exact ordinary_width19_impossible ha ho seed

theorem twenty_le_of_order_thirteen_late {s : ℕ} {T : Matrix (Fin (s+1)) (Fin (s+1)) K}
    {v : Fin (s+1)→K} (ha : ∀ i j,i≤j → T i j=0) (ho : HasOrder 13 T v)
    (late : coordinate (K:=K) (Fin.last s)∉treeSpace T 7) : 20≤s+1 := by
  have floor := stage_floor19 ha ho
  by_contra small
  have eq : s=18 := by omega
  subst s
  exact late (width19_pays_terminal_by_seven ha ho)

end
end RKResearch.Certified.Graded.ERK13NativeFirst
