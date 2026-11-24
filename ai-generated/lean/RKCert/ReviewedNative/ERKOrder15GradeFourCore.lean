module

public import RKCert.ReviewedNative.ERKOrder15EarlyHeadPayment
public import RKCert.ReviewedNative.ERKOrder15PhysicalCore
public import RKCert.ReviewedNative.ERKGradeEightOffCore

@[expose] public section

/-! # The three-dimensional ordinary grade four is impossible

Use the actual marked-flag payment and remove only the genuine terminal
line. The rank-one off-core row contradiction is the shared native
clock lemma, not a new copy of its polynomial calculation. -/
namespace RKResearch.Certified.Graded

open RKResearch Reverse Module Polynomial RKCert.OneEscape
open scoped Classical
noncomputable section
variable {K : Type*} [Field K] [CharZero K] {s a : ℕ}
variable {A : Matrix (Fin (s+1)) (Fin (s+1)) K} {b : Fin (s+1)→K}
variable {G : K[X]} {w : Fin (s+1)→K} {U : Submodule K (Fin (s+1)→K)}

/-- If F4 had dimension three, the original F3 and its clock image
would exhaust F4 and identify the whole marked core. -/
theorem Order15PaidStaircase.three_core_eq (S : Order15PaidStaircase A b a G 2 U w)
    (ha : ∀ i t,i≤t → A i t=0) (ho : HasOrder 15 A b)
    (r4 : finrank K (zeroSpace A 4)=3) :
    markedDefectSpace A b 4=U ∧ finrank K (zeroSpace A 3)=2 := by
  have early := S.early_two_head_payment
  have d3lo := zeroSpace_finrank ha ho (n:=2) (by decide)
  have se := coeff_separated ho (q:=7) (by decide)
  have d3hi := Submodule.finrank_lt_finrank_of_lt
    (zeroSpace_strict_of_separation ha (j:=3) se (by decide) (by decide))
  change 2≤finrank K (zeroSpace A 3) at d3lo
  change finrank K (zeroSpace A 3)<finrank K (zeroSpace A 4) at d3hi
  have d3 : finrank K (zeroSpace A 3)=2 := by omega
  have P : PolySeparated A 3 := PolySeparated.of_coeff (coeff_separated ho (by decide))
  have neq : ¬(zeroSpace A 3).map (diag (nodes A))≤zeroSpace A 3 := by
    intro inv
    have g := clock_invariant_outgoing ha P le_rfl inv
    rw [d3,r4] at g
    omega
  have low : zeroSpace A 4≤U := by
    have unit : finrank K (zeroSpace A 4)≤finrank K (zeroSpace A 3)+1 := by omega
    rw [zeroSpace_clock_step_of_unit unit neq]
    exact sup_le early.2.1 ((Submodule.map_mono early.2.1).trans S.stable)
  refine ⟨Submodule.eq_of_le_of_finrank_le (sup_le low early.2.2) ?_,d3⟩
  have mark := marked_defect_rank ho (j:=4) S.frame.lastActive (by decide)
  rw [r4] at mark
  have dU := S.headRank
  change finrank K U≤finrank K (markedDefectSpace A b 4)
  omega

omit [CharZero K] in
private theorem terminal_disjoint (ho : HasOrder 15 A b)
    (L : LastActive b (Fin.last s)) (j : ℕ) (h : j+1≤15) :
    Disjoint (zeroSpace A j) (terminalMark A b) := by
  by_cases z : firstSeed A b=0
  · rw [terminalMark,ite_eq_left z]
    exact Submodule.disjoint_span_singleton_of_notMem (last_coordinate_not_defect ho L h)
  · rw [terminalMark,ite_eq_right z]
    exact disjoint_bot_right

/-- The shared ordinary off-core theorem genuinely applies here. The
terminal mark is removed by disjointness and neither closure nor the
small row quotient is assumed of a marked flag. -/
theorem Order15PaidStaircase.no_three_dimensional_four (S : Order15PaidStaircase A b a G 2 U w)
    (ha : ∀ i t,i≤t → A i t=0) (ho : HasOrder 15 A b)
    (r4 : finrank K (zeroSpace A 4)=3) : False := by
  obtain ⟨e,d3⟩ := S.three_core_eq ha ho r4
  let F := zeroSpace A 4
  have low : F≤U := le_sup_left.trans e.le
  have cut {j : ℕ} (lo : 4≤j) (pay : j+1≤15) : U⊓zeroSpace A j=F := by
    have dis := terminal_disjoint ho S.frame.lastActive j pay
    rw [←e]
    change (F⊔terminalMark A b)⊓zeroSpace A j=F
    rw [sup_inf_assoc_of_le _ (zeroSpace_mono A lo),dis.symm.eq_bot,sup_bot_eq]
  have inv : F.map (diag (nodes A))≤F := by
    rintro _ ⟨x,hx,rfl⟩
    rw [←cut (j:=5) (by decide) (by decide)]
    exact ⟨S.stable (Submodule.mem_map_of_mem (low hx)),diag_zeroSpace A 4 hx⟩
  have alg (x : Fin (s+1)→K) (hx : x∈F) (y : Fin (s+1)→K) (hy : y∈F) : x*y∈F := by
    rw [←cut (j:=8) (by decide) (by decide)]
    exact ⟨S.core_times_five ha ho (S.earlyCore (low hy)) (low hx),zeroSpace_mul hx hy⟩
  exact no_rank_three_clock_core_at_order_ten ha ho (by decide) F inv rfl r4 d3 alg

/-- Every hypothetical native rank-two order-fifteen chart has ordinary
grade-four rank exactly four, over any characteristic-zero field. -/
theorem Order15PaidStaircase.ordinary_four_rank (S : Order15PaidStaircase A b a G 2 U w)
    (ha : ∀ i t,i≤t → A i t=0) (ho : HasOrder 15 A b) :
    finrank K (zeroSpace A 4)=4 := by
  have f5 := S.early 0 (by decide)
  change markedDefectSpace A b 5=chain (diag (nodes A)) U w 2 at f5
  have mark := marked_defect_rank ho (j:=5) S.frame.lastActive (by decide)
  have ub := clock_chain_rank_le (diag (nodes A)) U w 2
  have ur := S.headRank
  rw [←f5,mark] at ub
  have lo := zeroSpace_finrank ha ho (n:=3) (by decide)
  change 3≤finrank K (zeroSpace A 4) at lo
  have st := Submodule.finrank_lt_finrank_of_lt (zeroSpace_strict_of_separation ha (j:=4)
    (coeff_separated ho (q:=7) (by decide)) (by decide) (by decide))
  change finrank K (zeroSpace A 4)<finrank K (zeroSpace A 5) at st
  by_contra bad
  exact S.no_three_dimensional_four ha ho (by omega)

end
end RKResearch.Certified.Graded
