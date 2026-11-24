module

public import RKCert.ReviewedNative.ERKOrder15BandIsolation
public import RKCert.ReviewedNative.NativeClockChainPeel

@[expose] public section

/-! # The two-head clock tests pay the actual earlier grades -/
namespace RKResearch.Certified.Graded

open RKResearch Reverse Module RKCert.OneEscape
open scoped Classical
noncomputable section
variable {K : Type*} [Field K]

variable {s a : ℕ}
variable {A : Matrix (Fin (s+1)) (Fin (s+1)) K} {b : Fin (s+1)→K}
variable {w : Fin (s+1)→K} {U : Submodule K (Fin (s+1)→K)}
variable {G : Polynomial K}

private theorem marked_four_clock :
    markedDefectSpace A b 4≤(markedDefectSpace A b 5).comap (diag (nodes A)) := by
  apply Submodule.map_le_iff_le_comap.mp
  change (zeroSpace A 4⊔terminalMark A b).map (diag (nodes A))≤_
  rw [Submodule.map_sup]
  exact sup_le_sup (Submodule.map_le_iff_le_comap.mpr (diag_zeroSpace A 4)) (terminalMark_clock A b)

/-- Grade four lies in the core plus the original head line; grade
three and the actual terminal mark lie in the invariant core itself. -/
theorem Order15PaidStaircase.early_two_head_payment (S : Order15PaidStaircase A b a G 2 U w) :
    markedDefectSpace A b 4≤chain (diag (nodes A)) U w 1 ∧
    zeroSpace A 3≤U ∧ terminalMark A b≤U := by
  let D := diag (nodes A)
  let B := chain D U w
  have f5 : markedDefectSpace A b 5=B 2 := S.early 0 (by decide)
  have f7 : markedDefectSpace A b 7=B 4 := S.early 2 (by decide)
  have out2 : (D^2) w∉B 2 := by
    intro h
    have e3 : B 3=B 2 := sup_eq_left.mpr ((Submodule.span_singleton_le_iff_mem ..).mpr h)
    have inv : (B 2).map D≤B 2 :=
      le_sup_right.trans ((clock_chain_next S.stable (by decide : 0<2)).trans e3).le
    have e4 : B 4=B 2 := by
      rw [←show B 3⊔(B 3).map D=B 4 from clock_chain_next S.stable (by decide),e3,sup_eq_left.mpr inv]
    have r7 := S.frame.defectRank
    rw [f7,e4] at r7
    have cap : finrank K (B 2)≤finrank K U+2 := clock_chain_rank_le D U w 2
    have ur := S.headRank
    omega
  have out1 : (D^1) w∉B 1 := by
    intro h
    have move : (B 1).map D≤B 2 :=
      le_sup_right.trans (clock_chain_next S.stable (by decide : 0<1)).le
    apply out2
    rw [show (2:ℕ)=1+1 by decide,pow_succ',Module.End.mul_eq_comp,LinearMap.comp_apply]
    exact move (Submodule.mem_map_of_mem h)
  have one {x : Fin (s+1)→K} (h : x∈markedDefectSpace A b 5)
      (hD : D x∈markedDefectSpace A b 5) : x∈B 1 := by
    have b1 : x∈B 2 := by rw [←f5]; exact h
    have b2 : D x∈B 2 := by rw [←f5]; exact hD
    exact clock_chain_drop_of_next_unpaid (D:=D) (U:=U) (w:=w) S.stable 1 out2 b1 b2
  have two {x : Fin (s+1)→K} (h : x∈markedDefectSpace A b 5)
      (hD : D x∈markedDefectSpace A b 5) (hDD : D (D x)∈markedDefectSpace A b 5) :
      x∈U :=
    clock_chain_drop_of_next_unpaid S.stable 0 out1 (one h hD) (one hD hDD)
  have up (j : ℕ) (p : j≤5) : zeroSpace A j≤markedDefectSpace A b 5 :=
    (zeroSpace_mono A p).trans le_sup_left
  have tail : terminalMark A b≤markedDefectSpace A b 5 := le_sup_right
  refine ⟨?_,?_,?_⟩
  · intro x h
    exact one ((sup_le_sup (zeroSpace_mono A (by decide : 4≤5)) le_rfl) h)
      (marked_four_clock h)
  · intro x h
    have hd := diag_zeroSpace A 3 h
    exact two (up 3 (by decide) h) (up 4 (by decide) hd) (up 5 le_rfl (diag_zeroSpace A 4 hd))
  · intro x h
    have hd := terminalMark_clock A b (Submodule.mem_map_of_mem h)
    exact two (tail h) (tail hd) (tail (terminalMark_clock A b (Submodule.mem_map_of_mem hd)))

/-- A four-dimensional ordinary grade four pays the entire core and
actual rank-two head already at grade four. -/
theorem Order15PaidStaircase.four_eq_core_head (S : Order15PaidStaircase A b a G 2 U w)
    (ho : HasOrder A b 15) (rank4 : finrank K (zeroSpace A 4)=4) :
    markedDefectSpace A b 4=chain (diag (nodes A)) U w 1 := by
  apply Submodule.eq_of_le_of_finrank_le S.early_two_head_payment.1
  have r := marked_defect_rank ho (j:=4) S.frame.lastActive (by decide)
  rw [rank4] at r
  have cap := clock_chain_rank_le (diag (nodes A)) U w 1
  have h := S.headRank
  omega

end
end RKResearch.Certified.Graded
