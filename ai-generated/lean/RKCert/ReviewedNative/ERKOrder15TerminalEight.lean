module

public import RKCert.ReviewedNative.ERKOrder15GradeFourCore
public import RKCert.ReviewedNative.ERKOrder15PaidQuarticCut

@[expose] public section

/-! # The native rank-two chart has a genuine early terminal

First extract the grade-four paid quartic profile if the terminal is
absent. Then use the shared paid two-knot cutoff on the same physical
matrix. No later scalar-pencil step is assumed or proved here. -/
namespace RKResearch.Certified.Graded

open RKResearch Reverse Module Polynomial RKCert.OneEscape RKCert.Endpoint
open scoped Classical
noncomputable section
variable {K : Type*} [Field K] {s a : ℕ}
variable {A : Matrix (Fin (s+1)) (Fin (s+1)) K} {b : Fin (s+1)→K}
variable {G : K[X]} {w : Fin (s+1)→K} {U : Submodule K (Fin (s+1)→K)}

section Profile
variable [CharZero K]

/-- Under an absent terminal, the same rank-two chart has a disjoint
head in the actual marked F4 whose value on every active physical row
is a nonzero polynomial of degree at most four. -/
theorem Order15PaidStaircase.paid_quartic_profile_of_absent (S : Order15PaidStaircase A b a G 2 U w)
    (ha : ∀ i t,i≤t → A i t=0) (ho : HasOrder A b 15)
    (absent : firstSeed A b≠0 ∨ coordinate (K:=K) (Fin.last s)∉treeSpace A 8) :
    ∃ (v : Fin (s+1)→K) (P : K[X]), Order15PaidStaircase A b a G 2 U v ∧
      v∈markedDefectSpace A b 4 ∧ (∀ i, LiveCore.live U i → v i=0) ∧
      (∀ i,v i≠0 → v i=P.eval (nodes A i)) ∧ P≠0 ∧ P.natDegree≤4 := by
  obtain ⟨v,T,dis,_⟩ := S.clean_head ha ho
  have v4 : v∈markedDefectSpace A b 4 := by
    rw [T.four_eq_core_head ho (T.ordinary_four_rank ha ho)]
    have p := ((clock_chain_le_iff (T:=diag (nodes A)) (U:=U) (w:=v) 1).mp le_rfl).2 0 (by decide)
    simpa only [pow_zero,Module.End.one_eq_id,LinearMap.id_apply] using p
  have base := order15_absent_terminal_grade_eight_rigid ha ho T absent
  have next : markedDefectSpace A b 8=chain (diag (nodes A)) U v 5 := by
    change zeroSpace A 8⊔terminalMark A b=_
    rw [base]
    exact T.escape
  have sq : v*v∈chain (diag (nodes A)) U v 5 :=
    next ▸ marked_defect_mul (j:=4) (k:=4) v4 v4
  obtain ⟨u,hu,P,pd,eq⟩ := HeadFiber.exists_poly sq
  have repr (i : Fin (s+1)) (hi : v i≠0) : v i=P.eval (nodes A i) := by
    have ui : u i=0 := by
      by_contra un
      exact hi (dis i ⟨u,hu,un⟩)
    have h := congrFun eq i
    rw [Pi.mul_apply,Pi.add_apply,weightedEval_apply,ui,zero_add] at h
    exact mul_right_cancel₀ hi h
  have pn : P≠0 := by
    intro h
    have cnt : 0<(HeadFiber.physicalSites (nodes A) v).card :=
      ((Nat.zero_le _).trans_lt (T.ten_has_escape_sites ho)).trans_le
        (Finset.card_le_card HeadFiber.escape_le_physical)
    obtain ⟨_,m⟩ := Finset.card_pos.mp cnt
    obtain ⟨i,hi,_⟩ := Finset.mem_image.mp m
    have nz := (Finset.mem_filter.mp hi).2
    exact nz (by rw [repr i nz,h,eval_zero])
  have deg : P.natDegree<5 := (natDegree_lt_iff_degree_lt pn).mpr pd
  exact ⟨v,P,T,v4,dis,repr,pn,by omega⟩
end Profile

section Ordered
variable [LinearOrder K] [IsStrictOrderedRing K]

/-- The actual last coordinate enters the ordinary tree space at
grade eight, and does not already belong to grade seven. -/
theorem Order15PaidStaircase.terminal_eight_rank_two (S : Order15PaidStaircase A b a G 2 U w)
    (ha : ∀ i t,i≤t → A i t=0) (ho : HasOrder A b 15) :
    firstSeed A b=0 ∧ coordinate (K:=K) (Fin.last s)∈treeSpace A 8 ∧
      coordinate (K:=K) (Fin.last s)∉treeSpace A 7 := by
  have h : firstSeed A b=0 ∧ coordinate (K:=K) (Fin.last s)∈treeSpace A 8 := by
    by_contra denied
    have absent : firstSeed A b≠0 ∨ coordinate (K:=K) (Fin.last s)∉treeSpace A 8 := by
      by_cases z : firstSeed A b=0
      · exact Or.inr (fun z8 => denied ⟨z,z8⟩)
      · exact Or.inl z
    obtain ⟨v,P,T,v4,dis,repr,pn,pd⟩ := S.paid_quartic_profile_of_absent ha ho absent
    exact denied (T.terminal_of_paid_quartic ha ho v4 dis repr pn pd)
  exact ⟨h.1,h.2,endpoint_coordinate_out ha ho (q:=7) (by decide) _
    S.frame.lastActive.live (S.frame.lastActive.node_eq_one ha h.1)⟩

/-- The native width-22 ordered order-fifteen chart is now an actual
marked rank-two chart with the ordinary terminal entry E8 outside E7. -/
theorem order15_ordered_terminal_chart (ha : ∀ i t,i≤t → A i t=0)
    (ho : HasOrder A b 15) (cap : s+1≤22) :
    ∃ (a : ℕ) (G : K[X]) (U : Submodule K (Fin (s+1)→K)) (w : Fin (s+1)→K),
      Order15PaidStaircase A b a G 2 U w ∧ finrank K (zeroSpace A 4)=4 ∧
      firstSeed A b=0 ∧ coordinate (K:=K) (Fin.last s)∈treeSpace A 8 ∧
      coordinate (K:=K) (Fin.last s)∉treeSpace A 7 := by
  obtain ⟨a,G,U,w,S⟩ := order15_rank_two_staircase ha ho cap
  exact ⟨a,G,U,w,S,S.ordinary_four_rank ha ho,S.terminal_eight_rank_two ha ho⟩
end Ordered

end
end RKResearch.Certified.Graded
