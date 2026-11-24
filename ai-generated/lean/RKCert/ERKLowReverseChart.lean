module

public import RKCert.ERKLowSaturation
public import RKCert.ReverseHermiteRank

@[expose] public section

/-! # The order-nine fifth-grade clock is not invariant

The genuine reverse fourth-degree rows preserve a terminal-zero restriction.
This pays the missing rank in the saturated ten-dimensional fifth grade.
-/
namespace RKCert.Paired
open Module Polynomial RKCert.Endpoint ReverseHull

variable {K : Type*} [Field K] {s p : ℕ}

theorem annih_mono_reverse {V W : Submodule K (Vec K s)} (h : V ≤ W) :
    annih W ≤ annih V := fun _ hw => mem_annih.mpr fun v hv => mem_annih.mp hw v (h hv)

theorem transMat_mem_annih_pred {A : Fin s → Fin s → K} {j : ℕ} {w : Vec K s}
    (hw : w ∈ annih (treeSpace A (j+1))) : transMat A w ∈ annih (treeSpace A j) := by
  apply mem_annih.mpr
  intro v hv
  rw [row_flip_mat]
  exact mem_annih.mp hw _ (mat_treeSpace A j hv)

theorem transMat_last_zero {A : Fin (s+1) → Fin (s+1) → K} (ha : StrictLower A)
    (w : Vec K (s+1)) : transMat A w (Fin.last s)=0 := by
  rw [mat_apply]
  exact Finset.sum_eq_zero (fun i _ => by rw [ha i (Fin.last s) (Fin.le_last i),zero_mul])

theorem row_single_eq_coord (w : Vec K s) (i : Fin s) : row w (Pi.single i 1)=w i := by
  simp [row_apply,Pi.single_apply]

/-- A terminal restriction strictly decreases the annihilator rank
unless the corresponding basis column is already in the stage space. -/
theorem annih_coord_lt {U : Submodule K (Vec K s)} {i : Fin s}
    (hi : Pi.single i 1 ∉ U) :
    finrank K ↥(annih U ⊓ LinearMap.ker (LinearMap.proj i)) < finrank K (annih U) := by
  apply Submodule.finrank_lt_finrank_of_lt
  apply lt_of_le_of_ne inf_le_left
  intro heq
  apply hi
  apply row_annih_test
  intro w hw
  have hz := (show w ∈ annih U ⊓ LinearMap.ker (LinearMap.proj i) from heq.symm ▸ hw).2
  rw [row_single_eq_coord]
  exact LinearMap.mem_ker.mp hz

variable [CharZero K]

/-- Reverse Hermite gain with the target chosen by the caller. Both
the chronological image and the entire primitive family must fit. -/
theorem reverse_hermite_gain_to {A : Fin s → Fin s → K} {b : Vec K s}
    (ha : StrictLower A) (ho : HasTreeOrderAtLeast A b p) (hp : 4 ≤ p)
    (U Z : Submodule K (Vec K s)) (hUZ : U ≤ Z)
    (hmask : MaskInvariant (mirror A) U) (hmass : ∀ w ∈ U, ∑ i,w i=0)
    (hNZ : ∀ w∈U, transMat A w∈Z)
    (hP : ∀ P : K[X], P.natDegree ≤ 3 →
      transMat A (weightedEval (mirror A) b P) -
        weightedEval (mirror A) b (formalPrimitive P) ∈ Z) :
    finrank K U + 2 ≤ finrank K Z := by
  let T := revVec (K:=K) (s:=s)
  let Ur := U.map T.toLinearMap
  let Zr := Z.map T.toLinearMap
  let y := mirror A
  have hm : MaskInvariant (T y) Ur := by
    intro a w hw
    obtain ⟨x,hx,rfl⟩ := hw
    apply Submodule.mem_map_of_mem (hmask a x hx)
  have hf (w) (hw : w∈Ur) : (∑ i,w i)=0 := by
    obtain ⟨x,hx,rfl⟩ := hw
    change (∑ i : Fin s, x i.rev)=0
    rw [show (∑ i : Fin s, x i.rev)=∑ i,x i from Equiv.sum_comp Fin.revPerm x]
    exact hmass x hx
  have rsum (k : ℕ) : (∑ i,(T y i)^k*(T b i))=∑ i,(y i)^k*b i :=
    Equiv.sum_comp Fin.revPerm (fun i => y i^k*b i)
  obtain ⟨m1,m2,m3⟩ := mirror_moments ho hp
  have nod := two_failed_of_three_moments (T y) (T b) Ur hm hf
    ((rsum 1).trans m1) ((rsum 2).trans m2) ((rsum 3).trans m3)
  have wc (P : K[X]) : weightedEval (T y) (T b) P = T (weightedEval y b P) := by
    ext i
    simp only [T,revVec_apply,weightedEval_apply]
  have rank := outgoing_nodal_gain (T y) (T b) Ur Zr (reverseOp A) (reverseOp_strict ha) hm
    (Submodule.map_mono hUZ) (by
      rintro _ ⟨x,hx,rfl⟩
      rw [show T.toLinearMap x=revVec x from rfl,reverseOp_rev]
      exact Submodule.mem_map_of_mem (hNZ x hx)) 2 nod (by
        intro P hP'
        rw [wc,wc,show T=revVec from rfl,reverseOp_rev,←map_sub]
        apply Submodule.mem_map_of_mem
        exact hP P (by omega))
  rw [←(T.submoduleMap U).finrank_eq,←(T.submoduleMap Z).finrank_eq] at rank
  exact rank

/-- If the higher grade contains the terminal column at node one, the
reverse Hermite target loses one further dimension. An adjacent rank gap
of at most two is therefore incompatible with clock invariance. -/
theorem clock_not_of_anchored_adjacent_gap {A : Fin (s+1) → Fin (s+1) → K}
    {b : Vec K (s+1)} {j : ℕ} (ha : StrictLower A)
    (ho : HasTreeOrderAtLeast A b p) (hp : j+5 ≤ p)
    (hc : nodes A (Fin.last s)=1)
    (hi : Pi.single (Fin.last s) 1 ∈ treeSpace A (j+1))
    (hn : Pi.single (Fin.last s) 1 ∉ treeSpace A j)
    (hgap : finrank K (treeSpace A (j+1)) ≤ finrank K (treeSpace A j)+2) :
    ¬ (treeSpace A (j+1)).map (diag (nodes A)) ≤ treeSpace A (j+1) := by
  intro hC
  let U := annih (treeSpace A (j+1))
  let W := annih (treeSpace A j)
  let i := Fin.last s
  let Z : Submodule K (Vec K (s+1)) := W ⊓ LinearMap.ker (LinearMap.proj i)
  have hUW : U ≤ W := annih_mono_reverse (treeSpace_mono A (Nat.le_succ j))
  have hmask : MaskInvariant (mirror A) U :=
    reflected_mask_annih (maskInvariant_of_diag (fun _ hv => hC (Submodule.mem_map_of_mem hv)))
  have hmass (w : Vec K (s+1)) (hw : w∈U) : (∑ i,w i)=0 := by
    have h := mem_annih.mp hw (1 : Vec K (s+1)) (stageWeight_mem_space A .leaf (by simp [Tree.order]))
    simpa [row_apply] using h
  have hU := finrank_add_annih_eq (treeSpace A (j+1))
  have hW := finrank_add_annih_eq (treeSpace A j)
  change finrank K (treeSpace A (j+1)) + finrank K U = s+1 at hU
  change finrank K (treeSpace A j) + finrank K W = s+1 at hW
  have hUZ : U ≤ Z := by
    intro w hw
    exact ⟨hUW hw,LinearMap.mem_ker.mpr ((row_single_eq_coord w i).symm.trans (mem_annih.mp hw _ hi))⟩
  have hr := reverse_hermite_gain_to ha ho (by omega) U Z hUZ hmask hmass
    (fun w hw => ⟨transMat_mem_annih_pred hw, LinearMap.mem_ker.mpr (transMat_last_zero ha w)⟩)
    (fun P hd => by
      refine ⟨reverse_primitive_annih ho j hp P hd, LinearMap.mem_ker.mpr ?_⟩
      change transMat A (weightedEval (mirror A) b P) i -
        weightedEval (mirror A) b (formalPrimitive P) i=0
      have hm : mirror A i=0 := by change 1 - nodes A (Fin.last s)=0; rw [hc,sub_self]
      rw [transMat_last_zero ha,weightedEval_apply,hm,formalPrimitive_eval_zero,zero_mul,sub_zero])
  have hZ : finrank K Z < finrank K W := annih_coord_lt hn
  omega

/-- The fourth grade of a ten-stage order-eight tableau is not invariant
under node multiplication. This uses the same terminal restriction as p9. -/
theorem order8_treeSpace_four_not_clock_invariant
    {A : Fin 10 → Fin 10 → K} {b : Vec K 10}
    (ha : StrictLower A) (ho : HasTreeOrderAtLeast A b 8) :
    ¬ (treeSpace A 4).map (diag (nodes A)) ≤ treeSpace A 4 := by
  obtain ⟨_,_,hc,hi,hn,_,_,he3,he4,_,_⟩ := order8_ten_stage_chart ha ho
  have hcap : finrank K (treeSpace A 4) ≤ finrank K (treeSpace A 3)+2 := by rw [he4,he3]
  exact clock_not_of_anchored_adjacent_gap (s:=9) (j:=3) ha ho (by decide) hc hi hn hcap

/-- For an actual twelve-stage order-nine explicit tableau, both possible
E5 ranks are covered. No ordering or positivity of the field is assumed. -/
theorem order9_treeSpace_five_not_clock_invariant
    {A : Fin 12 → Fin 12 → K} {b : Vec K 12}
    (ha : StrictLower A) (ho : HasTreeOrderAtLeast A b 9) :
    ¬ (treeSpace A 5).map (diag (nodes A)) ≤ treeSpace A 5 := by
  intro hC
  obtain ⟨_,_,_,_,he4,he5lo,he5hi,_⟩ := order9_twelve_stage_chart ha ho
  let U := annih (treeSpace A 5)
  let W := annih (treeSpace A 4)
  have hUW : U ≤ W := annih_mono_reverse (treeSpace_mono A (by decide))
  have hmask : MaskInvariant (mirror A) U :=
    reflected_mask_annih (maskInvariant_of_diag (fun _ hv => hC (Submodule.mem_map_of_mem hv)))
  have hmass (w : Vec K 12) (hw : w∈U) : (∑ i,w i)=0 := by
    have h := mem_annih.mp hw (1 : Vec K 12) (stageWeight_mem_space A .leaf (by decide))
    simpa [row_apply] using h
  have hU := finrank_add_annih_eq (treeSpace A 5)
  have hW := finrank_add_annih_eq (treeSpace A 4)
  change finrank K (treeSpace A 5) + finrank K U = 12 at hU
  change finrank K (treeSpace A 4) + finrank K W = 12 at hW
  have hP (P : K[X]) (hdeg : P.natDegree ≤ 3) :
      transMat A (weightedEval (mirror A) b P) -
        weightedEval (mirror A) b (formalPrimitive P) ∈ W :=
    reverse_primitive_annih ho 4 (by decide) P hdeg
  by_cases he5 : finrank K (treeSpace A 5)=10
  · obtain ⟨_,hc,hi,hn,_,_⟩ := order9_rank_five_full ha ho he5
    have hcap : finrank K (treeSpace A 5) ≤ finrank K (treeSpace A 4)+2 := by rw [he5,he4]
    exact clock_not_of_anchored_adjacent_gap (s:=11) (j:=4) ha ho (by decide) hc hi hn hcap hC
  · have hdeg := reverse_hermite_gain_to ha ho (by decide) U W hUW hmask hmass
      (fun _ hw => transMat_mem_annih_pred hw) hP
    omega

end RKCert.Paired

