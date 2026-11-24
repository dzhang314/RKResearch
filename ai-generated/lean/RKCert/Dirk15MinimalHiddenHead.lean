module

public import RKCert.Dirk15MinimalCore
public import RKCert.Dirk15GhostPositions
public import RKCert.Dirk15PhysicalSignatures

@[expose] public section

/-! # The original two-hidden-quartic branch before its scalar cut

Every nonterminal nonghost coordinate is retained, irrespective of its
output weight. The shape uses two cheap original grade-five head powers,
not a truncated or projected RK method.
-/
namespace RKCert.Paired
open Module RKCert.OneEscape
open scoped Classical
noncomputable section
variable {K : Type*} [Field K] [CharZero K]
variable {A : Fin 20 → Fin 20 → K} {b : Vec K 20}

structure Order15HiddenHead (A : Fin 20 → Fin 20 → K) (b : Vec K 20) where
  head : Order15MinimalHead A b
  core_eq : head.U=simultaneousGhosts A b
  core_two : finrank K head.U=2
  five : zeroSpace A 5=chain (diag (nodes A)) head.U head.w 2
  head_zero : ∀ i∈ghostPositions A b, head.w i=0

set_option maxHeartbeats 1400000 in
theorem order15_two_hidden_head (ha : LowerArray A) (ho : HasTreeOrderAtLeast A b 15)
    (H : Order15MinimalMarkedChart A b) (hidden : zeroSpace A 4≤simultaneousGhosts A b) :
    Nonempty (Order15HiddenHead A b) := by
  classical
  let F := zeroSpace A
  let C' := diag (nodes A)
  let G := simultaneousGhosts A b
  obtain ⟨h⟩ := order15_minimal_head ha ho H
  obtain ⟨fG,gU,dU⟩ := h.two_hidden_rank H
    (dirk_zeroSpace_lt_succ ha ho (j:=3) (by decide) (by decide)) hidden
  have hG4 : G≤F 4 := fG.ge
  have eU : h.U=G := gU.symm
  have u4 : h.U=F 4 := eU.trans fG.symm
  have f4 : finrank K (F 4)=2 := u4 ▸ dU
  have f6 : finrank K (F 6)=5 := H.initial.f6
  have f7 : finrank K (F 7)=6 := H.initial.f7
  have lo := dirk_forward_invariant_outgoing ha ho (j:=4) (by decide)
    (F 4) le_rfl (fun v hv => by rw [←u4] at hv ⊢; exact h.maximal.2.1 (Submodule.mem_map_of_mem hv))
  change finrank K (F 4)+2≤finrank K (F 5) at lo
  have hi := Submodule.finrank_lt_finrank_of_lt
    (dirk_zeroSpace_lt_succ ha ho (j:=5) (by decide) (by decide))
  change finrank K (F 5)<finrank K (F 6) at hi
  have f5 : finrank K (F 5)=4 := by omega
  have step (k : ℕ) (hk : k<2) :
      finrank K (F (5+k+1))≤finrank K (F (5+k))+1 ∧ ¬(F (5+k)).map C'≤F (5+k) := by
    have unit : finrank K (F (5+k+1))=finrank K (F (5+k))+1 := by
      rcases (show k=0 ∨ k=1 by omega) with rfl|rfl
      · change finrank K (F 6)=finrank K (F 5)+1
        omega
      · change finrank K (F 7)=finrank K (F 6)+1
        omega
    refine ⟨unit.le,fun notOut => ?_⟩
    have out := dirk_forward_invariant_outgoing ha ho (j:=5+k) (by omega) (F (5+k))
      le_rfl (fun z hz => notOut (Submodule.mem_map_of_mem hz))
    change finrank K (F (5+k))+(5+k)/2≤finrank K (F (5+k+1)) at out
    omega
  obtain ⟨d,V,w,d0,inv,inF,maxV,base,_,_,rank⟩ :=
    Clock.ordinary_single_head A 5 (step 0 (by decide)).1 (step 0 (by decide)).2
  have ve : V=h.U := le_antisymm
    (h.maximal.2.2 _ (inF.trans (zeroSpace_mono A (by decide))) inv)
    (maxV _ h.maximal.2.1 (u4 ▸ (zeroSpace_mono A (by decide : 4≤5))))
  subst V
  change finrank K (F 5)=finrank K h.U+d at rank
  have d2 : d=2 := by omega
  subst d
  let v : Vec K 20 := fun i => if i∈ghostPositions A b then 0 else w i
  have diff : w-v∈h.U := by
    rw [eU]
    apply simultaneousGhosts_mem.mpr
    refine ⟨by simp [v,mem_ghostPositions],fun i hi => ?_⟩
    have ng : i∉ghostPositions A b := fun gm =>
      hi.elim (fun e => e (mem_ghostPositions.mp gm).2.1)
        (fun e => e (mem_ghostPositions.mp gm).2.2)
    simp [v,ng]
  have reset : chain C' h.U v 2=chain C' h.U w 2 := by
    have e := chain_sub_head (w:=w) h.maximal.2.1 diff 2
    simpa only [sub_sub_cancel] using e
  have five : F 5=chain C' h.U v 2 := base.trans reset.symm
  have band := Clock.ordinary_staircase h.maximal.2.1 (by decide) five
    (fun k hk => (step k hk).1) (fun k hk => (step k hk).2)
  let J : Order15MinimalHead A b := ⟨h.U,v,h.maximal,h.low,h.high,h.ghosts,h.cubic,
    (by rw [dU]; exact band 1 (by decide)), (by rw [dU]; exact band 2 (by decide)),
    h.seven_escape⟩
  exact ⟨⟨J,eU,dU,five,fun i hi => by simp [J,v,hi]⟩⟩

/-- Exactly seventeen real nonghost signatures, with genuine comparison
on fixed clock fibers. -/
theorem Order15HiddenHead.seventeen_signatures (h : Order15HiddenHead A b)
    (ha : LowerArray A) (ho : HasTreeOrderAtLeast A b 15) (H : Order15MinimalMarkedChart A b) :
    ∃ idx : Fin 17→Fin 20, Function.Injective idx ∧
      (∀ i,idx i≠Fin.last 19 ∧ idx i∉ghostPositions A b) ∧
      (∀ i : Fin 20,i≠Fin.last 19→i∉ghostPositions A b→∃ j,idx j=i) ∧
      Function.Injective (fun i => (nodes A (idx i),h.head.w (idx i))) ∧
      ∀ a, (Signature.fiberAt (fun i => nodes A (idx i)) a).card≤2 := by
  have rn : 17=19-finrank K (simultaneousGhosts A b) := by rw [←h.core_eq,h.core_two]
  obtain ⟨idx,inji,ret,onto⟩ := exists_retained_nonghost_indices H.terminal.weight_ne rn
  have ⟨inj,cap⟩ := order15_actual_signatures ha ho H (order15_minimal_reverse_nonlocal ha ho H)
    h.head.seven.le idx inji (fun i => (ret i).1)
    (fun u hu i => ghostPositions_vanish (h.core_eq ▸ hu) (ret i).2)
  exact ⟨idx,inji,ret,onto,inj,cap⟩

omit [CharZero K] in
set_option maxHeartbeats 600000 in
theorem Order15HiddenHead.square_paid (h : Order15HiddenHead A b) (l : Fin 3) :
    ((diag (nodes A))^l.val) (h.head.w*h.head.w)∈zeroSpace A 10 := by
  let C' := diag (nodes A)
  let w := h.head.w
  have parts := ((chain_le_iff (T:=C') (U:=h.head.U) (w:=w) 2).mp le_rfl).2
  have hw : w∈zeroSpace A 5 := h.five.ge (by simpa only [pow_zero,one_apply_eq_self] using parts 0 (by decide))
  have cw : C' w∈zeroSpace A 5 := h.five.ge (by simpa only [pow_one] using parts 1 (by decide))
  fin_cases l
  · change (C'^0) (w*w)∈zeroSpace A 10
    simpa only [pow_zero,one_apply_eq_self] using zeroSpace_mul hw hw
  · change (C'^1) (w*w)∈zeroSpace A 10
    rw [pow_one,show C' (w*w)=C' w*w by ext i; simp only [C',diag_apply,Pi.mul_apply,mul_assoc]]
    exact zeroSpace_mul cw hw
  · change (C'^2) (w*w)∈zeroSpace A 10
    rw [show (C'^2) (w*w)=C' w*C' w by
      ext i; simp only [C',Clock.pow_diag_apply,Pi.mul_apply,diag_apply]; ring]
    exact zeroSpace_mul cw cw

end
end RKCert.Paired
