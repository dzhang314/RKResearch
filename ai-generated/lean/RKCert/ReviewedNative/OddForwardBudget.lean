module
public import RKCert.ReviewedNative.OddHorizon

@[expose] public section

/-! # Odd forward room and two-ended native frame
Only a lower bound for the actual middle defect rank is passed in; the
node separation, exact dimensions, and reverse cover are all derived.
-/
namespace RKResearch.Certified.Graded.Reverse
open RKResearch Module
noncomputable section

variable {K : Type*} [Field K] {s p q d : ℕ}
variable {A : Matrix (Fin (s+1)) (Fin (s+1)) K} {b : Fin (s+1) → K}

theorem coeff_separated_next (ha : ∀ i j, i ≤ j → A i j = 0)
    (ho : HasOrder A b p) (pay : 2*q+1 ≤ p) (a : Fin (q+1) → K)
    (hv : coeffEval A q a ∈ zeroSpace A (q+1)) : a = 0 := by
  have h0 : coeffEval A q a 0=0 := origin_zeroSpace ha (q+1) hv
  have a0 : a 0=0 := by rw [coeffEval_origin ha] at h0; exact h0
  have tests (i : Fin q) :
      (∑ j : Fin q,a j.succ/((i.val+j.val+2:ℕ):K))=0 := by
    have h := probe_zeroSpace (k:=i.val) ho (by have := i.isLt;omega) hv
    change probe A b i.val (coeffEval A q a) = 0 at h
    rw [probe_coeffEval ho (k:=i.val) (q:=q) (by have :=i.isLt;omega) a,
      Fin.sum_univ_succ,a0,zero_div,zero_add] at h
    simpa only [Fin.val_succ,Nat.add_assoc] using h
  have rest := moments_detect ho (n:=q) (d:=2) (by decide) (by omega)
    (fun i j=>by have :=i.isLt;have :=j.isLt;omega) (fun j:Fin q=>a j.succ) tests
  ext i
  exact Fin.cases a0 rest i

/-- At the next ordinary grade one keeps q+1 independent polynomial
columns with the zero-origin condition. No extra moment is borrowed. -/
theorem odd_next_tree_rank_lower (ha : ∀ i j, i ≤ j → A i j = 0) (ho : HasOrder A b p)
    (pay : 2*q+1 ≤ p) :
    q+1+finrank K (zeroSpace A (q+1)) ≤ finrank K (treeSpace A (q+1)) := by
  let V := (coeffEval A q).range
  let F := zeroSpace A (q+1)
  have dis : V ⊓ F = ⊥ := by
    apply le_antisymm _ bot_le
    intro v hv
    obtain ⟨hv,hf⟩:=Submodule.mem_inf.mp hv
    obtain ⟨a,rfl⟩:=hv
    rw [coeff_separated_next ha ho pay a hf,map_zero]
    exact (⊥:Submodule K (Fin (s+1) → K)).zero_mem
  have inj : Function.Injective (coeffEval A q) := by
    apply (injective_iff_map_eq_zero _).mpr
    intro a za
    apply coeff_separated_next ha ho pay a
    exact za ▸ F.zero_mem
  have vdim : finrank K V=q+1 := by
    exact (LinearMap.finrank_range_of_inj inj).trans (Module.finrank_fin_fun K)
  have inc : V ⊔ F ≤ treeSpace A (q+1) := by
    apply sup_le
    · rintro _ ⟨a,rfl⟩
      exact treeSpace_mono A (Nat.le_succ q) (coeffEval_mem_treeSpace A q a)
    · exact zeroSpace_le_treeSpace A (q+1)
  have h := Submodule.finrank_mono inc
  have e := Submodule.finrank_sup_add_finrank_inf_eq V F
  rw [dis,finrank_bot,add_zero,vdim] at e
  rwa [e] at h

/-- Exact cap on next-grade defects plus the first-seed rank at odd order. -/
theorem odd_next_paid_room (ha : ∀ i j, i ≤ j → A i j = 0) (ho : HasOrder A b p)
    (q2 : 2 ≤ q) (pay : 2*q+1 ≤ p) :
    finrank K (zeroSpace A (q+1)) + finrank K (back A b 0) + 2*q ≤ s+2 := by
  have lo:=odd_next_tree_rank_lower ha ho pay
  have hi:=backward_count ha ho (q+1) (q-2) (by omega)
  omega

structure OddBalancedFrame (A : Matrix (Fin (s+1)) (Fin (s+1)) K)
    (b : Fin (s+1) → K) (q d : ℕ) : Prop where
  stageCount : s+1=3*q+d
  separated : ∀ a, coeffEval A q a ∈ zeroSpace A q → a=0
  middleDefects : finrank K (zeroSpace A q)=q+d-1
  middleTree : finrank K (treeSpace A q)=2*q+d
  nextRoom : finrank K (zeroSpace A (q+1)) + finrank K (back A b 0) ≤ q+d+1
  reverse : OddHorizon A b q

/-- At an order-specific forward surplus, the actual stage cap buys the
whole odd frame, with measured ranks and an earned last-active line. -/
theorem odd_short_frame (ha : ∀ i j, i ≤ j → A i j = 0) (ho : HasOrder A b p)
    (q2 : 2 ≤ q) (pay : 2*q+1 ≤ p) (upper : s+1 ≤ 3*q+d)
    (forward : q+d-1 ≤ finrank K (zeroSpace A q)) : OddBalancedFrame A b q d := by
  have sep := coeff_separated ho pay
  have mid := treeSpace_rank_eq_of_separation ho (q:=q) (by omega) sep
  have count := backward_endpoint_count ha ho q (q-1) pay (by omega)
  have hs : s+1=3*q+d := by omega
  have f : finrank K (zeroSpace A q)=q+d-1 := by omega
  have E : finrank K (treeSpace A q)=2*q+d := by omega
  have next := odd_next_paid_room ha ho q2 pay
  exact ⟨hs,sep,f,E,by omega,odd_horizon_of_rank ha ho (by omega) pay (by omega)⟩

end
end RKResearch.Certified.Graded.Reverse
