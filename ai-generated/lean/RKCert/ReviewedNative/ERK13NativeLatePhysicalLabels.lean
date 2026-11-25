module

public import RKCert.ReviewedNative.ERK13NativeLatePhysicalFold
import Mathlib.Data.Finset.Max
import Mathlib.Data.Finset.Card
import Mathlib.Data.Set.Finite.Basic

@[expose] public section

/-! # Literal first representatives and the unique omitted order-13 row

As in `HyperplanePhysicalLabels`, the representative of each class is
its earliest original row. The late seam has 18 marked labels on 19
stages. Its unique omission is located by the paid positive reflected
row, not chosen by sorting numerical clocks. -/

namespace RKResearch.Certified.Graded.ERK13NativeLatePhysicalFold

open RKResearch Reverse HyperplaneTerminal
open scoped Classical Matrix BigOperators

noncomputable section

variable {K α : Type*} [Field K] [CharZero K] [DecidableEq α]
variable {A : Matrix (Fin 19) (Fin 19) K} {b : Fin 19 → K}

private theorem last_off_one_exists (ho : HasOrder 13 A b) :
    ∃ m : Fin 19, b m ≠ 0 ∧ reflectedClock A m ≠ 0 ∧
      ∀ i, m < i → b i*reflectedClock A i=0 := by
  classical
  let S := Finset.univ.filter (fun i : Fin 19 => b i*reflectedClock A i ≠ 0)
  have sn : S.Nonempty := by
    by_contra off
    have z (i : Fin 19) : b i*reflectedClock A i=0 := by
      by_contra hz
      exact off ⟨i,Finset.mem_filter.mpr ⟨Finset.mem_univ _,hz⟩⟩
    apply reflected_target_ne_zero ho (by decide)
    simp only [row_apply,dotProduct,diag_apply,Pi.one_apply,mul_one]
    apply Finset.sum_eq_zero
    intro i _
    rw [mul_comm,z i]
  let m := S.max' sn
  have mm : m ∈ S := S.max'_mem sn
  have mlive := (Finset.mem_filter.mp mm).2
  refine ⟨m,fun hz => mlive (by rw [hz,zero_mul]),
    fun hz => mlive (by rw [hz,mul_zero]),fun i hi => ?_⟩
  by_contra zi
  exact (not_lt_of_ge (S.le_max' i (Finset.mem_filter.mpr
    ⟨Finset.mem_univ _,zi⟩))) hi

private theorem positive_row_at_or_after {m : Fin 19}
    (ha : ∀ i j, i ≤ j → A i j=0) (tail : ∀ i, m < i → b i*reflectedClock A i=0)
    (i : Fin 19) (hi : m ≤ i) :
    reflectedStageRow A b 1 i = -(b i*reflectedClock A i^2) := by
  have cut : mat A.transpose (reflectedStageWeight A b 1) i=0 := by
    change (∑ j : Fin 19, A j i*(b j*reflectedClock A j^1))=0
    simp only [pow_one]
    apply Finset.sum_eq_zero
    intro j _
    by_cases h : j ≤ i
    · rw [ha j i h,zero_mul]
    · rw [tail j (hi.trans_lt (lt_of_not_ge h)),mul_zero]
  change (((1+1:ℕ):K)*mat A.transpose (reflectedStageWeight A b 1) i -
    b i*reflectedClock A i^2) = _
  rw [cut,mul_zero,zero_sub]

/-- The physical label chart supplies the unique earlier representative of
the last b-live off-one row and retains every other original row. No
remaining class support or ratio hypothesis is assumed here. -/
theorem actual_pair_of_marked_labels (ha : ∀ i j, i ≤ j → A i j=0)
    (ho : HasOrder 13 A b) (seed : firstSeed A b=0)
    (f : Fin 19→α) (card : (Finset.univ.image f).card=18)
    (cy : ∀ i j, f i=f j → reflectedClock A i=reflectedClock A j)
    (masks : ∀ t : Fin 19, (fun i => if f i=f t then (1:K) else 0) ∈ markedTreeSpace A b 10) :
    ∃ (e : Fin 18→Fin 19) (r : Fin 19→Fin 18) (m : Fin 19),
      PairClasses e r m ∧
      (∀ i t, r i=t ↔ f i=f (e t)) ∧
      (∀ i, reflectedClock A (e (r i))=reflectedClock A i) ∧
      b m ≠ 0 ∧ reflectedClock A m ≠ 0 ∧
      (∀ i, m < i → b i*reflectedClock A i=0) ∧
      (∀ t : Fin 18,(fun i=> coordinate (K:=K) t (r i)) ∈ treeSpace A 10 ⊔ K∙coordinate (Fin.last 18)) := by
  classical
  obtain ⟨m,live,offOne,tail⟩ := last_off_one_exists ho
  -- Use the same chronological representatives as HyperplanePhysicalLabels.
  let first (i : Fin 19) := ∀ h, h < i → f h ≠ f i
  let S := Finset.univ.filter first
  have once : Set.InjOn f (S : Set (Fin 19)) := by
    intro i hi h hh eq
    have a := (Finset.mem_filter.mp hi).2
    have d := (Finset.mem_filter.mp hh).2
    rcases lt_trichotomy i h with k|k|k
    · exact (d i k eq).elim
    · exact k
    · exact (a h k eq.symm).elim
  have any_rep (i : Fin 19) : ∃ h ∈ S, h ≤ i ∧ f h=f i := by
    let T : Set (Fin 19) := {h | f h=f i}
    obtain ⟨h,hh,least⟩ := wellFounded_lt.has_min T ⟨i,rfl⟩
    have hfirst : first h := fun v prior eq=> least v (eq.trans hh) prior
    exact ⟨h,Finset.mem_filter.mpr ⟨Finset.mem_univ _,hfirst⟩,
      le_of_not_gt (least i rfl),hh⟩
  have image : S.image f=Finset.univ.image f := by
    apply Finset.Subset.antisymm (Finset.image_subset_image (Finset.subset_univ S))
    intro z hz
    obtain ⟨i,_,rfl⟩ := Finset.mem_image.mp hz
    obtain ⟨h,hh,_,eq⟩ := any_rep i
    exact Finset.mem_image.mpr ⟨h,hh,eq⟩
  have size : S.card=18 := by
    rw [←Finset.card_image_of_injOn once,image,card]
  let e := S.orderEmbOfFin size
  have repr (i : Fin 19) : ∃ t : Fin 18, e t ≤ i ∧ f (e t)=f i := by
    obtain ⟨h,hh,earlier,label⟩ := any_rep i
    have ran : h ∈ Set.range e := by
      rw [Finset.range_orderEmbOfFin]
      exact hh
    obtain ⟨t,rfl⟩ := ran
    exact ⟨t,earlier,label⟩
  choose r earlier label using repr
  have fibres (i : Fin 19) (t : Fin 18) : r i=t ↔ f i=f (e t) := by
    constructor
    · intro eq
      rw [←eq]
      exact (label i).symm
    · intro eq
      apply e.injective
      exact once (S.orderEmbOfFin_mem size _) (S.orderEmbOfFin_mem size _) ((label i).trans eq)
  have lifts (t : Fin 18) : (fun i=> coordinate (K:=K) t (r i)) ∈ treeSpace A 10 ⊔ K∙coordinate (Fin.last 18) := by
    have mask : (fun i=> coordinate (K:=K) t (r i))=
        (fun i=> if f i=f (e t) then (1:K) else 0) := by
      ext i
      by_cases eq : r i=t
      · simp [coordinate,eq,(fibres i t).mp eq]
      · have de : f i ≠ f (e t) := fun h=> eq ((fibres i t).mpr h)
        simp [coordinate,eq,Ne.symm eq,de]
    rw [mask]
    simpa only [markedTreeSpace,terminalMark,if_pos seed] using masks (e t)
  let rho := reflectedStageRow A b 1
  have fld : ∀ t, foldLinear r rho t=0 := fold_first_paid ha ho seed lifts
  have nz : rho m ≠ 0 := by
    change reflectedStageRow A b 1 m ≠ 0
    rw [positive_row_at_or_after ha tail m le_rfl]
    exact neg_ne_zero.mpr (mul_ne_zero live (pow_ne_zero _ offOne))
  have quiet (i : Fin 19) (hi : m < i) : rho i=0 := by
    change reflectedStageRow A b 1 i=0
    rw [positive_row_at_or_after ha tail i hi.le,pow_two,←mul_assoc,tail i hi,zero_mul,neg_zero]
  have notFirst : m∉S := by
    intro hS
    have minimal := (Finset.mem_filter.mp hS).2
    have later (i : Fin 19) (fib : r i=r m) (ne : i ≠ m) : m < i := by
      by_contra notLater
      have eq : f i=f m := ((fibres i (r m)).mp fib).trans (label m)
      exact minimal i (lt_of_le_of_ne (le_of_not_gt notLater) ne) eq
    have h := fld (r m)
    change (∑ i ∈ Finset.univ.filter (fun i => r i=r m),rho i)=0 at h
    rw [Finset.sum_eq_single m] at h
    · exact nz h
    · intro i hi ine
      exact quiet i (later i (Finset.mem_filter.mp hi).2 ine)
    · simp
  have erase : S=Finset.univ.erase m := by
    apply Finset.eq_of_subset_of_card_le
    · intro i hi
      refine Finset.mem_erase.mpr ⟨fun h => notFirst (h ▸ hi),Finset.mem_univ _⟩
    · simp [Finset.card_erase_of_mem (Finset.mem_univ m), size]
  have kept (i : Fin 19) (hi : i ≠ m) : e (r i)=i := by
    have is : i ∈ S := by rw [erase]; exact Finset.mem_erase.mpr ⟨hi,Finset.mem_univ _⟩
    exact once (S.orderEmbOfFin_mem size _) is (label i)
  have omitted : e (r m) ≠ m := by
    intro eq
    exact notFirst (eq ▸ S.orderEmbOfFin_mem size (r m))
  exact ⟨e,r,m,⟨e.monotone,earlier,omitted,kept⟩,
    fibres,(fun i => cy _ _ (label i)),live,offOne,tail,lifts⟩

end
end RKResearch.Certified.Graded.ERK13NativeLatePhysicalFold
