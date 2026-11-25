module

public import RKCert.ReviewedNative.ERKOrder16WeakFourFivePlusOne

@[expose] public section

namespace RKResearch.Certified.ERK16

open RKResearch Polynomial Module RKCert.OneEscape RKCert.Endpoint.WeightedClock
open RKResearch.Certified.Graded RKResearch.Certified.Graded.Reverse
open RKResearch.Certified.Graded.Reverse.Thin
open scoped BigOperators Classical Matrix

noncomputable section
variable {K : Type*} [Field K] [LinearOrder K] [IsStrictOrderedRing K]
variable {A : Matrix (Fin 24) (Fin 24) K} {b w : Fin 24→K}
variable {U : Submodule K (Fin 24→K)} {Q P : K[X]}

/-- The original inactive origin may share a numerical clock with a
different, active contrast row. In this case the five base labels still
include both endpoints. The original origin is kept as the sixth
physical row, and no diagonal identity is imposed on its joined group. -/
theorem Width24OrdinaryWeakHead.weak_four_inactive_origin_shared_clock_impossible
    (L : Width24OrdinaryWeakHead A b U w Q P)
    (ha : ∀ i j, i≤j → A i j=0) (ho : HasOrder 16 A b)
    (rankThree : finrank K (width24WeakFiveCarrier A b)=3)
    (four : (weightedSites (reflectedClock A) (reverseContrast A b Q P)).card=4)
    (physical : (weakFiveRows A b Q P).card=4)
    (inactive : (0:Fin 24)∉weakFiveRows A b Q P)
    (share : ∃ j∈weakFiveRows A b Q P, reflectedClock A j=1) : False := by
  classical
  obtain ⟨q,θ,W,src⟩ := L.rank_three_forward_mask_with_source ha ho rankThree
  let y := reflectedClock A
  let V := weakFiveRows A b Q P
  let t := Fin.last 23
  let Cset := insert t V
  let cover := width24_quadratic_cover ha ho
  have data (i : Fin 24) (hi : i∈V) :
      quadraticSeed A b i=0 ∧ y i≠0 ∧ b i≠0 ∧ Q.eval (y i)≠0 ∧ w i=0 :=
    reverse_contrast_true_support L.qFit L.pFit i ((mem_weakFiveRows i).mp hi)
  obtain ⟨j,jV,jOne⟩ := share
  change j∈V at jV
  change y j=1 at jOne
  have yt : y t=0 := by
    change 1-nodes A (Fin.last 23)=0
    rw [cover.frame.lastClock,sub_self]
  have nt : t∉V := fun h=>(data t h).2.1 yt
  have originClock : y 0=1 := by
    have h : nodes A (0:Fin 24)=0 := by
      change (∑ i,A 0 i*(1:K))=0
      exact Finset.sum_eq_zero fun i _=>by rw [ha 0 i (Fin.zero_le i),zero_mul]
    change 1-nodes A 0=1
    rw [h,sub_zero]
  have Q1 : Q.eval 1≠0 := by
    have h := (data j jV).2.2.2.1
    rwa [jOne] at h
  have w5 : w∈zeroSpace A 5 := by
    have flag : zeroSpace A 5=chain (diag (nodes A)) U w 2 := L.flat.flags 0 (by decide)
    rw [flag]
    have h := ((clock_chain_le_iff (T:=diag (nodes A)) (U:=U) (w:=w) 2).mp le_rfl).2
      0 (by decide)
    simpa only [pow_zero,Module.End.one_eq_id,LinearMap.id_apply] using h
  have w0 : w 0=0 := origin_zeroSpace ha 5 w5
  have d0 : quadraticSeed A b 0=0 := by
    have h := L.qFit 0
    change quadraticSeed A b 0*w 0=Q.eval (y 0)*quadraticSeed A b 0 at h
    rw [w0,originClock,mul_zero] at h
    exact (mul_eq_zero.mp h.symm).resolve_left Q1
  have Vsimple : Set.InjOn y (V : Set (Fin 24)) := by
    apply Finset.card_image_iff.mp
    have image : V.image y=weightedSites (reflectedClock A) (reverseContrast A b Q P) := by
      ext a
      simp only [Finset.mem_image,mem_weightedSites,V,y,mem_weakFiveRows]
    rw [image,four]
    exact physical.symm
  have baseSimple : Set.InjOn y (Cset : Set (Fin 24)) := by
    intro i hi k hk eq
    rcases Finset.mem_insert.mp hi with hi|hi <;>
      rcases Finset.mem_insert.mp hk with hk|hk
    · exact hi.trans hk.symm
    · rw [hi,yt] at eq
      exact False.elim ((data k hk).2.1 eq.symm)
    · rw [hk,yt] at eq
      exact False.elim ((data i hi).2.1 eq)
    · exact Vsimple hi hk eq
  have five : Cset.card=5 := by
    change (insert t V).card=5
    rw [Finset.card_insert_of_notMem nt,show V.card=4 from physical]
  have originOut : (0:Fin 24)∉Cset := by
    intro h
    rcases Finset.mem_insert.mp h with eq|hv
    · exact (by decide : (0:Fin 24)≠Fin.last 23) eq
    · exact inactive hv
  have M : WeakFourGradedMask A b θ q Q (insert (0:Fin 24) Cset) := by
    refine ⟨W.degree,W.reflected,src,?_,?_⟩
    · intro i hi
      have hv : i∉V := fun h=>hi (Finset.mem_insert_of_mem (Finset.mem_insert_of_mem h))
      have h0 : i≠0 := fun e=>hi (e.symm ▸ Finset.mem_insert_self _ _)
      have ht : i≠t := fun e=>hi (e.symm ▸ Finset.mem_insert_of_mem (Finset.mem_insert_self _ _))
      exact W.outside i hv h0 ht
    · intro i hi
      rcases Finset.mem_insert.mp hi with rfl|hc
      · exact d0
      · rcases Finset.mem_insert.mp hc with rfl|hv
        · exact cover.lastSeed
        · exact (data i hv).1
  exact M.five_plus_one_impossible ha ho L.qNonzero L.qDegree five originOut baseSimple
    ⟨t,Finset.mem_insert_self _ _,yt⟩
    ⟨j,Finset.mem_insert_of_mem jV,jOne⟩
    (Or.inl ⟨j,Finset.mem_insert_of_mem jV,jOne.trans originClock.symm⟩)

end
end RKResearch.Certified.ERK16
