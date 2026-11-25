module

public import RKCert.ReviewedNative.ERKOrder16WeakFourPhysicalSymplectic
public import RKCert.ReviewedNative.ERKOrder16WeakFourLobattoScalar
import Mathlib.Data.Fintype.EquivFin

@[expose] public section

namespace RKResearch.Certified.ERK16

open RKResearch Polynomial Module RKCert.Endpoint.WeightedClock
open RKResearch.Certified.Graded RKResearch.Certified.Graded.Reverse
open RKResearch.Certified.Graded.Reverse.Thin
open RKCert.ReviewedNative.PositiveRule19
open RKCert.ReviewedNative.WeakFourLobatto
open scoped BigOperators Classical Matrix

noncomputable section
variable {K : Type*} [Field K] [LinearOrder K] [IsStrictOrderedRing K]
variable {A : Matrix (Fin 24) (Fin 24) K} {b w : Fin 24→K}
variable {U : Submodule K (Fin 24→K)} {Q P : K[X]}

/-- Exclude only the true rank-three carrier with exactly four
physical contrast rows at four distinct numerical sites, including the
original physical origin. Repeats and an invisible origin are not
silently omitted from the ordinary weak four-site split. -/
theorem Width24OrdinaryWeakHead.weak_four_simple_active_origin_impossible
    (L : Width24OrdinaryWeakHead A b U w Q P)
    (ha : ∀ i j, i≤j → A i j=0) (ho : HasOrder 16 A b)
    (rankThree : finrank K (width24WeakFiveCarrier A b)=3)
    (four : (weightedSites (reflectedClock A) (reverseContrast A b Q P)).card=4)
    (physical : (weakFiveRows A b Q P).card=4)
    (origin : (0:Fin 24)∈weakFiveRows A b Q P) : False := by
  classical
  obtain ⟨q,θ,W,src⟩ := L.rank_three_forward_mask_with_source ha ho rankThree
  let z := reflectedClock A
  let V := weakFiveRows A b Q P
  let t := Fin.last 23
  let Cset := insert t V
  let cover := width24_quadratic_cover ha ho
  have data (i : Fin 24) (h : i∈V) :
      quadraticSeed A b i=0 ∧ z i≠0 ∧ b i≠0 ∧ Q.eval (z i)≠0 ∧ w i=0 :=
    reverse_contrast_true_support L.qFit L.pFit i ((mem_weakFiveRows i).mp h)
  have yt : z t=0 := by
    change 1-nodes A (Fin.last 23)=0
    rw [cover.frame.lastClock,sub_self]
  have y0 : z 0=1 := by
    have h : nodes A (0:Fin 24)=0 := by
      change (∑ j,A 0 j*(1:K))=0
      exact Finset.sum_eq_zero fun j _=>by rw [ha 0 j (Fin.zero_le j),zero_mul]
    change 1-nodes A 0=1
    rw [h,sub_zero]
  have nt : t∉V := fun h=>(data t h).2.1 yt
  have cc : Cset.card=5 := by
    change (insert t V).card=5
    rw [Finset.card_insert_of_notMem nt]
    change (weakFiveRows A b Q P).card+1=5
    rw [physical]
  have Vsimple : Set.InjOn z (V : Set (Fin 24)) := by
    apply Finset.card_image_iff.mp
    have image : V.image z = weightedSites (reflectedClock A) (reverseContrast A b Q P) := by
      ext a
      simp only [Finset.mem_image, mem_weightedSites, V, z, mem_weakFiveRows]
    rw [image, four]
    exact physical.symm
  let e : Fin 5 ≃ ↥Cset := Fintype.equivOfCardEq
    (by rw [Fintype.card_fin,Fintype.card_coe,cc])
  let f (i : Fin 5) := (e i).val
  have fi : Function.Injective f := fun _ _ h=>e.injective (Subtype.ext h)
  have fm (i : Fin 5) : f i∈Cset := (e i).property
  have enum (i : Fin 24) (h : i∈Cset) : ∃ j, f j=i := by
    refine ⟨e.symm ⟨i,h⟩,?_⟩
    change (e (e.symm ⟨i,h⟩)).val=i
    rw [e.apply_symm_apply]
  let y (i : Fin 5) := z (f i)
  have yi : Function.Injective y := by
    intro i j h
    apply fi
    change z (f i)=z (f j) at h
    rcases Finset.mem_insert.mp (fm i) with hi | hi <;>
      rcases Finset.mem_insert.mp (fm j) with hj | hj
    · exact hi.trans hj.symm
    · rw [hi,yt] at h
      exact False.elim ((data _ hj).2.1 h.symm)
    · rw [hj,yt] at h
      exact False.elim ((data _ hi).2.1 h)
    · exact Vsimple hi hj h
  have side : ∀ i : Fin 5, quadraticSeed A b (f i)=0 := by
    intro i
    rcases Finset.mem_insert.mp (fm i) with hi | hi
    · rw [hi]
      exact cover.lastSeed
    · exact (data (f i) hi).1
  have θOff (i : Fin 24) (hi : i∉Cset) : θ i=0 := by
    have nV : i∉V := fun h=>hi (Finset.mem_insert_of_mem h)
    have n0 : i≠0 := fun e=>nV (e.symm ▸ origin)
    have nl : i≠t := fun e=>hi (e.symm ▸ Finset.mem_insert_self _ _)
    exact W.outside i nV n0 nl
  have off (i : Fin 24) (no : ∀ j, f j≠i) : θ i=0 := by
    apply θOff i
    intro h
    obtain ⟨j,hj⟩ := enum i h
    exact no j hj
  have zeroLabel : ∃ i, y i=0 := by
    obtain ⟨i,hi⟩ := enum t (Finset.mem_insert_self _ _)
    exact ⟨i,by change z (f i)=0; rw [hi,yt]⟩
  have oneLabel : ∃ i, y i=1 := by
    obtain ⟨i,hi⟩ := enum 0 (Finset.mem_insert_of_mem origin)
    exact ⟨i,by change z (f i)=1; rw [hi,y0]⟩
  obtain ⟨H,Hd,diag⟩ := W.diagonal_on_actual_five src ha ho f fi yi off side
  let a (i : Fin 5) := b (f i)*θ (f i)
  have image : (Finset.univ : Finset (Fin 5)).image f=Cset := by
    ext i
    constructor
    · intro h
      obtain ⟨j,_,rfl⟩ := Finset.mem_image.mp h
      exact fm j
    · intro h
      obtain ⟨j,hj⟩ := enum i h
      exact Finset.mem_image.mpr ⟨j,Finset.mem_univ j,hj⟩
  have paid : Mass Q y a := by
    intro R rd
    rw [W.unweighted_mass src ho L.qDegree R rd]
    have restrict :
        (∑ i∈Cset,b i*θ i*R.eval (z i))=∑ i,b i*θ i*R.eval (z i) := by
      apply Finset.sum_subset (Finset.subset_univ _)
      intro i _ hi
      rw [θOff i hi,mul_zero,zero_mul]
    rw [←restrict,←image,Finset.sum_image fi.injOn]
  exact five_paid_diagonal_impossible L.qNonzero L.qDegree Hd yi zeroLabel oneLabel paid diag

end
end RKResearch.Certified.ERK16
