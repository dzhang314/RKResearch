module

public import RKCert.ReviewedNative.ERKOrder16WeakFourGroupedSymplectic
public import RKCert.ReviewedNative.ERKOrder16WeakFourGroupedLobatto
import Mathlib.Data.Fintype.EquivFin

@[expose] public section

namespace RKResearch.Certified.ERK16

open RKResearch Polynomial
open RKResearch.Certified.Graded RKResearch.Certified.Graded.Reverse
open RKCert.ReviewedNative.WeakFourLobatto
open scoped BigOperators Classical Matrix

noncomputable section
variable {K : Type*} [Field K] [LinearOrder K] [IsStrictOrderedRing K]
variable {A : Matrix (Fin 24) (Fin 24) K} {b θ : Fin 24→K}
variable {q Q : K[X]}

private theorem fibre_single {C : Finset (Fin 24)} {j i : Fin 24}
    (iC : i∈C) (simple : Set.InjOn (reflectedClock A) (C : Set (Fin 24)))
    (off : reflectedClock A i≠reflectedClock A j) :
    (insert j C).filter (fun k=>reflectedClock A k=reflectedClock A i)={i} := by
  ext k
  simp only [Finset.mem_filter,Finset.mem_singleton]
  constructor
  · rintro ⟨mem,e⟩
    rcases Finset.mem_insert.mp mem with h|h
    · exact False.elim (off (e.symm.trans (congrArg (reflectedClock A) h)))
    · exact simple h iC e
  · rintro rfl
    exact ⟨Finset.mem_insert_of_mem iC,rfl⟩

/-- Five true paid numerical labels with physical endpoints and one further
actual coordinate. The latter can either repeat a label or have zero
original mass. Both the mass and the grouped diagonal are obtained from
the original six physical columns; no virtual stages are introduced. -/
theorem WeakFourGradedMask.five_plus_one_impossible
    {C : Finset (Fin 24)} {j : Fin 24}
    (W : WeakFourGradedMask A b θ q Q (insert j C))
    (ha : ∀ i k,i≤k→A i k=0) (ho : HasOrder 16 A b)
    (qn : Q≠0) (qd : Q.natDegree≤4)
    (count : C.card=5) (_out : j∉C)
    (distinct : Set.InjOn (reflectedClock A) (C : Set (Fin 24)))
    (zero : ∃ i∈C,reflectedClock A i=0) (one : ∃ i∈C,reflectedClock A i=1)
    (extra : (∃ i∈C,reflectedClock A i=reflectedClock A j) ∨ b j=0) : False := by
  classical
  let e : Fin 5 ≃ ↥C := Fintype.equivOfCardEq
    (by rw [Fintype.card_fin,Fintype.card_coe,count])
  let f (i : Fin 5) := (e i).val
  have fm (i : Fin 5) : f i∈C := (e i).property
  have enum (i : Fin 24) (h : i∈C) : ∃ k, f k=i := by
    refine ⟨e.symm ⟨i,h⟩,?_⟩
    exact congrArg Subtype.val (e.apply_symm_apply ⟨i,h⟩)
  let y (i : Fin 5) := reflectedClock A (f i)
  let ξ := reflectedClock A j
  have yi : Function.Injective y := fun i k h=>e.injective (Subtype.ext (distinct (fm i) (fm k) h))
  have yz : ∃ i,y i=0 := by
    obtain ⟨i,hi,zi⟩ := zero
    obtain ⟨k,hk⟩ := enum i hi
    exact ⟨k,(congrArg (reflectedClock A) hk).trans zi⟩
  have yo : ∃ i,y i=1 := by
    obtain ⟨i,hi,oi⟩ := one
    obtain ⟨k,hk⟩ := enum i hi
    exact ⟨k,(congrArg (reflectedClock A) hk).trans oi⟩
  by_cases rep : ∃ i,y i=ξ
  · obtain ⟨bad,hbad⟩ := rep
    have all (i : Fin 24) (hi : i∈insert j C) : ∃ k,y k=reflectedClock A i := by
      rcases Finset.mem_insert.mp hi with rfl|hc
      · exact ⟨bad,hbad⟩
      · obtain ⟨k,hk⟩ := enum i hc
        exact ⟨k,congrArg (reflectedClock A) hk⟩
    obtain ⟨H,Hd,M,D⟩ := W.grouped_diagonal (d:=1) le_rfl ha ho qd y yi all
    let a (i : Fin 5) := row b (weakFourGroupColumn A θ (insert j C) (y i))
    have diag (i : Fin 5) (hi : i≠bad) :
        H.eval (y i)=(a i*RKCert.ReviewedNative.FiveNodalDiagonal.slope y i)^2 := by
      have ni : y i≠ξ := fun h=>hi (yi (h.trans hbad.symm))
      obtain ⟨h,s⟩ := D i (f i) (fibre_single (fm i) distinct ni)
      rw [show a i=b (f i)*θ (f i) from s]
      exact h
    exact five_paid_repeated_group_impossible bad qn qd (by simpa using Hd) yi yz yo M diag
  · have extra0 : b j=0 := by
      rcases extra with ⟨i,hi,eq⟩|h
      · obtain ⟨k,hk⟩ := enum i hi
        exact False.elim (rep ⟨k,(congrArg (reflectedClock A) hk).trans eq⟩)
      · exact h
    let z : Fin 6→K := Fin.cases ξ y
    have zs : Function.Injective z := by
      intro i k
      refine Fin.cases ?_ (fun i=>?_) i <;> refine Fin.cases ?_ (fun k=>?_) k
      · intro _
        rfl
      · intro eq
        exact False.elim (rep ⟨k,eq.symm⟩)
      · intro eq
        exact False.elim (rep ⟨i,eq⟩)
      · intro eq
        exact congrArg Fin.succ (yi eq)
    have all (i : Fin 24) (hi : i∈insert j C) : ∃ k,z k=reflectedClock A i := by
      rcases Finset.mem_insert.mp hi with rfl|hc
      · exact ⟨0,rfl⟩
      · obtain ⟨k,hk⟩ := enum i hc
        exact ⟨k.succ,congrArg (reflectedClock A) hk⟩
    obtain ⟨H,Hd,M,D⟩ := W.grouped_diagonal (d:=2) (by decide) ha ho qd z zs all
    let a (i : Fin 5) := row b (weakFourGroupColumn A θ (insert j C) (y i))
    have jonly : (insert j C).filter (fun k=>reflectedClock A k=ξ)={j} := by
      ext i
      simp only [Finset.mem_filter,Finset.mem_singleton]
      constructor
      · rintro ⟨hi,eq⟩
        rcases Finset.mem_insert.mp hi with e|hc
        · exact e
        · obtain ⟨k,hk⟩ := enum i hc
          exact False.elim (rep ⟨k,(congrArg (reflectedClock A) hk).trans eq⟩)
      · rintro rfl
        exact ⟨Finset.mem_insert_self _ _,rfl⟩
    obtain ⟨edge,edgeMass⟩ := D 0 j jonly
    have mass0 : row b (weakFourGroupColumn A θ (insert j C) (z 0))=0 := by
      rw [edgeMass,extra0,zero_mul]
    have Hv : H.eval ξ=0 := by
      change H.eval (z 0)=0
      rw [edge,extra0,zero_mul,zero_mul,zero_pow (by decide : (2:ℕ)≠0)]
    have paid : Mass Q y a := by
      intro R rd
      rw [M R rd,Fin.sum_univ_succ,mass0,zero_mul,zero_add] <;> rfl
    have diag (i : Fin 5) (hf : y i≠ξ) :
        H.eval (y i)=(a i*RKCert.ReviewedNative.NodalOddDiagonal.slope (Fin.cases ξ y) i.succ)^2 := by
      obtain ⟨h,s⟩ := D i.succ (f i) (fibre_single (fm i) distinct hf)
      rw [show a i=b (f i)*θ (f i) from s]
      exact h
    exact five_paid_with_zero_mass_extra_impossible qn qd (by simpa using Hd) yi yz yo paid
      (fun i h=>rep ⟨i,h⟩) Hv (fun i=>diag i (fun ep=>rep ⟨i,ep⟩))

end
end RKResearch.Certified.ERK16
