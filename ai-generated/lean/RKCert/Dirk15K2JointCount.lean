module

public import RKCert.Dirk15K2Residual
public import RKCert.Dirk15DeletedPencilJacobi

@[expose] public section

/-! # Exact physical tallies in the one exceptional joint block -/
namespace RKCert.Paired
open Module Polynomial RKCert.OneEscape RKCert.Endpoint
open scoped Classical
noncomputable section
variable {K : Type*} [Field K] [CharZero K]
variable {A : Fin 20→Fin 20→K} {b v : Vec K 20}

theorem finset_enum {α : Type*} (S : Finset α) :
    ∃ idx : Fin S.card→α, Function.Injective idx ∧
      (∀ i,idx i∈S) ∧ ∀ j∈S,∃ i,idx i=j := by
  let e : (↑S)≃Fin S.card := (Fintype.equivFin _).trans (finCongr (Fintype.card_coe S))
  let idx : Fin S.card→α := fun i=>(e.symm i).val
  refine ⟨idx,Subtype.val_injective.comp e.symm.injective,fun i=>(e.symm i).property,fun j hj=>?_⟩
  exact ⟨e ⟨j,hj⟩,congrArg Subtype.val (e.symm_apply_apply ⟨j,hj⟩)⟩

namespace Order15K2Head
variable (h : Order15K2Head A b v)

def jointBlock (_h : Order15K2Head A b v) (c t : K) : Finset (Fin 20) :=
  (retainedNonghostPositions A b).filter (fun i=>nodes A i=c ∧ v i=t)

omit [CharZero K] in
theorem mem_jointBlock {c t : K} {i : Fin 20} :
    i∈h.jointBlock c t ↔ i∈retainedNonghostPositions A b ∧ nodes A i=c ∧ v i=t :=
  Finset.mem_filter

set_option maxHeartbeats 1300000 in
theorem joint_block_counts (ha : LowerArray A) (ho : HasTreeOrderAtLeast A b 15)
    (H : Order15MinimalMarkedChart A b) (c t : K) :
    (h.jointBlock c t).card≤2 ∧
      ((∀ z∈h.residual,∀ i∈h.jointBlock c t,z i=0) → (h.jointBlock c t).card≤1) ∧
      ((∃ z∈h.residual,∃ a : K,a≠0 ∧ ∀ i∈h.jointBlock c t,z i=a) →
        (h.jointBlock c t).card≤1) := by
  let B := h.jointBlock c t
  obtain ⟨idx,inj,mem,onto⟩ := finset_enum B
  have rt (i : Fin B.card) := mem_retainedNonghostPositions.mp (h.mem_jointBlock.mp (mem i)).1
  have E := h.joint_restrict_cap ha ho H idx c t inj (fun i => (rt i).1)
    (fun i => (rt i).2) (fun i => (h.mem_jointBlock.mp (mem i)).2.1)
    (fun i => (h.mem_jointBlock.mp (mem i)).2.2)
  let W := h.residual.map (restrictCol idx)
  have up : finrank K W≤1 := (Submodule.finrank_map_le _ _).trans (h.rank_split H).2
  have d : B.card≤1+finrank K W := E.1
  change B.card≤2 ∧ ((∀ z∈h.residual,∀ i∈B,z i=0)→B.card≤1) ∧
    ((∃ z∈h.residual,∃ a : K,a≠0 ∧ ∀ i∈B,z i=a)→B.card≤1)
  refine ⟨by omega,fun zeros => ?_,fun live => ?_⟩
  · have we : W=⊥ := by
      apply le_antisymm _ bot_le
      rintro _ ⟨x,hx,rfl⟩
      rw [Submodule.mem_bot]
      ext i
      exact zeros x hx (idx i) (mem i)
    rw [we,finrank_bot,add_zero] at d
    exact d
  · obtain ⟨u,hu,a,an,q⟩ := live
    have z : (1:Vec K B.card)∈W := by
      refine ⟨a⁻¹ • u,h.residual.smul_mem _ hu,?_⟩
      ext i
      rw [restrictCol_apply,Pi.smul_apply,smul_eq_mul,q _ (mem i),inv_mul_cancel₀ an,Pi.one_apply]
    exact (E.2 z).trans up

/-- Strip only the genuine ghost part from the original representative
of the D relation. It is still a true pure column, with its actual
terminal value not asserted by the deleted identity. -/
theorem residual_pencil_difference (D : h.head.DeletedPencil) :
    ∃ R : K[X],R.natDegree≤4 ∧ ∃ z∈h.residual,
      ∀ i∈retainedNonghostPositions A b,
        D.D.eval (nodes A i)-v i*R.eval (nodes A i)=z i := by
  obtain ⟨u,hu,R,dR,p⟩ := D.head_profile
  have len : h.head.length=4 := by rw [Order15MinimalHead.length,h.core_two]
  have dd : R.natDegree≤4 := len ▸ dR
  rw [h.split.1] at hu
  obtain ⟨g,hg,z,hz,ue⟩ := Submodule.mem_sup.mp hu
  refine ⟨R,dd,z,hz,fun i hi => ?_⟩
  obtain ⟨nt,ng⟩ := mem_retainedNonghostPositions.mp hi
  have g0 : g i=0 := ghostPositions_vanish (v:=g) hg ng
  have e := p i nt
  have zz := congrFun ue i
  simp only [Pi.add_apply,g0,zero_add] at zz
  rw [h.physical,←zz] at e
  linear_combination e

end Order15K2Head
end
end RKCert.Paired
