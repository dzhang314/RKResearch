module

public import Mathlib.LinearAlgebra.FiniteDimensional.Lemmas

@[expose] public section

/-! An abstract rank gate used in the two-clock single-ghost branch.
There is no RK order condition hidden in this statement. -/
namespace RKResearch.ERK10SingleGhost
open Module
variable {K V : Type*} [Field K] [AddCommGroup V] [Module K V] [Module.Finite K V]

/-- A two-dimensional cyclic lane containing the single generator of the
reverse filtration must be the whole rank-two filtration if the rank-three
room is not stable. The companion case of proportional generators uses
the actual clock move on the generator. -/
theorem twoClockLane (D : Module.End K V)
    {U W R : Submodule K V} {r h : V}
    (uW : U ≤ W) (rW : R ≤ W)
    (dU : finrank K U = 2) (dW : finrank K W = 3) (dR : finrank K R = 2)
    (Rstable : R.map D ≤ R) (Wunstable : ¬ W.map D ≤ W)
    (rU : r ∈ U) (rR : r ∈ R) (rNZ : r ≠ 0)
    (hU : h ∈ U) (hNZ : h ≠ 0) (DhU : D h ∈ U)
    (DrR : D r ∈ R) (DrFree : D r ∉ Submodule.span K {r}) :
    U = R := by
  classical
  let L : Submodule K V := Submodule.span K {r}
  have LU : L ≤ U := (Submodule.span_singleton_le_iff_mem ..).mpr rU
  have LR : L ≤ R := (Submodule.span_singleton_le_iff_mem ..).mpr rR
  have dL : finrank K L = 1 := finrank_span_singleton rNZ
  have hR : h ∈ R := by
    by_contra hn
    have eq : R ⊔ Submodule.span K {h} = W := by
      apply Submodule.eq_of_le_of_finrank_le
      · exact sup_le rW ((Submodule.span_singleton_le_iff_mem ..).mpr (uW hU))
      · rw [Submodule.finrank_sup_span_singleton hn, dR, dW]
    apply Wunstable
    rintro _ ⟨v,hv,rfl⟩
    rw [← eq] at hv
    obtain ⟨x,hx,y,hy,rfl⟩ := Submodule.mem_sup.mp hv
    have dx : D x ∈ W := rW (Rstable (Submodule.mem_map_of_mem hx))
    obtain ⟨a,rfl⟩ := Submodule.mem_span_singleton.mp hy
    rw [map_add,map_smul]
    exact W.add_mem dx (W.smul_mem a (uW DhU))
  by_cases hl : h ∈ L
  · obtain ⟨a,ha⟩ := Submodule.mem_span_singleton.mp hl
    have ha0 : a ≠ 0 := by
      intro h0
      apply hNZ
      rw [← ha,h0,zero_smul]
    have drU : D r ∈ U := by
      have q := U.smul_mem a⁻¹ DhU
      rw [← ha,map_smul,smul_smul,inv_mul_cancel₀ ha0,one_smul] at q
      exact q
    have E : L ⊔ Submodule.span K {D r} = R := by
      apply Submodule.eq_of_le_of_finrank_le
      · exact sup_le LR ((Submodule.span_singleton_le_iff_mem ..).mpr DrR)
      · rw [Submodule.finrank_sup_span_singleton DrFree,dL,dR]
    symm
    apply Submodule.eq_of_le_of_finrank_le
    · rw [← E]
      exact sup_le LU ((Submodule.span_singleton_le_iff_mem ..).mpr drU)
    · rw [dU,dR]
  · have E : L ⊔ Submodule.span K {h} = U := by
      apply Submodule.eq_of_le_of_finrank_le
      · exact sup_le LU ((Submodule.span_singleton_le_iff_mem ..).mpr hU)
      · rw [Submodule.finrank_sup_span_singleton hl,dL,dU]
    apply Submodule.eq_of_le_of_finrank_le
    · rw [← E]
      exact sup_le LR ((Submodule.span_singleton_le_iff_mem ..).mpr hR)
    · rw [dR,dU]

end RKResearch.ERK10SingleGhost
#print axioms RKResearch.ERK10SingleGhost.twoClockLane
