module

public import RKCert.Dirk15DeletedScalarReduction

@[expose] public section

/-! # The folded head relation is the only later scalar correction -/
namespace RKCert.Paired
open Module Polynomial RKCert.OneEscape RKCert.Endpoint
open scoped Classical
noncomputable section
variable {K : Type*} [Field K] [CharZero K]
variable {A : Fin 20 → Fin 20 → K} {b : Vec K 20}

namespace Order15MinimalHead
variable (h : Order15MinimalHead A b)

set_option maxHeartbeats 1250000 in
theorem folded_scalar_zero (ha : LowerArray A) (ho : HasTreeOrderAtLeast A b 15)
    (H : Order15MinimalMarkedChart A b)
    (folded : deleteTerminal K 19 (((diag (nodes A))^h.length) h.w)∈deletedTreeSpace A 7)
    {P : K[X]} (dP : P.natDegree≤11)
    (ev : deleteTerminal K 19 (evalNodes A P)∈deletedHeadOrbit A h.U h.w h.length) : P=0 := by
  let L := deletedHeadOrbit A h.U h.w h.length
  let S := deletedScalarOrbit A 11
  let e := (deleteTerminal K 19).comp (polyEval A 11)
  have len := h.length_sum
  have ds : deletedTreeSpace A 11=S⊔L := by
    rcases h.deleted_growth_dichotomy ha ho H with ⟨_,growth⟩|⟨op,_⟩
    · exact growth 4 (by decide)
    · exact (op folded).elim
  have dis := h.deleted_direct ha ho H (by decide) (by decide) (by omega) ds
  have d18 := (order15_minimal_deleted_band ha ho H 11 (by decide) (by decide)).2
  rw [ds] at d18
  have rank := Submodule.finrank_sup_add_finrank_inf_eq S L
  change Disjoint S L at dis
  rw [dis.eq_bot,finrank_bot,add_zero,d18] at rank
  have ub := h.deleted_head_rank_upper h.length
  change finrank K L≤finrank K h.U+h.length at ub
  have scalarLower : 12≤finrank K S := by omega
  have er : LinearMap.range e=S := by
    change LinearMap.range ((deleteTerminal K 19).comp (polyEval A 11))=deletedScalarOrbit A 11
    rw [LinearMap.range_comp,deletedScalarOrbit_eq]
  have r := e.finrank_range_add_finrank_ker
  rw [er,Module.finrank_fin_fun] at r
  have ker0 : LinearMap.ker e=⊥ := Submodule.finrank_eq_zero.mp (by omega)
  have inj := LinearMap.ker_eq_bot.mp ker0
  let a : Fin 12→K := fun i => P.coeff i.val
  have ea : e a=deleteTerminal K 19 (evalNodes A P) := by
    change deleteTerminal K 19 (polyEval A 11 a)=_
    rw [evalNodes_eq_polyEval A _ dP]
  have z : e a∈S⊓L := ⟨er ▸ LinearMap.mem_range_self e a,ea.symm ▸ ev⟩
  rw [dis.eq_bot,Submodule.mem_bot] at z
  have coeff := inj (show e a=e 0 by rw [z,map_zero])
  ext j
  rw [coeff_zero]
  by_cases h : j<12
  · exact congrFun coeff ⟨j,h⟩
  · exact coeff_eq_zero_of_natDegree_lt (by omega)

end Order15MinimalHead

namespace Order15MinimalHead.DeletedPencil
variable {h : Order15MinimalHead A b} (D : h.DeletedPencil)

set_option maxHeartbeats 1600000 in
theorem folded_scalar_reduces (ha : LowerArray A) (ho : HasTreeOrderAtLeast A b 15)
    (H : Order15MinimalMarkedChart A b)
    (folded : deleteTerminal K 19 (((diag (nodes A))^h.length) h.w)∈deletedTreeSpace A 7)
    {P : K[X]} (dP : P.natDegree≤11)
    (ev : deleteTerminal K 19 (evalNodes A P)∈deletedHeadOrbit A h.U h.w (h.length+1)) :
    ∃ a : K, P=C a*D.D := by
  let L := deletedHeadOrbit A h.U h.w
  let e := (deleteTerminal K 19).comp (evaluateColumn A)
  let d := h.length
  have dpos : 0<d := h.length_pos
  have Dne : D.D≠0 := by
    intro z
    have t := D.dmin
    rw [z,natDegree_zero] at t
    omega
  have D7 : D.D.natDegree=7 := by simpa [folded] using D.growth
  have unpaid : e D.D∉L d := by
    intro hD
    exact Dne (h.folded_scalar_zero ha ho H folded (D7.le.trans (by decide)) hD)
  have mem : e D.D∈L (d+1) := by
    change deleteTerminal K 19 (evalNodes A D.D)∈deletedHeadOrbit A h.U h.w (d+1)
    rw [D.eq,deletedHeadOrbit_eq]
    exact Submodule.mem_map_of_mem D.genuine
  have step : L (d+1)=L d⊔K∙(((deletedClock A)^d) (deleteTerminal K 19 h.w)) := rfl
  have cap : finrank K (L (d+1))≤finrank K (L d)+1 := by
    rw [step]
    let a := ((deletedClock A)^d) (deleteTerminal K 19 h.w)
    change finrank K (L d⊔K∙a : Submodule K (Vec K 19))≤finrank K (L d)+1
    have t := Submodule.finrank_sup_add_finrank_inf_eq (L d) (K∙a)
    have up : finrank K (K∙a)≤1 := by
      by_cases z : a=0
      · rw [z,Submodule.span_zero_singleton,finrank_bot]; decide
      · exact (finrank_span_singleton z).le
    omega
  have exact_step : L (d+1)=L d⊔K∙(e D.D) := by
    have small : L d≤L (d+1) := clock_chain_mono (Nat.le_succ d)
    have inc : L d⊔K∙e D.D≤L (d+1) :=
      sup_le small ((Submodule.span_singleton_le_iff_mem _ _).mpr mem)
    apply (Submodule.eq_of_le_of_finrank_le inc ?_).symm
    rwa [Submodule.finrank_sup_span_singleton unpaid]
  change e P∈L (d+1) at ev
  rw [exact_step] at ev
  obtain ⟨v,hv,z,hz,eq⟩ := Submodule.mem_sup.mp ev
  obtain ⟨a,rfl⟩ := Submodule.mem_span_singleton.mp hz
  have t : e (P-C a*D.D)∈L d := by
    rw [←smul_eq_C_mul,map_sub,map_smul,←eq,add_sub_cancel_right]
    exact hv
  have td : (P-C a*D.D).natDegree≤11 := (natDegree_sub_le _ _).trans
    (max_le dP ((natDegree_C_mul_le _ _).trans (D7.le.trans (by decide))))
  exact ⟨a,sub_eq_zero.mp (h.folded_scalar_zero ha ho H folded td t)⟩

end Order15MinimalHead.DeletedPencil
end
end RKCert.Paired
