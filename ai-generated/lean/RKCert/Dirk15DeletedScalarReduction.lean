module

public import RKCert.Dirk15DeletedPencil

@[expose] public section

/-! # Unique scalar correction in the unfolded deleted head band

This is the exact numerical comparison needed at grade eleven. The small
scalar evaluation remains injective because the original E7 restriction
is injective at the genuine terminal, not because the deleted array is
assumed to meet any order conditions.
-/
namespace RKCert.Paired
open Module Polynomial RKCert.OneEscape
open scoped Classical
noncomputable section
variable {K : Type*} [Field K] [CharZero K]
variable {A : Fin 20 → Fin 20 → K} {b : Vec K 20}

omit [CharZero K] in
theorem order15_deleted_small_scalar_zero (ho : HasTreeOrderAtLeast A b 15)
    (H : Order15MinimalMarkedChart A b) {P : K[X]} (dP : P.natDegree≤7)
    (eval : deleteTerminal K 19 (evalNodes A P)=0) : P=0 := by
  have e : evalNodes A P∈treeSpace A 7 := by
    rw [evalNodes_eq_polyEval A _ dP]
    exact polyEval_mem_treeSpace _ _ _
  have eq := deleteTerminal_inj_on H.terminal_not_mem
    (a₁:=⟨evalNodes A P,e⟩) (a₂:=⟨0,(treeSpace A 7).zero_mem⟩) (by simpa using eval)
  have z : evalNodes A P=0 := congrArg Subtype.val eq
  have a := poly_separated ho (by decide : 2*7+1≤15)
    (fun i => P.coeff i.val) (by
      rw [←evalNodes_eq_polyEval A _ dP,z]
      exact (zeroSpace A 7).zero_mem)
  ext j
  rw [coeff_zero]
  by_cases h : j<8
  · exact congrFun a ⟨j,h⟩
  · exact coeff_eq_zero_of_natDegree_lt (by omega)

namespace Order15MinimalHead.DeletedPencil
variable {h : Order15MinimalHead A b} (D : h.DeletedPencil)

set_option maxHeartbeats 1500000 in
theorem unfolded_scalar_reduces (ha : LowerArray A) (ho : HasTreeOrderAtLeast A b 15)
    (H : Order15MinimalMarkedChart A b)
    (unfolded : deleteTerminal K 19 (((diag (nodes A))^h.length) h.w)∉deletedTreeSpace A 7)
    {P : K[X]} (dP : P.natDegree≤8)
    (inHead : deleteTerminal K 19 (evalNodes A P)∈deletedHeadOrbit A h.U h.w (h.length+4)) :
    ∃ a : K,P=C a*D.D := by
  let L := deletedHeadOrbit A h.U h.w
  let e := (deleteTerminal K 19).comp (evaluateColumn A)
  have d8 : D.D.natDegree=8 := by simpa [unfolded] using D.growth
  have nz : D.D≠0 := fun e => by rw [e,natDegree_zero] at d8; contradiction
  have lc : D.D.coeff 8≠0 := by
    rw [←d8,coeff_natDegree]
    exact leadingCoeff_ne_zero.mpr nz
  have dh : e D.D∈L (h.length+4) := by
    change deleteTerminal K 19 (evalNodes A D.D)∈deletedHeadOrbit A h.U h.w (h.length+4)
    rw [D.eq,deletedHeadOrbit_eq]
    exact Submodule.mem_map_of_mem (clock_chain_mono (by omega : h.length+1≤h.length+4) D.genuine)
  let a := P.coeff 8/D.D.coeff 8
  let T := P-C a*D.D
  have rt : T.natDegree≤8 :=
    (natDegree_sub_le _ _).trans (max_le dP ((natDegree_C_mul_le _ _).trans d8.le))
  have z : T.coeff 8=0 := by
    simp only [T,coeff_sub,coeff_C_mul,a,div_mul_cancel₀ _ lc,sub_self]
  have td : T.natDegree≤7 := by
    apply natDegree_le_iff_coeff_eq_zero.mpr
    intro j hj
    by_cases l : j=8
    · rwa [l]
    · exact coeff_eq_zero_of_natDegree_lt (by omega)
  have th : e T∈L (h.length+4) := by
    change e (P-C a*D.D)∈L (h.length+4)
    rw [←smul_eq_C_mul,map_sub,map_smul]
    exact (L (h.length+4)).sub_mem inHead ((L (h.length+4)).smul_mem a dh)
  have ts : e T∈deletedScalarOrbit A 7 := by
    change deleteTerminal K 19 (evalNodes A T)∈deletedScalarOrbit A 7
    rw [deletedScalarOrbit_eq]
    apply Submodule.mem_map_of_mem
    rw [evalNodes_eq_polyEval A _ td]
    exact LinearMap.mem_range_self _ _
  have split : deletedTreeSpace A 11=deletedScalarOrbit A 7⊔L (h.length+4) := by
    rcases h.deleted_growth_dichotomy ha ho H with ⟨bad,_⟩|⟨_,band⟩
    · exact (unfolded bad).elim
    · exact band 4 (by decide)
  have sep := h.deleted_direct ha ho H (by decide) (by decide)
    (by have := h.length_sum; omega) split
  have vanish : e T=0 := by
    have y : e T∈deletedScalarOrbit A 7⊓L (h.length+4) := ⟨ts,th⟩
    rw [sep.eq_bot,Submodule.mem_bot] at y
    exact y
  have hT := order15_deleted_small_scalar_zero ho H td vanish
  exact ⟨a,sub_eq_zero.mp hT⟩

end Order15MinimalHead.DeletedPencil
end
end RKCert.Paired
