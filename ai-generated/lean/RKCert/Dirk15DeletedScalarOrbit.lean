module

public import RKCert.Dirk15NativeReverse
public import RKCert.Dirk15NonC2Orbit

@[expose] public section

/-! # Clock orbits on the nineteen physically retained coordinates

These are images of true polynomial and pure spaces. Only the diagonal
clock descends here; no assertion about the original operator after
deletion is needed or made.
-/
namespace RKCert.Paired
open Module Polynomial RKCert.OneEscape RKCert.Endpoint
open scoped Classical
noncomputable section
variable {K : Type*} [Field K]
variable {A : Fin 20 → Fin 20 → K} {b : Vec K 20}

def deletedClock (A : Fin 20 → Fin 20 → K) : Vec K 19 →ₗ[K] Vec K 19 :=
  diag (deleteTerminal K 19 (nodes A))

def deletedScalarOrbit (A : Fin 20 → Fin 20 → K) (j : ℕ) : Submodule K (Vec K 19) :=
  chain (deletedClock A) ⊥ 1 (j+1)

def deletedHeadOrbit (A : Fin 20 → Fin 20 → K) (U : Submodule K (Vec K 20))
    (w : Vec K 20) (j : ℕ) : Submodule K (Vec K 19) :=
  chain (deletedClock A) (U.map (deleteTerminal K 19)) (deleteTerminal K 19 w) j

theorem deleteTerminal_diag_pow (v : Vec K 20) (j : ℕ) :
    deleteTerminal K 19 ((diag (nodes A)^j) v) =
      (deletedClock A^j) (deleteTerminal K 19 v) := by
  ext i
  rw [deleteTerminal_apply,Clock.pow_diag_apply]
  change _ = (diag (deleteTerminal K 19 (nodes A))^j) (deleteTerminal K 19 v) i
  rw [Clock.pow_diag_apply,deleteTerminal_apply,deleteTerminal_apply]

theorem deletedHeadOrbit_eq (U : Submodule K (Vec K 20)) (w : Vec K 20) (j : ℕ) :
    deletedHeadOrbit A U w j = (chain (diag (nodes A)) U w j).map (deleteTerminal K 19) := by
  induction j with
  | zero => rfl
  | succ j ih =>
    change deletedHeadOrbit A U w j ⊔ K ∙ ((deletedClock A^j) (deleteTerminal K 19 w)) =
      (chain (diag (nodes A)) U w j ⊔ K ∙ ((diag (nodes A)^j) w)).map (deleteTerminal K 19)
    rw [ih,Submodule.map_sup,Submodule.map_span,Set.image_singleton,deleteTerminal_diag_pow]

theorem deletedCore_invariant {U : Submodule K (Vec K 20)}
    (inv : U.map (diag (nodes A)) ≤ U) :
    (U.map (deleteTerminal K 19)).map (deletedClock A) ≤ U.map (deleteTerminal K 19) := by
  rintro _ ⟨_,⟨v,hv,rfl⟩,rfl⟩
  have t := inv (Submodule.mem_map_of_mem hv)
  change diag (deleteTerminal K 19 (nodes A)) (deleteTerminal K 19 v)∈U.map (deleteTerminal K 19)
  rw [←deleteTerminal_diag]
  exact Submodule.mem_map_of_mem t

theorem deletedHeadOrbit_step {U : Submodule K (Vec K 20)} {w : Vec K 20}
    (hU : U.map (diag (nodes A))≤U) {n : ℕ} (n0 : 0<n) :
    deletedHeadOrbit A U w n⊔(deletedHeadOrbit A U w n).map (deletedClock A) =
      deletedHeadOrbit A U w (n+1) :=
  chain_sup_map (deletedCore_invariant hU) n0

theorem deletedScalarOrbit_step (j : ℕ) :
    deletedScalarOrbit A j⊔(deletedScalarOrbit A j).map (deletedClock A) =
      deletedScalarOrbit A (j+1) :=
  chain_sup_map (by simp) (Nat.succ_pos j)

theorem deleted_polynomial_eval_pow (j : ℕ) :
    deleteTerminal K 19 (evalNodes A (X^j : K[X])) = (deletedClock A^j) 1 := by
  ext i
  change deleteTerminal K 19 (evalNodes A (X^j : K[X])) i =
    (diag (deleteTerminal K 19 (nodes A))^j) 1 i
  rw [Clock.pow_diag_apply,deleteTerminal_apply,deleteTerminal_apply]
  simp only [evalNodes_apply,eval_pow,eval_X,Pi.one_apply,mul_one]

theorem deletedScalarOrbit_eq (j : ℕ) :
    deletedScalarOrbit A j = (LinearMap.range (polyEval A j)).map (deleteTerminal K 19) := by
  apply le_antisymm
  · apply (chain_le_iff _).mpr
    refine ⟨bot_le,fun k hk => ?_⟩
    rw [←deleted_polynomial_eval_pow (A:=A) k]
    apply Submodule.mem_map_of_mem
    rw [evalNodes_eq_polyEval A _ (by rw [natDegree_X_pow]; omega : (X^k:K[X]).natDegree≤j)]
    exact LinearMap.mem_range_self _ _
  · rintro _ ⟨_,⟨a,rfl⟩,rfl⟩
    rw [polyEval_apply,map_sum]
    apply (deletedScalarOrbit A j).sum_mem
    intro k _
    rw [map_smul]
    apply (deletedScalarOrbit A j).smul_mem
    have e : normTree A (Tree.bush k.val)=evalNodes A (X^k.val : K[X]) := by
      ext i
      simp [normTree_bush]
    rw [e,deleted_polynomial_eval_pow]
    have hp := (chain_le_iff (T:=deletedClock A) (U:=⊥) (w:=1) (j+1)).mp le_rfl
    exact hp.2 _ k.isLt

theorem deletedScalarOrbit_le (j : ℕ) : deletedScalarOrbit A j≤deletedTreeSpace A j := by
  rw [deletedScalarOrbit_eq]
  apply Submodule.map_mono
  rintro _ ⟨a,rfl⟩
  exact polyEval_mem_treeSpace _ _ _

theorem deletedScalarOrbit_decompose {j : ℕ} {v : Vec K 19} (h : v∈deletedScalarOrbit A j) :
    ∃ Q : K[X],Q.natDegree≤j ∧ v=deleteTerminal K 19 (evalNodes A Q) := by
  rw [deletedScalarOrbit_eq] at h
  obtain ⟨_,⟨a,rfl⟩,rfl⟩ := h
  refine ⟨ofFn (j+1) a,?_ ,?_⟩
  · have e := ofFn_natDegree_lt (Nat.succ_pos j) a
    change (ofFn (j+1) a).natDegree<j+1 at e
    omega
  · rw [evalNodes_ofFn]

theorem order15_deleted_clock_escape [CharZero K] (ha : LowerArray A)
    (ho : HasTreeOrderAtLeast A b 15) (H : Order15MinimalMarkedChart A b)
    (j : ℕ) (lo : 7≤j) (hi : j≤10) :
    ¬(deletedTreeSpace A j).map (deletedClock A)≤deletedTreeSpace A j := by
  rw [(order15_minimal_deleted_band ha ho H j lo (by omega)).1]
  exact deleteTerminal_dual_noninvariant (nodes A) (W:=markedTerminalZero A 15 (14-j))
    inf_le_right (order15_minimal_marked_escape ha ho H _ (by omega) (by omega))

theorem order15_deleted_clock_step [CharZero K] (ha : LowerArray A)
    (ho : HasTreeOrderAtLeast A b 15) (H : Order15MinimalMarkedChart A b)
    (j : ℕ) (lo : 7≤j) (hi : j≤10) :
    deletedTreeSpace A (j+1)=deletedTreeSpace A j⊔(deletedTreeSpace A j).map (deletedClock A) := by
  symm
  refine Submodule.eq_of_le_of_finrank_le
    (sup_le (deleted_tree_mono (Nat.le_succ j)) (deleted_tree_clock j)) ?_
  have out := order15_deleted_clock_escape ha ho H j lo hi
  have o : deletedTreeSpace A j < deletedTreeSpace A j⊔(deletedTreeSpace A j).map (deletedClock A) :=
    lt_of_le_of_ne le_sup_left (fun e => out (le_sup_right.trans e.ge))
  have q := Submodule.finrank_lt_finrank_of_lt o
  rw [(order15_minimal_deleted_band ha ho H (j+1) (by omega) (by omega)).2,
      (order15_minimal_deleted_band ha ho H j lo (by omega)).2] at *
  omega

end
end RKCert.Paired
