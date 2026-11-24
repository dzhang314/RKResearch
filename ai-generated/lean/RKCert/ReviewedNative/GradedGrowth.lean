module
public import RKCert.ReviewedNative.GradedSeparation
public import RKCert.ReviewedNative.CausalStage

@[expose] public section

/-! # Native forward defect growth from reviewed elementary columns -/
namespace RKResearch.Certified.Graded
open RKResearch FiniteRootedTree Module
open scoped Matrix FiniteRootedTree

variable {K:Type*} [Field K] {s p:ℕ} {A:Matrix (Fin s) (Fin s) K} {b:Fin s→K}

theorem forward_seed_mem (A:Matrix (Fin s) (Fin s) K) :
    (2:K) • mat A (diag (nodes A) 1)-diag (nodes A) (diag (nodes A) 1)
      ∈zeroSpace A 2 := by
  have h:=monomialStageDefect_mem A 1
  have eq : diag (nodes A) (1:Fin s→K)=nodes A := by ext i;simp
  rw [eq]
  convert h using 1
  ext i
  simp [monomialStageDefect,pow_two]

/-- Each grade buys one new forward residual direction, with no
characteristic-zero restriction on an actually attained order. -/
theorem zeroSpace_finrank (strict:∀i j,i≤j→A i j=0) (ho:HasOrder A b p)
    {n:ℕ} (pay:n+2≤p) : n≤finrank K (zeroSpace A (n+1)) := by
  let c:=nodes A
  let seed:=(2:K) • mat A (diag c 1)-diag c (diag c 1)
  let W:=orbit (mat A) (diag c) seed
  have sub (k:ℕ) (hk:k+2≤p) : W k≤zeroSpace A (k+1) := by
    induction k with
    | zero => exact bot_le
    | succ k ih =>
      have h:=ih (by omega)
      change W k⊔(W k).map _⊔(W k).map _⊔Submodule.span K {seed}≤_
      refine sup_le (sup_le (sup_le (h.trans (zeroSpace_mono A (by omega))) ?_) ?_) ?_
      · exact Submodule.map_le_iff_le_comap.mpr (h.trans (mat_zeroSpace ho _ (by omega)))
      · exact Submodule.map_le_iff_le_comap.mpr (h.trans (diag_zeroSpace A _))
      · apply Submodule.span_le.mpr
        rintro x (rfl:x=seed)
        exact zeroSpace_mono A (by omega : 2≤k+1+1) (forward_seed_mem A)
  have zw : ∀x∈W n,probe A b 0 x=0 :=
    fun _ hx=>probe_zeroSpace ho (by omega : 0+(n+1)+1≤p) (sub n pay hx)
  have out : diag c 1∉W n := by
    intro h
    have m := probe_normTree ho (clockTree 1) 0 (by rw [order_clockTree];omega)
    have z : normTree A (clockTree 1)=diag c 1 := by
      rw [normTree_clockTree]
      ext i
      simp [c]
    rw [z,zw _ h,mul_zero] at m
    exact zero_ne_one m
  exact (orbit_rank (Equiv.refl _) (mat A) (causal_mat strict) c 1 n out).trans
    (Submodule.finrank_mono (sub n pay))

theorem nodes_not_defect_of_separation {q:ℕ} (hq:1≤q)
    (sep:∀a,coeffEval A q a∈zeroSpace A q→a=0) :
    nodes A∉zeroSpace A q := by
  intro hc
  let j:Fin (q+1) := ⟨1,by omega⟩
  have ev : coeffEval A q (Pi.single j 1)=nodes A := by
    rw [coeffEval_single,normTree_clockTree]
    ext i
    simp [j]
  have h:=congrFun (sep (Pi.single j 1) (ev.symm ▸ hc)) j
  simp at h

theorem zeroSpace_strict_of_separation [CharZero K] (strict:∀i j,i≤j→A i j=0)
    {q j:ℕ} (sep:∀a,coeffEval A q a∈zeroSpace A q→a=0) (jpos:1≤j) (jq:j+1≤q) :
    zeroSpace A j<zeroSpace A (j+1) := by
  refine lt_of_le_of_ne (zeroSpace_mono A (Nat.le_succ _)) ?_
  intro he
  apply nodes_not_defect_of_separation (by omega) sep
  apply zeroSpace_mono A jq
  rw [←he,←show diag (nodes A) (1:Fin s→K)=nodes A by ext i;simp]
  apply mem_of_invariant_seed (Equiv.refl _) (mat A) (causal_mat strict) (nodes A) 1 (zeroSpace A j)
  · intro v hv
    rw [he]
    exact mat_zeroSpace_charZero A j hv
  · intro v hv
    rw [he]
    exact diag_zeroSpace A j hv
  · rw [he]
    exact zeroSpace_mono A (by omega : 2≤j+1) (forward_seed_mem A)

end RKResearch.Certified.Graded
