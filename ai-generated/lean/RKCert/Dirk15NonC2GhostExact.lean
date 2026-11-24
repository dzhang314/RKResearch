module

public import RKCert.Dirk15NonC2Early
public import RKCert.FiveDebutObstruction

@[expose] public section

/-! # Exact simultaneous ghost support at the non-C(2) boundary

The ordinary fifth-debut obstruction applies directly if the entire
four-dimensional core is a coordinate subspace. This argument deliberately
does not assume that a larger clock-invariant core is an algebra. -/
namespace RKCert.Paired
open Module RKCert.OneEscape
open scoped Classical
noncomputable section
variable {K : Type*} [Field K] [CharZero K]
variable {A : Fin 20→Fin 20→K} {b : Vec K 20}

omit [CharZero K] in
theorem order15_nonC2_has_core :
    ∃ U : Submodule K (Vec K 20), MaximalClockCore A 7 U := by
  let C := diag (nodes A)
  let F := zeroSpace A 7
  obtain ⟨n,_,hn⟩ := exists_plateau C F
  refine ⟨core C F n,?_,invariant_of_plateau hn,fun _ q t => invariant_le_core q t n⟩
  intro v hv
  simpa only [pow_zero,Module.End.one_eq_id,LinearMap.id_apply] using (mem_core.mp hv) 0 (Nat.zero_le n)

omit [CharZero K] in
theorem nonC2Ghosts_mulClosed : Clock.MulClosed (nonC2Ghosts A b) := by
  intro u hu v _
  apply mem_nonC2Ghosts.mpr
  intro i hi
  rw [Pi.mul_apply,mem_nonC2Ghosts.mp hu i hi,zero_mul]

theorem order15_nonC2_unit_escape (ha : LowerArray A) (ho : HasTreeOrderAtLeast A b 15)
    (hq : q₂ (mat A) (nodes A) 1≠0) {j : ℕ} (hl : 5≤j) (hh : j≤6) :
    finrank K (zeroSpace A (j+1))=finrank K (zeroSpace A j)+1 ∧
      ¬(zeroSpace A j).map (diag (nodes A))≤zeroSpace A j := by
  have H := order15_nonC2_rank_chart ha ho hq
  have f5 := (order15_nonC2_early_ranks ha ho hq).2
  have unit : finrank K (zeroSpace A (j+1))=finrank K (zeroSpace A j)+1 := by
    rcases (show j=5 ∨ j=6 by omega) with rfl|rfl
    · rw [f5,H.f6]
    · rw [H.f6,H.f7]
  refine ⟨unit,fun inv => ?_⟩
  have out := dirk_forward_invariant_outgoing ha ho (j:=j) (by omega)
    (zeroSpace A j) le_rfl (fun v hv => inv (Submodule.mem_map_of_mem hv))
  omega

/-- An invariant hyperplane forces the full one-head band, with no
coordinatewise-algebra assumption. -/
theorem order15_nonC2_hyperplane_band (ha : LowerArray A) (ho : HasTreeOrderAtLeast A b 15)
    (hq : q₂ (mat A) (nodes A) 1≠0) {U : Submodule K (Vec K 20)}
    (inc : U≤zeroSpace A 5) (inv : U.map (diag (nodes A))≤U) (dim : finrank K U=4) :
    ∃ w : Vec K 20, ∀ k≤2,zeroSpace A (5+k)=chain (diag (nodes A)) U w (1+k) := by
  have f5 := (order15_nonC2_early_ranks ha ho hq).2
  have step (k : ℕ) (hk : k<2) :=
    order15_nonC2_unit_escape ha ho hq (j:=5+k) (by omega) (by omega)
  obtain ⟨r,V,w,pos,_,_,largest,head5,_,_,hr⟩ :=
    Clock.ordinary_single_head A 5 (step 0 (by decide)).1.le (step 0 (by decide)).2
  have uV : U≤V := largest U inv inc
  have hd := Submodule.finrank_mono uV
  have vU : U=V := Submodule.eq_of_le_of_finrank_le uV (by rw [f5] at hr; omega)
  subst V
  have h1 : r=1 := by rw [f5,dim] at hr; omega
  subst r
  exact ⟨w,Clock.ordinary_staircase inv (by decide) head5
    (fun k hk => (step k hk).1.le) (fun k hk => (step k hk).2)⟩

/-- The simultaneous two-channel zero space is precisely the genuine F4,
even before excluding a larger invariant hyperplane. -/
theorem order15_nonC2_ghosts_exact (ha : LowerArray A) (ho : HasTreeOrderAtLeast A b 15)
    (hq : q₂ (mat A) (nodes A) 1≠0) :
    zeroSpace A 4=nonC2Ghosts A b := by
  let G := nonC2Ghosts A b
  have fg : zeroSpace A 4≤G := order15_nonC2_quartic_channels ha ho hq
  have H := order15_nonC2_rank_chart ha ho hq
  obtain ⟨U,coreU⟩ := order15_nonC2_has_core (A:=A)
  have gU : G≤U := coreU.2.2 G (order15_nonC2_ghosts_le ha ho hq) nonC2Ghosts_invariant
  obtain ⟨_,ub,eq4⟩ := order15_ordinary_core_rank ha ho (e:=1) H.f3 H.f6 H.f7 U coreU
  have gcap : finrank K G≤4 := (Submodule.finrank_mono gU).trans ub
  have gn : finrank K G≠4 := by
    intro g4
    have u4 : finrank K U=4 := by
      have d := Submodule.finrank_mono gU
      omega
    have gu : G=U := Submodule.eq_of_le_of_finrank_eq gU (g4.trans u4.symm)
    have inc : G≤zeroSpace A 5 := gU.trans (eq4 u4).1
    obtain ⟨w,band⟩ := order15_nonC2_hyperplane_band ha ho hq inc nonC2Ghosts_invariant g4
    exact RKCert.FiveDebut.no_grade5_head ha ho (by decide) nonC2Ghosts_invariant
      nonC2Ghosts_mulClosed inc band
  apply Submodule.eq_of_le_of_finrank_le fg
  rw [(order15_nonC2_early_ranks ha ho hq).1]
  omega

end
end RKCert.Paired
