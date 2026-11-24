module

public import RKCert.Dirk15NonC2GhostExact
public import RKCert.DirkWeightedFiveOriginal

@[expose] public section

/-! # The actual non-C(2) ordinary head

The four-dimensional maximal core is excluded by the paid projected
weighted fifth debut, even when it is not a coordinate algebra. -/
namespace RKCert.Paired
open Module RKCert.OneEscape
open scoped Classical
noncomputable section
variable {K : Type*} [Field K] [CharZero K]
variable {A : Fin 20→Fin 20→K} {b : Vec K 20}

structure Order15NonC2Head (A : Fin 20→Fin 20→K) (b : Vec K 20) where
  head : Vec K 20
  core_eq : zeroSpace A 4=nonC2Ghosts A b
  core : MaximalClockCore A 7 (nonC2Ghosts A b)
  disjoint : ∀ i, b i=0 → reverseCubic A b i=0 → head i=0
  band : ∀ k≤2,zeroSpace A (5+k)=chain (diag (nodes A)) (nonC2Ghosts A b) head (2+k)

theorem order15_nonC2_no_hyperplane (ha : LowerArray A) (ho : HasTreeOrderAtLeast A b 15)
    (hq : q₂ (mat A) (nodes A) 1≠0) {U : Submodule K (Vec K 20)}
    (inc : U≤zeroSpace A 5) (inv : U.map (diag (nodes A))≤U) :
    finrank K U≠4 := by
  intro e
  obtain ⟨w,band⟩ := order15_nonC2_hyperplane_band ha ho hq inc inv e
  exact no_invariant_grade5_head ha ho (by decide) inv inc band

theorem order15_nonC2_head (ha : LowerArray A) (ho : HasTreeOrderAtLeast A b 15)
    (hq : q₂ (mat A) (nodes A) 1≠0) : Nonempty (Order15NonC2Head A b) := by
  classical
  let C := diag (nodes A)
  let F := zeroSpace A
  let G := nonC2Ghosts A b
  have fG : F 4=G := order15_nonC2_ghosts_exact ha ho hq
  obtain ⟨U,maxU⟩ := order15_nonC2_has_core (A:=A)
  have GH : G≤U := maxU.2.2 _ (order15_nonC2_ghosts_le ha ho hq) nonC2Ghosts_invariant
  obtain ⟨f4,f5⟩ := order15_nonC2_early_ranks ha ho hq
  have H := order15_nonC2_rank_chart ha ho hq
  obtain ⟨_,uCap,whenEq⟩ := order15_ordinary_core_rank ha ho (e:=1) H.f3 H.f6 H.f7 U maxU
  have not4 : finrank K U≠4 := fun he =>
    order15_nonC2_no_hyperplane ha ho hq (whenEq he).1 maxU.2.1 he
  have dimG : finrank K G=3 := by rw [←fG]; exact f4
  have gU : G=U := Submodule.eq_of_le_of_finrank_le GH (by omega)
  have coreG : MaximalClockCore A 7 G := by rw [gU]; exact maxU
  have step (k : ℕ) (hk : k<2) :=
    order15_nonC2_unit_escape ha ho hq (j:=5+k) (by omega) (by omega)
  obtain ⟨r,V,w,pos,inv,le5,largest,head5,_,_,hr⟩ :=
    Clock.ordinary_single_head A 5 (step 0 (by decide)).1.le (step 0 (by decide)).2
  have hG5 : G≤zeroSpace A 5 := by rw [←fG]; exact zeroSpace_mono A (by decide : 4≤5)
  have hVG : V=G := le_antisymm
    (coreG.2.2 _ (le5.trans (zeroSpace_mono A (by decide))) inv)
    (largest G coreG.2.1 hG5)
  rw [hVG,dimG,f5] at hr
  have er : r=2 := by omega
  rw [hVG,er] at head5
  let v : Vec K 20 := fun i => if b i=0 ∧ reverseCubic A b i=0 then 0 else w i
  have diff : w-v∈G := by
    apply mem_nonC2Ghosts.mpr
    intro i hi
    have hn : ¬(b i=0 ∧ reverseCubic A b i=0) := fun e => hi.elim (· e.1) (· e.2)
    simp [v,Pi.sub_apply,hn]
  have same : chain C G v 2=chain C G w 2 := by
    have h := chain_sub_head (w:=w) coreG.2.1 diff 2
    simpa only [sub_sub_cancel] using h
  have start : F 5=chain C G v 2 := head5.trans same.symm
  exact ⟨⟨v,fG,coreG,fun i hx hy => by simp [v,hx,hy],
    Clock.ordinary_staircase coreG.2.1 (by decide) start
      (fun k hk => (step k hk).1.le) (fun k hk => (step k hk).2)⟩⟩

end
end RKCert.Paired
