module

public import RKCert.Dirk15NonC2Head
public import RKCert.DirkTerminalPolynomialSeparation

@[expose] public section

/-! # Exact native forward flag in the non-C(2) order-fifteen boundary

A real terminal zero separates the scalar band one grade further. The
two paid reverse flag ranks then force the remaining clock additions.
There is no shortened method and no distinct-node assumption.
-/
namespace RKCert.Paired
open Module RKCert.OneEscape RKCert.Endpoint Polynomial
open scoped Classical
noncomputable section

section RankAdapters
variable {K : Type*} [Field K] {s : ℕ}
variable {c w : Vec K s} {U : Submodule K (Vec K s)}

theorem chain_dim_upper (n : ℕ) : finrank K (chain (diag c) U w n)≤finrank K U+n := by
  classical
  induction n with
  | zero => exact le_rfl
  | succ n ih =>
    let C := chain (diag c) U w n
    let v := (diag c^n) w
    let V := Submodule.span K ({v}:Set (Vec K s))
    have d : finrank K V≤1 := by
      by_cases e : v=0
      · change finrank K (K ∙ v)≤1
        rw [e,Submodule.span_zero_singleton,finrank_bot]
        exact Nat.zero_le _
      · exact (finrank_span_singleton e).le
    have h := Submodule.finrank_sup_add_finrank_inf_eq C V
    change finrank K (C⊔V : Submodule K (Vec K s))≤_
    change finrank K C≤_ at ih
    omega

theorem chain_dim_sites (n : ℕ) :
    finrank K (chain (diag c) U w n)≤finrank K U+(Clock.headSites c w).card := by
  classical
  let S := Clock.headSites c w
  let W : Finset (Vec K s) := S.image (fun z => Clock.fiber c z w)
  let L := Submodule.span K (W:Set (Vec K s))
  have memL (a : K) (ha : a∈S) : Clock.fiber c a w∈L :=
    Submodule.subset_span (Finset.mem_image_of_mem _ ha)
  have split (r : ℕ) : (diag c^r) w=∑ a∈S,a^r • Clock.fiber c a w := by
    ext i
    rw [Clock.pow_diag_apply,Finset.sum_apply]
    by_cases hi : w i≠0
    · rw [Finset.sum_eq_single_of_mem (c i) (Clock.headSites_mem i hi)]
      · simp [Clock.fiber]
      · intro a _ na
        simp [Clock.fiber,Ne.symm na]
    · push Not at hi
      simp [Clock.fiber,hi]
  have include' : chain (diag c) U w n≤U⊔L := by
    apply (chain_le_iff _).mpr
    refine ⟨le_sup_left,fun r _ => ?_⟩
    rw [split]
    exact (le_sup_right : L≤U⊔L) (L.sum_mem (fun a ha => L.smul_mem _ (memL a ha)))
  have nd := Submodule.finrank_mono include'
  have sup := Submodule.finrank_sup_add_finrank_inf_eq U L
  have lr : finrank K L≤S.card := (finrank_span_finset_le_card W).trans Finset.card_image_le
  change finrank K (chain (diag c) U w n)≤finrank K U+S.card
  omega

theorem full_clock_step_of_unit {A : Fin s→Fin s→K} {j : ℕ}
    (one : finrank K (treeSpace A (j+1))≤finrank K (treeSpace A j)+1)
    (out : ¬(treeSpace A j).map (diag (nodes A))≤treeSpace A j) :
    treeSpace A (j+1)=treeSpace A j ⊔ (treeSpace A j).map (diag (nodes A)) := by
  apply Eq.symm
  refine Submodule.eq_of_le_of_finrank_le
    (sup_le (treeSpace_mono A (by omega)) (Submodule.map_le_iff_le_comap.mpr (diag_treeSpace A j))) ?_
  have hlt : treeSpace A j<treeSpace A j ⊔ (treeSpace A j).map (diag (nodes A)) :=
    lt_of_le_of_ne le_sup_left (fun e => out (le_sup_right.trans e.ge))
  have hd := Submodule.finrank_lt_finrank_of_lt hlt
  omega

end RankAdapters

variable {K : Type*} [Field K] [CharZero K]
variable {A : Fin 20→Fin 20→K} {b : Vec K 20}

theorem order15_nonC2_full_clock_escape (ha : LowerArray A) (ho : HasTreeOrderAtLeast A b 15)
    (hq : q₂ (mat A) (nodes A) 1≠0) (j : ℕ) (hl : 7≤j) (hu : j≤11) :
    ¬(treeSpace A j).map (diag (nodes A))≤treeSpace A j := by
  intro inv
  let n := 14-j
  have nn : 3≤n := by dsimp [n]; omega
  have nh : n≤7 := by dsimp [n]; omega
  have e : marked A 15 n=annih (treeSpace A j) := by
    change annih (treeSpace A (15-1-n))=_
    rw [show 15-1-n=j by dsimp [n]; omega]
  have invM : (marked A 15 n).map (diag (mirror A))≤marked A 15 n := by
    rw [e]
    rintro _ ⟨w,hw,rfl⟩
    apply mem_annih.mpr
    intro x hx
    rw [row_flip_diag]
    apply mem_annih.mp hw
    have eq : diag (mirror A) x=x-diag (nodes A) x := by
      ext i
      simp [mirror,sub_mul]
    rw [eq]
    exact (treeSpace A j).sub_mem hx (inv (Submodule.mem_map_of_mem hx))
  have H := order15_nonC2_rank_chart ha ho hq
  rw [H.marked_terminal_zero ha ho n (by omega) nh] at invM
  by_cases en : n=3
  · rw [en] at invM
    exact order15_cubic_budget_nonlocal ha ho (H.cubic_budget ha ho) invM
  · exact order15_cubic_budget_escape ha ho (H.cubic_budget ha ho) n (by omega) nh invM

def ordinaryScalarBand (A : Fin 20→Fin 20→K) : Submodule K (Vec K 20) :=
  LinearMap.range (polyEval A 7)

omit [CharZero K] in
theorem ordinaryScalarBand_rank (ho : HasTreeOrderAtLeast A b 15) :
    finrank K (ordinaryScalarBand A)=8 := by
  have inj : Function.Injective (polyEval A 7) := by
    intro a z e
    apply sub_eq_zero.mp
    apply poly_separated ho (by decide : 2*7+1≤15)
    rw [map_sub,e,sub_self]
    exact (zeroSpace A 7).zero_mem
  rw [ordinaryScalarBand,LinearMap.finrank_range_of_inj inj,Module.finrank_fin_fun]

set_option maxHeartbeats 1150000 in
theorem order15_nonC2_full_flag (ha : LowerArray A) (ho : HasTreeOrderAtLeast A b 15)
    (hq : q₂ (mat A) (nodes A) 1≠0) (h : Order15NonC2Head A b) :
    ∀ j : ℕ, 7≤j → j≤12 →
      treeSpace A j=ordinaryScalarBand A ⊔
        chain (diag (nodes A)) (nonC2Ghosts A b) h.head (j-3) := by
  classical
  let E := treeSpace A
  let F := zeroSpace A
  let S := ordinaryScalarBand A
  let U := nonC2Ghosts A b
  let C := diag (nodes A)
  let w := h.head
  let Z := F 7 ⊔ (F 7).map C
  let L := chain C U w
  have base : F 7=L 4 := h.band 2 (by decide)
  have z5 : Z=L 5 := by
    change F 7 ⊔ (F 7).map C=L 5
    rw [base,chain_sup_map h.core.2.1 (by decide : 0<4)]
  have hS : S≤E 7 := by
    rintro _ ⟨a,rfl⟩
    exact polyEval_mem_treeSpace _ _ _
  have Zpure : Z≤F 8 := sup_le (zeroSpace_mono A (by decide))
    (Submodule.map_le_iff_le_comap.mpr (diag_zeroSpace A 7))
  have H := order15_nonC2_rank_chart ha ho hq
  have dU : finrank K U=3 := by
    rw [show U=F 4 from h.core_eq.symm]
    exact (order15_nonC2_early_ranks ha ho hq).1
  have zdim : finrank K Z=8 := by
    have out : ¬(F 7).map C≤F 7 := by
      intro inv
      have m := Submodule.finrank_mono (h.core.2.2 _ le_rfl inv)
      change finrank K (F 7)≤finrank K U at m
      rw [H.f7,dU] at m
      omega
    have lt : F 7<Z := lt_of_le_of_ne le_sup_left (fun e => out (le_sup_right.trans e.ge))
    have lower := Submodule.finrank_lt_finrank_of_lt lt
    have upper : finrank K Z≤8 := by
      rw [z5]
      exact (chain_dim_upper (c:=nodes A) (U:=U) (w:=w) 5).trans (by rw [dU])
    change finrank K (F 7)<finrank K Z at lower
    rw [H.f7] at lower
    omega
  have zlast : Z≤LinearMap.ker (LinearMap.proj (Fin.last 19)) := by
    apply sup_le
    · intro v hv
      exact H.terminal_pure_zero _ hv
    · rintro _ ⟨v,hv,rfl⟩
      change nodes A (Fin.last 19)*v (Fin.last 19)=0
      rw [H.terminal_pure_zero _ hv,mul_zero]
  have dis : Disjoint S Z := by
    rw [disjoint_iff_inf_le]
    intro x hx
    have hSx : x∈S := hx.1
    obtain ⟨a,e⟩ := hSx
    let P : K[X] := ofFn (7+1) a
    have dP : P.natDegree≤7 := by
      have z := ofFn_natDegree_lt (by decide : 0<7+1) a
      change P.natDegree<7+1 at z
      omega
    have eval : evalNodes A P=x := (evalNodes_ofFn A 7 a).trans e
    have term : P.eval 1=0 := by
      have h := zlast hx.2
      change x (Fin.last 19)=0 at h
      rw [←eval,evalNodes_apply,H.terminal.node_one] at h
      exact h
    have p0 := terminal_polynomial_defect_zero ho (by decide : 1≤7) (by decide : 7≤8)
      (by decide : 8+7≤15) dP term (by rw [eval]; exact Zpure hx.2)
    rw [Submodule.mem_bot,←eval,p0]
    ext i
    simp
  have eight : E 8=S⊔L 5 := by
    rw [←z5]
    apply Eq.symm
    refine Submodule.eq_of_le_of_finrank_le (sup_le (hS.trans (treeSpace_mono A (by decide)))
      (Zpure.trans (zeroSpace_le_treeSpace A 8))) ?_
    have dim := Submodule.finrank_sup_add_finrank_inf_eq S Z
    rw [dis.eq_bot,finrank_bot,add_zero,ordinaryScalarBand_rank ho,zdim] at dim
    rw [dim,H.treeBand 8 (by decide) (by decide)]
  have sc8 : S.map C≤E 8 := by
    rintro _ ⟨v,⟨a,rfl⟩,rfl⟩
    let P : K[X] := ofFn (7+1) a
    have dP : P.natDegree≤7 := by
      have k := ofFn_natDegree_lt (by decide : 0<7+1) a
      change P.natDegree<7+1 at k
      omega
    have eval : C (polyEval A 7 a)=evalNodes A (X*P) := by
      rw [←evalNodes_ofFn A 7 a]
      ext i
      simp [C,P,eval_mul]
    rw [eval]
    exact evalNodes_mem_treeSpace A _ (natDegree_mul_le.trans (by rw [natDegree_X]; omega))
  have grow (k : ℕ) (hk : k≤4) : E (8+k)=S⊔L (5+k) := by
    induction k with
    | zero => exact eight
    | succ k ih =>
      have old := ih (by omega)
      have one := full_clock_step_of_unit
        (j:=8+k) (by rw [H.treeBand (8+k+1) (by omega) (by omega),
          H.treeBand (8+k) (by omega) (by omega)])
        (order15_nonC2_full_clock_escape ha ho hq (8+k) (by omega) (by omega))
      have sml : S.map C≤S⊔L (5+k) := by
        rw [←old]
        exact sc8.trans (treeSpace_mono A (by omega))
      have supE : (S⊔L (5+k)) ⊔ (S.map C⊔(L (5+k)).map C)=
          (S⊔L (5+k)) ⊔ (L (5+k)).map C := by
        exact le_antisymm (sup_le le_sup_left (sup_le (sml.trans le_sup_left) le_sup_right))
          (sup_le le_sup_left (le_sup_right.trans le_sup_right))
      change E (8+k+1)=E (8+k)⊔(E (8+k)).map C at one
      have cc : L (5+k)⊔(L (5+k)).map C=L (5+k+1) :=
        chain_sup_map h.core.2.1 (by omega : 0<5+k)
      rw [show 8+(k+1)=8+k+1 by omega,one,old,Submodule.map_sup,supE,sup_assoc,cc,
        show 5+k+1=5+(k+1) by omega]
  intro j hl hu
  change E j=S⊔L (j-3)
  by_cases ej : j=7
  · subst j
    rw [show 7-3=4 by decide,←base]
    apply le_antisymm _ (sup_le hS (zeroSpace_le_treeSpace A 7))
    intro x hx
    obtain ⟨a,hxF⟩ := exists_poly_zeroSpace ho (by decide : 7+1≤15) hx
    apply Submodule.mem_sup.mpr
    exact ⟨_,⟨a,rfl⟩,_,hxF,by abel⟩
  · have gg := grow (j-8) (by omega)
    rwa [show 8+(j-8)=j by omega,show 5+(j-8)=j-3 by omega] at gg

theorem order15_nonC2_full_flag_dim_split (ha : LowerArray A) (ho : HasTreeOrderAtLeast A b 15)
    (hq : q₂ (mat A) (nodes A) 1≠0) (h : Order15NonC2Head A b)
    (j : ℕ) (hl : 7≤j) (hu : j≤12) :
    let S := ordinaryScalarBand A
    let W := chain (diag (nodes A)) (nonC2Ghosts A b) h.head (j-3)
    Disjoint S W ∧ finrank K W=j := by
  let S := ordinaryScalarBand A
  let U := nonC2Ghosts A b
  let W := chain (diag (nodes A)) U h.head (j-3)
  change Disjoint S W ∧ finrank K W=j
  have e : treeSpace A j=S⊔W := order15_nonC2_full_flag ha ho hq h j hl hu
  have d := Submodule.finrank_sup_add_finrank_inf_eq S W
  rw [←e,(order15_nonC2_rank_chart ha ho hq).treeBand j hl hu,ordinaryScalarBand_rank ho] at d
  have dimU : finrank K U=3 := by
    change finrank K (nonC2Ghosts A b)=3
    rw [←h.core_eq]
    exact (order15_nonC2_early_ranks ha ho hq).1
  have low : finrank K W≤j := (chain_dim_upper (U:=U) _).trans (by rw [dimU]; omega)
  have no : finrank K (S⊓W : Submodule K (Vec K 20))=0 := by omega
  exact ⟨disjoint_iff_inf_le.mpr ((Submodule.finrank_eq_zero.mp no).le),by omega⟩

theorem order15_nonC2_head_sites (ha : LowerArray A) (ho : HasTreeOrderAtLeast A b 15)
    (hq : q₂ (mat A) (nodes A) 1≠0) (h : Order15NonC2Head A b) :
    9≤(Clock.headSites (nodes A) h.head).card := by
  have dim := (order15_nonC2_full_flag_dim_split ha ho hq h 12 (by decide) (by decide)).2
  change finrank K (chain (diag (nodes A)) (nonC2Ghosts A b) h.head (12-3))=12 at dim
  have cap := chain_dim_sites (c:=nodes A) (U:=nonC2Ghosts A b) (w:=h.head) (12-3)
  rw [dim,←h.core_eq,(order15_nonC2_early_ranks ha ho hq).1] at cap
  omega

end
end RKCert.Paired
