module

public import RKCert.Dirk15CleanCount
public import RKCert.RadauGridComplete
public import Mathlib.FieldTheory.IsAlgClosed.AlgebraicClosure
public import RKCert.BaseChange

@[expose] public section

/-! # Actual non-C(2) fourth and fifth ranks via all eight Radau ports
No assertion identifying the maximal clock core with the coordinate
kernel is made here. The possible invariant hyperplane is a later gate. -/
namespace RKCert.Paired
open Polynomial Module RKCert.OneEscape
open RKCert.FixedPolynomial.Radau77569
open scoped Classical
noncomputable section
variable {K : Type*} [Field K] [CharZero K]
variable {A : Fin 20→Fin 20→K} {b : Vec K 20}

theorem order15_nonC2_quartic_channels_of_split [IsAlgClosed K] (ha : LowerArray A)
    (ho : HasTreeOrderAtLeast A b 15) (hq : q₂ (mat A) (nodes A) 1≠0)
    {v : Vec K 20} (hv : v∈zeroSpace A 4) :
    ∀ i,b i≠0 ∨ reverseCubic A b i≠0 → v i=0 := by
  classical
  obtain ⟨S,hS,ports⟩ := exists_eight_ports (K:=K)
  let T := cleanPortSites A b
  have hT : T.card≤5 := order15_nonC2_clean_port_count ha ho hq
  have inter : (S∩T).card≤T.card := Finset.card_le_card Finset.inter_subset_right
  have bound := Finset.card_sdiff_add_card_inter S T
  obtain ⟨a,d,e,aS,dS,eS,ad,ae,de⟩ :=
    Finset.two_lt_card_iff.mp (show 2<(S\T).card by omega)
  have outside (i : Fin 20) (hb : b i≠0) (ht : reverseCubic A b i=0)
      {z : K} (hz : z∈S\T) : mirror A i≠z := by
    have hmem : mirror A i∈T := Finset.mem_image_of_mem _ ((mem_cleanRows i).mpr ⟨hb,ht⟩)
    exact fun e => (Finset.mem_sdiff.mp hz).2 (e ▸ hmem)
  exact order15_nonC2_quartics_of_three_missing ha ho hq a d e ad ae de
    (ports _ (Finset.mem_sdiff.mp aS).1) (ports _ (Finset.mem_sdiff.mp dS).1)
    (ports _ (Finset.mem_sdiff.mp eS).1)
    (fun i hb ht => ⟨outside i hb ht aS,outside i hb ht dS,outside i hb ht eS⟩) hv

def nonC2Ghosts (A : Fin 20→Fin 20→K) (b : Vec K 20) : Submodule K (Vec K 20) :=
  ⨅ (i : Fin 20) (_ : b i≠0 ∨ reverseCubic A b i≠0), LinearMap.ker (LinearMap.proj i)

omit [CharZero K] in
theorem mem_nonC2Ghosts {v : Vec K 20} :
    v∈nonC2Ghosts A b ↔ ∀ i,b i≠0 ∨ reverseCubic A b i≠0 → v i=0 := by
  simp [nonC2Ghosts]

omit [CharZero K] in
theorem nonC2Ghosts_invariant : (nonC2Ghosts A b).map (diag (nodes A))≤nonC2Ghosts A b := by
  rintro _ ⟨v,hv,rfl⟩
  apply mem_nonC2Ghosts.mpr
  intro i hi
  change nodes A i*v i=0
  rw [mem_nonC2Ghosts.mp hv i hi,mul_zero]

theorem order15_nonC2_ghosts_le (ha : LowerArray A) (ho : HasTreeOrderAtLeast A b 15)
    (hq : q₂ (mat A) (nodes A) 1≠0) : nonC2Ghosts A b≤zeroSpace A 7 := by
  intro v hv
  have H := order15_nonC2_rank_chart ha ho hq
  have mem : v∈treeSpace A 7 := by
    rw [←annih_annih_paired (treeSpace A 7)]
    change v∈annih (marked A 15 7)
    apply mem_annih.mpr
    intro w hw
    rw [order15_nonC2_reverse_orbit ha ho H 7 (by decide) (by decide)] at hw
    obtain ⟨u,hu,Q,_,wQ⟩ := Clock.exists_head_poly hw
    have uz : u=0 := by simpa using hu
    rw [row_apply]
    apply Finset.sum_eq_zero
    intro i _
    by_cases ht : reverseCubic A b i=0
    · simp [wQ i,uz,ht]
    · simp [mem_nonC2Ghosts.mp hv i (Or.inr ht)]
  obtain ⟨a,hf⟩ := exists_poly_zeroSpace ho (by decide : 7+1≤15) mem
  have vp (k : ℕ) : probe A b k v=0 := by
    simp only [probe,row_apply]
    apply Finset.sum_eq_zero
    intro i _
    by_cases h : b i=0
    · simp [h]
    · simp [mem_nonC2Ghosts.mp hv i (Or.inl h)]
  have az : a=0 := by
    funext j
    apply moments_detect ho (d:=1) (by decide) (by decide) (fun i l => by omega) a _ j
    intro i
    have hi := probe_zeroSpace ho (by have := i.isLt; omega : i.val+7+1≤15) hf
    change probe A b i.val (v-polyEval A 7 a)=0 at hi
    rw [map_sub,vp,zero_sub,neg_eq_zero,probe_polyEval ho (by have := i.isLt; omega)] at hi
    exact hi
  simpa only [az,map_zero,sub_zero] using hf

/-- The physical quartic channel vanishings force the first two ranks.
This uses the native, still unresolved maximal-clock-core bound, not
a guess that its dimension is three. -/
theorem order15_nonC2_early_ranks_of_channels (ha : LowerArray A) (ho : HasTreeOrderAtLeast A b 15)
    (hq : q₂ (mat A) (nodes A) 1≠0) (h4 : zeroSpace A 4≤nonC2Ghosts A b) :
    finrank K (zeroSpace A 4)=3 ∧ finrank K (zeroSpace A 5)=5 := by
  let C := diag (nodes A)
  let F := zeroSpace A
  obtain ⟨n,_,hn⟩ := exists_plateau C (F 7)
  let U := core C (F 7) n
  have hU : MaximalClockCore A 7 U := by
    refine ⟨?_,invariant_of_plateau hn,fun _ q t => invariant_le_core q t n⟩
    intro v hv
    simpa only [pow_zero,one_apply_eq_self] using (mem_core.mp hv) 0 (Nat.zero_le n)
  have U4 : F 4≤U := h4.trans (hU.2.2 _ (order15_nonC2_ghosts_le ha ho hq) nonC2Ghosts_invariant)
  have H := order15_nonC2_rank_chart ha ho hq
  obtain ⟨_,cap,big⟩ := order15_ordinary_core_rank ha ho (e:=1) H.f3 H.f6 H.f7 U hU
  have f34 : finrank K (F 3)<finrank K (F 4) := Submodule.finrank_lt_finrank_of_lt
    (dirk_zeroSpace_lt_succ ha ho (j:=3) (by decide) (by decide))
  have f45 : finrank K (F 4)<finrank K (F 5) := Submodule.finrank_lt_finrank_of_lt
    (dirk_zeroSpace_lt_succ ha ho (j:=4) (by decide) (by decide))
  have f56 : finrank K (F 5)<finrank K (F 6) := Submodule.finrank_lt_finrank_of_lt
    (dirk_zeroSpace_lt_succ ha ho (j:=5) (by decide) (by decide))
  have f3 : finrank K (F 3)=2 := H.f3
  have f6 : finrank K (F 6)=6 := H.f6
  have fr := Submodule.finrank_mono U4
  have outgoing (eq : F 4=U) : finrank K (F 4)+2≤finrank K (F 5) := by
    apply dirk_forward_invariant_outgoing ha ho (j:=4) (by decide) (F 4) le_rfl
    intro v hv
    rw [eq] at hv ⊢
    exact hU.2.1 (Submodule.mem_map_of_mem hv)
  have f4 : finrank K (F 4)=3 := by
    by_contra ne
    have eq : F 4=U := Submodule.eq_of_le_of_finrank_le U4 (by omega)
    have o := outgoing eq
    omega
  refine ⟨f4,?_⟩
  change finrank K (F 5)=5
  by_cases high : finrank K U=4
  · exact (big high).2
  · have eq : F 4=U := Submodule.eq_of_le_of_finrank_le U4 (by omega)
    have o := outgoing eq
    omega

section Extend
variable {L : Type*} [Field L] (f : K→+*L)

omit [CharZero K] in
theorem map_zeroSpace_mem {s n : ℕ} {A : Fin s→Fin s→K} {v : Vec K s}
    (hv : v∈zeroSpace A n) :
    (fun i => f (v i))∈zeroSpace (fun i j => f (A i j)) n := by
  let F := zeroSpace (fun i j => f (A i j)) n
  refine Submodule.span_induction
    (p:=fun x _ => (fun i => f (x i))∈F) ?_ ?_ ?_ ?_ hv
  · rintro _ ⟨t,u,e,h,rfl⟩
    have eq : (fun i => f ((normTree A t-normTree A u) i))=
        normTree (fun i j => f (A i j)) t-normTree (fun i j => f (A i j)) u := by
      ext i
      simp only [normTree,Pi.sub_apply,Pi.smul_apply,smul_eq_mul,map_sub,map_mul,map_natCast,
        map_stageWeight]
    rw [eq]
    exact normDiff_mem _ t u e h
  · have he : (fun i : Fin s => f ((0:Vec K s) i))=0 := by ext i; simp
    rw [he]
    exact F.zero_mem
  · intro x y _ _ hx hy
    have he : (fun i => f ((x+y) i))=(fun i => f (x i))+(fun i => f (y i)) := by
      ext i
      simp
    exact he ▸ F.add_mem hx hy
  · intro r x _ hx
    have he : (fun i => f ((r • x) i))=f r • (fun i => f (x i)) := by
      ext i
      simp
    exact he ▸ F.smul_mem _ hx

omit [CharZero K] in
theorem map_forward_q₂ (i : Fin 20) :
    f (q₂ (mat A) (nodes A) 1 i)=
      q₂ (mat (fun j k => f (A j k))) (nodes (fun j k => f (A j k))) 1 i := by
  simp only [q₂,mat_apply,diag_apply,nodes,Pi.sub_apply,Pi.smul_apply,smul_eq_mul,Pi.one_apply,
    map_sub,map_sum,map_mul,map_ofNat,map_one]

omit [CharZero K] in
theorem map_reverseCubic (i : Fin 20) :
    f (reverseCubic A b i)=reverseCubic (fun j k => f (A j k)) (fun j => f (b j)) i := by
  simp only [reverseCubic,q₃,mat_apply,diag_apply,mirror,nodes,Pi.sub_apply,Pi.smul_apply,
    smul_eq_mul,Pi.one_apply,map_sub,map_sum,map_mul,map_ofNat,map_one]
end Extend

/-- This rank restriction and the simultaneous quartic disappearances hold
over any characteristic-zero field, even without the missing ports in it. -/
theorem order15_nonC2_quartic_channels (ha : LowerArray A)
    (ho : HasTreeOrderAtLeast A b 15) (hq : q₂ (mat A) (nodes A) 1≠0) :
    zeroSpace A 4≤nonC2Ghosts A b := by
  let f := algebraMap K (AlgebraicClosure K)
  let B : Fin 20→Fin 20→AlgebraicClosure K := fun j k => f (A j k)
  let w : Vec (AlgebraicClosure K) 20 := fun j => f (b j)
  have hq' : q₂ (mat B) (nodes B) 1≠0 := by
    intro e
    apply hq
    ext i
    apply f.injective
    rw [map_forward_q₂ f i,congrFun e i]
    exact f.map_zero.symm
  intro v hv
  apply mem_nonC2Ghosts.mpr
  intro i hi
  apply f.injective
  rw [map_zero]
  have him : w i≠0 ∨ reverseCubic B w i≠0 := by
    rcases hi with hb|ht
    · exact Or.inl (fun z => hb (f.injective (z.trans f.map_zero.symm)))
    · right
      rw [←map_reverseCubic f i]
      exact fun z => ht (f.injective (z.trans f.map_zero.symm))
  exact order15_nonC2_quartic_channels_of_split (lowerTriangular_map ha f) (ho.map f) hq'
    (map_zeroSpace_mem f hv) i him

theorem order15_nonC2_early_ranks (ha : LowerArray A) (ho : HasTreeOrderAtLeast A b 15)
    (hq : q₂ (mat A) (nodes A) 1≠0) :
    finrank K (zeroSpace A 4)=3 ∧ finrank K (zeroSpace A 5)=5 :=
  order15_nonC2_early_ranks_of_channels ha ho hq (order15_nonC2_quartic_channels ha ho hq)


end
end RKCert.Paired
