module

public import RKCert.DirkNoStall
public import RKCert.UniformDIRK

@[expose] public section

/-! # Stage counts from genuine ordinary DIRK ranks

This module isolates the numerical counts from the grade-six amplification.
No strict triangularity, nonzero individual weights, or positivity is used.
The grade-six surplus enters the last four statements as an explicit hypothesis,
not as an imported or presumed claim. -/

namespace RKCert.Paired
open Module

variable {K : Type*} [Field K] {s p m q n : ℕ}
variable {A : Fin s → Fin s → K} {b : Vec K s}

theorem zeroSpace_first_of_row {A : Fin (s+1) → Fin (s+1) → K}
    (h0 : ∀ j, A 0 j=0) (m : ℕ) :
    zeroSpace A m ≤ LinearMap.ker (LinearMap.proj 0) := by
  have hnorm (t : Tree) : normTree A t 0 = if t.order = 1 then 1 else 0 := by
    cases t with
    | leaf => simp [normTree_leaf, Tree.order]
    | attach t u =>
      have := t.order_pos
      have := u.order_pos
      have hn : (t.attach u).order ≠ 1 := by simp only [Tree.order]; omega
      simp [normTree, stageWeight, h0, hn]
  apply Submodule.span_le.mpr
  rintro _ ⟨t,u,hh,_,rfl⟩
  change normTree A t 0 - normTree A u 0 = 0
  rw [hnorm, hnorm, hh, sub_self]

theorem polyEval_first_of_row {A : Fin (s+1) → Fin (s+1) → K}
    (h0 : ∀ j, A 0 j=0) (q : ℕ) (a : Fin (q+1) → K) :
    polyEval A q a 0 = a 0 := by
  have hc0 : nodes A 0=0 := by simp [nodes, h0]
  rw [polyEval_apply, Fin.sum_univ_succ]
  simp [Finset.sum_apply, normTree_bush, hc0]

/-- A real zero row suffices; later diagonal entries may be arbitrary. -/
theorem poly_separated_of_first_row {A : Fin (s+1) → Fin (s+1) → K} {b : Vec K (s+1)}
    (h0 : ∀ j, A 0 j=0) (ho : HasTreeOrderAtLeast A b p) (hp : 2*m≤p)
    (a : Fin (m+1) → K) (h : polyEval A m a∈zeroSpace A m) : a=0 := by
  have hfirst : polyEval A m a 0=0 := zeroSpace_first_of_row h0 m h
  have hz := (polyEval_first_of_row h0 m a).symm.trans hfirst
  have he (i : Fin m) :
      (∑ j : Fin m, a j.succ / ((i.val+j.val+2:ℕ):K))=0 := by
    have hh : probe A b i.val (polyEval A m a)=0 := probe_zeroSpace ho (by omega) h
    rw [probe_polyEval ho (by omega), Fin.sum_univ_succ, hz, zero_div,zero_add] at hh
    simpa only [Fin.val_succ, Nat.add_assoc] using hh
  have hh := moments_detect ho (d:=2) (by decide) (by omega)
    (fun i j => by omega) (fun j : Fin m => a j.succ) he
  ext j; exact Fin.cases hz hh j

/-- Separation of scalar degrees `q` inside any later paid defect grade `m`. -/
theorem poly_separated_delayed (ho : HasTreeOrderAtLeast A b p) (hqm : q≤m)
    (hp : q+m+1≤p) (a : Fin (q+1) → K) (h : polyEval A q a∈zeroSpace A m) : a=0 := by
  have hz := moments_detect ho (d:=1) (by decide) (n:=q+1) (by omega)
    (fun i j => by omega) a ?_
  · exact funext hz
  · intro i
    have hh : probe A b i.val (polyEval A q a)=0 := probe_zeroSpace ho (by omega) h
    rwa [probe_polyEval ho (by omega)] at hh

theorem treeSpace_rank_of_delayed (hqm : q≤m)
    (hsep : ∀ a, polyEval A q a ∈ zeroSpace A m → a=0) :
    q+1 + finrank K (zeroSpace A m) ≤ finrank K (treeSpace A m) := by
  let F := zeroSpace A m
  let E := treeSpace A m
  let f : ((Fin (q+1) → K) × F) →ₗ[K] Vec K s := (polyEval A q).coprod F.subtype
  let g : ((Fin (q+1) → K) × F) →ₗ[K] E := f.codRestrict E (fun z =>
    E.add_mem (treeSpace_mono A hqm (polyEval_mem_treeSpace _ _ _))
      (zeroSpace_le_treeSpace _ _ z.2.property))
  have hg : Function.Injective g := by
    apply (injective_iff_map_eq_zero _).mpr
    intro z hz
    have h : polyEval A q z.1 + (z.2 : Vec K s) = 0 :=
      congrArg (fun w : E => (w : Vec K s)) hz
    have hneg : polyEval A q z.1 = -(z.2 : Vec K s) := eq_neg_of_add_eq_zero_left h
    have hz₁ := hsep z.1 (hneg ▸ F.neg_mem z.2.property)
    have hz₂ : (z.2 : Vec K s) = 0 := by simpa [hz₁] using h
    exact Prod.ext hz₁ (Subtype.ext hz₂)
  simpa only [Module.finrank_prod, Module.finrank_fin_fun] using
    (LinearMap.finrank_le_finrank_of_injective hg)

theorem dirk_forward_rank_three (ha : ∀ i j : Fin s, i.val<j.val → A i j=0)
    (ho : HasTreeOrderAtLeast A b p) (hp : 4≤p) :
    1 ≤ finrank K (zeroSpace A 3) := by
  have h := dirkFront_rank ha ho 1 hp
  change 1 + finrank K (dirkFront A 0) ≤ finrank K (zeroSpace A 3) at h
  omega

theorem dirk_forward_rank_three_nonzero (ha : ∀ i j : Fin s, i.val<j.val → A i j=0)
    (ho : HasTreeOrderAtLeast A b p) (hp : 4≤p) (hq : q₂ (mat A) (nodes A) 1≠0) :
    2 ≤ finrank K (zeroSpace A 3) := by
  have h := dirkFront_rank ha ho 1 hp
  change 1 + finrank K (dirkFront A 0) ≤ finrank K (zeroSpace A 3) at h
  have hl : 1 ≤ finrank K (dirkFront A 0) := by
    by_contra hh
    have hz : finrank K (dirkFront A 0)=0 := by omega
    exact hq ((twoOrbit_initial_zero hz).2)
  omega

/-- Dimension payment through grade `m+r` without assuming absence of
terminal zero weights. This retains both low reverse seeds in the ledger. -/
theorem dirk_end_count (ha : ∀ i j : Fin s, i.val<j.val → A i j=0)
    (ho : HasTreeOrderAtLeast A b p) {r : ℕ} (hr : m+r+3≤p) :
    finrank K (treeSpace A m) + r + finrank K (dirkBack A b 0) ≤ s := by
  have ht := dirkBack_rank ha ho r (by omega)
  have hs := finrank_annih_le (dirkBack_annih ho m r hr)
  omega

/-- Endpoint equality puts a genuine one-stage cardinal in the ordinary
tree space, without trimming or presuming every output weight is nonzero. -/
theorem dirk_end_cardinal (ha : ∀ i j : Fin s, i.val<j.val → A i j=0)
    (ho : HasTreeOrderAtLeast A b p) {r : ℕ} (hr : m+r+3≤p)
    (he : s ≤ finrank K (treeSpace A m) + r) :
    ∃ i : Fin s, b i ≠ 0 ∧ nodes A i=1 ∧ Pi.single i (1:K) ∈ treeSpace A m := by
  have hs := dirk_end_count ha ho hr
  have hz : finrank K (dirkBack A b 0)=0 := by omega
  obtain ⟨h₁,h₂⟩ := twoOrbit_initial_zero hz
  obtain ⟨i,hbi,hlast⟩ := last_output ho (by omega)
  have hci := dirk_last_node ha i hbi hlast h₁ h₂
  have hj : nodes A i=1 := (sub_eq_zero.mp (show 1-nodes A i=0 from hci)).symm
  have hAnn := annih_flip_le (dirkBack_annih ho m r hr)
  have hdimAnn := finrank_annih_le (le_refl (annih (dirkBack A b r)))
  have hdimBack := dirkBack_rank ha ho r (by omega)
  have hle := Submodule.finrank_mono hAnn
  have hEq := Submodule.eq_of_le_of_finrank_eq hAnn (by omega)
  refine ⟨i,hbi,hj,?_⟩
  rw [hEq,mem_annih]
  intro v hv
  have hv0 : v i = 0 := dirkBack_prior ha i hlast hci h₁ h₂ r hv i (show i ≤ i from le_rfl)
  simp [row,hv0]

/-- At equal rank, a genuine origin rules out the terminal cardinal. -/
theorem dirk_end_count_anchor {A : Fin (s+1) → Fin (s+1) → K} {b : Vec K (s+1)}
    (ha : ∀ i j : Fin (s+1), i.val<j.val → A i j=0)
    (ho : HasTreeOrderAtLeast A b p) (h0 : ∀ j, A 0 j=0) {r : ℕ}
    (hr : m+r+3≤p) (hp : 2*m+1≤p) :
    finrank K (treeSpace A m) + r + 1 ≤ s+1 := by
  by_contra hh
  obtain ⟨i,hbi,hc,hv⟩ := dirk_end_cardinal ha ho hr (by omega)
  obtain ⟨a,hf⟩ := exists_poly_zeroSpace ho (by omega) hv
  apply terminal_not_decomposable ho hp h0 i hc hbi a _ hf
  abel

/-- A full set of one-endpoint weighted polynomial moments separates without
an origin when one additional test degree is available. -/
theorem constant_moments_unanchored (ho : HasTreeOrderAtLeast A b p) (hp : 2*m+2≤p)
    (a : Fin (m+1) → K) (B : K)
    (he : ∀ k : Fin (m+2), probe A b k.val (polyEval A m a)=B) : B=0 := by
  let w : Fin (m+1) → K := fun j => a j / ((j.val+1:ℕ):K)
  have hn (n : ℕ) (hl : 0<n) (hu : n≤p) : (n:K) ≠ 0 := cast_ne_zero_of_budget ho hl hu
  have ker (i : Fin (m+1)) :
      (∑ j : Fin (m+1), w j / ((i.val+j.val+2:ℕ):K))=0 := by
    have hx : ((i.val+1:ℕ):K) ≠ 0 := hn _ (by omega) (by omega)
    apply mul_left_cancel₀ hx
    rw [mul_zero,Finset.mul_sum]
    have term (j : Fin (m+1)) :
        ((i.val+1:ℕ):K) * (w j / ((i.val+j.val+2:ℕ):K)) =
        a j / ((j.val+1:ℕ):K) - a j / ((i.val+j.val+2:ℕ):K) := by
      have h₁ := hn (j.val+1) (by omega) (by omega)
      have h₂ := hn (i.val+j.val+2) (by omega) (by omega)
      dsimp [w]; field_simp; push_cast; ring
    rw [Finset.sum_congr rfl (fun j _ => term j),Finset.sum_sub_distrib]
    have hbase := he (0 : Fin (m+2))
    have hstep := he i.succ
    rw [probe_polyEval ho (by omega)] at hbase hstep
    simp only [Fin.val_zero,zero_add] at hbase
    have hs : (∑ j : Fin (m+1), a j / ((i.val+j.val+2:ℕ):K))=B := by
      convert hstep using 2 with j
      congr 2
      simp only [Fin.val_succ]
      omega
    rw [hbase,hs,sub_self]
  have hz := moments_detect ho (d:=2) (by decide) (by omega) (fun i j => by omega) w ker
  have hbase := he (0:Fin (m+2))
  rw [probe_polyEval ho (by omega)] at hbase
  simp only [Fin.val_zero,zero_add] at hbase
  change (∑ j : Fin (m+1), w j)=B at hbase
  simpa [hz] using hbase.symm

theorem dirk_end_count_unanchored (ha : ∀ i j : Fin s, i.val<j.val → A i j=0)
    (ho : HasTreeOrderAtLeast A b p) {r : ℕ} (hr : m+r+3≤p) (hp : 2*m+2≤p) :
    finrank K (treeSpace A m) + r + 1 ≤ s := by
  by_contra hh
  obtain ⟨i,hbi,hc,hv⟩ := dirk_end_cardinal ha ho hr (by omega)
  obtain ⟨a,hf⟩ := exists_poly_zeroSpace ho (by omega) hv
  apply hbi
  apply constant_moments_unanchored ho hp a (b i)
  intro k
  have h := probe_zeroSpace ho (by omega : k.val+m+1≤p) hf
  change probe A b k.val (Pi.single i (1:K)-polyEval A m a)=0 at h
  rw [map_sub,sub_eq_zero] at h
  rw [← h]
  classical
  simp [probe,Pi.single_apply,hc]

/-- The order-twelve rank bridge: all-tree order and the genuine f₆ surplus
suffice for the checked lower count, with or without a zero first row. -/
theorem dirk_order12_of_grade6 (ha : ∀ i j : Fin s, i.val<j.val → A i j=0)
    (ho : HasTreeOrderAtLeast A b 12)
    (h₆ : finrank K (zeroSpace A 3)+4 ≤ finrank K (zeroSpace A 6)) : 15≤s := by
  classical
  have h₃ := dirk_forward_rank_three ha ho (by decide)
  have hcount := dirk_end_count ha ho (m:=6) (r:=3) (by decide)
  by_cases hq : q₂ (mat A) (nodes A) 1=0
  · cases s with
    | zero => omega
    | succ s =>
      have h₀ := dirk_first_row ha hq
      have hsep := poly_separated_of_first_row h₀ ho (m:=6) (by decide)
      have he := treeSpace_rank_of_separated A 6 hsep
      omega
  · have he := treeSpace_rank_of_delayed (A:=A) (q:=5) (m:=6) (by decide)
      (poly_separated_delayed ho (by decide) (by decide))
    have h₃n := dirk_forward_rank_three_nonzero ha ho (by decide) hq
    omega

theorem dirk_order13_of_grade6 (ha : ∀ i j : Fin s, i.val<j.val → A i j=0)
    (ho : HasTreeOrderAtLeast A b 13)
    (h₆ : finrank K (zeroSpace A 3)+4 ≤ finrank K (zeroSpace A 6)) : 17≤s := by
  classical
  have h₃ := dirk_forward_rank_three ha ho (by decide)
  have hcount := dirk_end_count ha ho (m:=6) (r:=4) (by decide)
  by_cases hq : q₂ (mat A) (nodes A) 1=0
  · cases s with
    | zero => omega
    | succ s =>
      have h₀ := dirk_first_row ha hq
      have he := treeSpace_rank_of_separated A 6
        (poly_separated_of_first_row h₀ ho (m:=6) (by decide))
      have hb := dirk_end_count_anchor ha ho h₀ (m:=6) (r:=4) (by decide) (by decide)
      omega
  · have he := treeSpace_rank ho (q:=6) (by decide)
    have h₃n := dirk_forward_rank_three_nonzero ha ho (by decide) hq
    omega

theorem dirk_order14_of_grade6 (ha : ∀ i j : Fin s, i.val<j.val → A i j=0)
    (ho : HasTreeOrderAtLeast A b 14)
    (h₆ : finrank K (zeroSpace A 3)+4 ≤ finrank K (zeroSpace A 6)) :
    18 ≤ s ∧ (q₂ (mat A) (nodes A) 1≠0 → 19≤s) := by
  classical
  have h₃ := dirk_forward_rank_three ha ho (by decide)
  have hcount := dirk_end_count_unanchored ha ho (m:=6) (r:=5) (by decide) (by decide)
  have he := treeSpace_rank ho (q:=6) (by decide)
  refine ⟨by omega,fun hq => ?_⟩
  have h₃n := dirk_forward_rank_three_nonzero ha ho (by decide) hq
  omega

theorem dirk_order15_of_grade6 (ha : ∀ i j : Fin s, i.val<j.val → A i j=0)
    (ho : HasTreeOrderAtLeast A b 15)
    (h₆ : finrank K (zeroSpace A 3)+4 ≤ finrank K (zeroSpace A 6)) : 20≤s := by
  classical
  have h₃ := dirk_forward_rank_three ha ho (by decide)
  have hcount := dirk_end_count_unanchored ha ho (m:=6) (r:=6) (by decide) (by decide)
  by_cases hq : q₂ (mat A) (nodes A) 1=0
  · have hh := Submodule.finrank_lt_finrank_of_lt (dirk_zeroSpace_lt_succ ha ho
        (j:=6) (by decide) (by decide))
    change finrank K (zeroSpace A 6) < finrank K (zeroSpace A 7) at hh
    cases s with
    | zero => omega
    | succ s =>
      have h₀ := dirk_first_row ha hq
      have he := treeSpace_rank_of_separated A 7
        (poly_separated_of_first_row h₀ ho (m:=7) (by decide))
      have hb := dirk_end_count_anchor ha ho h₀ (m:=7) (r:=5) (by decide) (by decide)
      omega
  · have he := treeSpace_rank ho (q:=6) (by decide)
    have h₃n := dirk_forward_rank_three_nonzero ha ho (by decide) hq
    omega

end RKCert.Paired
