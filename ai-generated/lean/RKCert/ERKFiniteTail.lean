module
public import RKCert.ERKFiniteMidpoint

@[expose] public section

/-! # A marked terminal-coordinate ideal for all parity charts
Only the odd zero-initial-residual setup retains the extra terminal line.
This realizes prefix restriction without changing the physical tableau or
losing the actual order conditions on its full-length moments. -/
namespace RKCert.Paired.FiniteMidpoint
open RKCert.Paired Module
variable {K:Type*} [Field K] {s:ℕ}
variable {A:Fin (s+1)→Fin (s+1)→K} {b:Vec K (s+1)}

noncomputable def terminal (s:ℕ) : Vec K (s+1) := by
  classical exact Pi.single (Fin.last s) 1

noncomputable def tailPlane (K:Type*) [Field K] (s d:ℕ) : Submodule K (Vec K (s+1)) :=
  if d=0 then ⊥ else Submodule.span K {terminal s}

noncomputable def treePlus (A:Fin (s+1)→Fin (s+1)→K) (d j:ℕ) :=
  treeSpace A j ⊔ tailPlane K s d

noncomputable def defectPlus (A:Fin (s+1)→Fin (s+1)→K) (d j:ℕ) :=
  zeroSpace A j ⊔ tailPlane K s d

theorem terminal_at_last : terminal (K:=K) s (Fin.last s)=1 := by classical simp [terminal]

theorem terminal_at_ne {i:Fin (s+1)} (h:i≠Fin.last s) : terminal (K:=K) s i=0 := by
  classical simp [terminal,Pi.single_eq_of_ne h]

theorem terminal_ne : terminal (K:=K) s≠0 := by
  intro h
  have e := congrFun h (Fin.last s)
  rw [terminal_at_last,Pi.zero_apply] at e
  exact one_ne_zero e

theorem tail_rank (d:ℕ) (hd:d≤1) : finrank K (tailPlane K s d)=d := by
  by_cases h:d=0
  · subst d
    rw [tailPlane,ite_eq_left rfl]
    exact finrank_bot K (Vec K (s+1))
  · have e:d=1 := by omega
    subst d
    rw [tailPlane,ite_eq_right (by decide : (1:ℕ)≠0)]
    exact finrank_span_singleton (terminal_ne (K:=K) (s:=s))

theorem tail_supported {d:ℕ} {x:Vec K (s+1)} (hx:x∈tailPlane K s d) {i:Fin (s+1)} (hi:i≠Fin.last s) :
    x i=0 := by
  by_cases h:d=0
  · have e:x=0 := (Submodule.mem_bot K).mp (by simpa [tailPlane,h] using hx)
    rw [e];rfl
  · rw [tailPlane,ite_eq_right h] at hx
    obtain ⟨u,rfl⟩:=Submodule.mem_span_singleton.mp hx
    simp [terminal_at_ne hi]

theorem terminal_mul (v:Vec K (s+1)) :
    terminal (K:=K) s*v=v (Fin.last s) • terminal s := by
  ext i
  by_cases h:i=Fin.last s
  · subst i
    simp [terminal_at_last]
  · simp [terminal_at_ne h]

theorem tail_ideal {d:ℕ} {u:Vec K (s+1)} (hu:u∈tailPlane K s d) (v:Vec K (s+1)) :
    u*v∈tailPlane K s d := by
  by_cases h:d=0
  · have e:u=0 := (Submodule.mem_bot K).mp (by simpa [tailPlane,h] using hu)
    rw [e,zero_mul];exact (tailPlane K s d).zero_mem
  · rw [tailPlane,ite_eq_right h] at hu ⊢
    obtain ⟨a,rfl⟩:=Submodule.mem_span_singleton.mp hu
    rw [smul_mul_assoc,terminal_mul,smul_smul]
    exact (Submodule.span K {terminal s}).smul_mem _ (Submodule.subset_span (Set.mem_singleton _))

theorem tail_clock (d:ℕ) (c:Vec K (s+1)) :
    (tailPlane K s d).map (diag c)≤tailPlane K s d := by
  rintro _ ⟨u,hu,rfl⟩
  have e:diag c u=u*c := by ext i;simp [mul_comm]
  rw [e]
  exact tail_ideal hu c

theorem terminal_mat (ha:StrictLower A) : mat A (terminal s)=0 := by
  ext i
  change (∑ j : Fin (s+1),A i j*terminal s j)=0
  apply Finset.sum_eq_zero
  intro j _
  by_cases h:j=Fin.last s
  · subst j
    rw [ha i (Fin.last s) (Fin.le_last i),zero_mul]
  · rw [terminal_at_ne h,mul_zero]

theorem tail_mat (ha:StrictLower A) {d:ℕ} {u:Vec K (s+1)} (hu:u∈tailPlane K s d) :
    mat A u=0 := by
  by_cases h:d=0
  · have e:u=0 := (Submodule.mem_bot K).mp (by simpa [tailPlane,h] using hu)
    rw [e,map_zero]
  · rw [tailPlane,ite_eq_right h] at hu
    obtain ⟨a,rfl⟩:=Submodule.mem_span_singleton.mp hu
    rw [map_smul,terminal_mat ha,smul_zero]

theorem Eplus_mono (A:Fin (s+1)→Fin (s+1)→K) (d:ℕ) {j k:ℕ} (hk:j≤k) :
    treePlus A d j≤treePlus A d k := sup_le_sup (treeSpace_mono A hk) le_rfl

theorem Fplus_mono (A:Fin (s+1)→Fin (s+1)→K) (d:ℕ) {j k:ℕ} (hk:j≤k) :
    defectPlus A d j≤defectPlus A d k := sup_le_sup (zeroSpace_mono A hk) le_rfl

theorem Eplus_clock (A:Fin (s+1)→Fin (s+1)→K) (d j:ℕ) :
    (treePlus A d j).map (diag (nodes A))≤treePlus A d (j+1) := by
  unfold treePlus
  rw [Submodule.map_sup]
  exact sup_le_sup (Submodule.map_le_iff_le_comap.mpr (diag_treeSpace A j)) (tail_clock d _)

theorem Fplus_clock (A:Fin (s+1)→Fin (s+1)→K) (d j:ℕ) :
    (defectPlus A d j).map (diag (nodes A))≤defectPlus A d (j+1) := by
  unfold defectPlus
  rw [Submodule.map_sup]
  exact sup_le_sup (Submodule.map_le_iff_le_comap.mpr (diag_zeroSpace A j)) (tail_clock d _)

theorem Eplus_mat (ha:StrictLower A) (d j:ℕ) :
    (treePlus A d j).map (mat A)≤treePlus A d (j+1) := by
  unfold treePlus
  rw [Submodule.map_sup]
  apply sup_le_sup (Submodule.map_le_iff_le_comap.mpr (mat_treeSpace A j))
  rintro _ ⟨u,hu,rfl⟩
  rw [tail_mat ha hu];exact (tailPlane K s d).zero_mem

theorem Fplus_mat [CharZero K] (ha:StrictLower A) (d j:ℕ) :
    (defectPlus A d j).map (mat A)≤defectPlus A d (j+1) := by
  unfold defectPlus
  rw [Submodule.map_sup]
  apply sup_le_sup (Submodule.map_le_iff_le_comap.mpr (mat_zeroSpace_charZero A j))
  rintro _ ⟨u,hu,rfl⟩
  rw [tail_mat ha hu];exact (tailPlane K s d).zero_mem

theorem Fplus_mul {d j k:ℕ} {u v:Vec K (s+1)} (hu:u∈defectPlus A d j) (hv:v∈defectPlus A d k) :
    u*v∈defectPlus A d (j+k) := by
  obtain ⟨x,hx,y,hy,rfl⟩:=Submodule.mem_sup.mp hu
  obtain ⟨z,hz,t,ht,rfl⟩:=Submodule.mem_sup.mp hv
  rw [add_mul,mul_add,mul_add]
  apply (defectPlus A d (j+k)).add_mem
  · exact (defectPlus A d (j+k)).add_mem
      ((show zeroSpace A (j+k)≤defectPlus A d (j+k) from le_sup_left) (zeroSpace_mul hx hz))
      ((show tailPlane K s d≤defectPlus A d (j+k) from le_sup_right) (by rw [mul_comm];exact tail_ideal ht x))
  · exact (defectPlus A d (j+k)).add_mem
      ((show tailPlane K s d≤defectPlus A d (j+k) from le_sup_right) (tail_ideal hy z))
      ((show tailPlane K s d≤defectPlus A d (j+k) from le_sup_right) (tail_ideal hy t))

theorem row_terminal (w:Vec K (s+1)) : row w (terminal s)=w (Fin.last s) := by
  classical
  simp only [row_apply,terminal,Pi.single_apply,mul_ite,mul_one,mul_zero,Finset.sum_ite_eq',Finset.mem_univ,ite_true]

theorem seed_zero_of_rank_zero (h:finrank K (back A b 0)=0) : backSeed1 A b=0 := by
  have hh : backSeed1 A b∈back A b 0 := Submodule.subset_span (Set.mem_singleton _)
  rw [Submodule.finrank_eq_zero.mp h] at hh
  exact (Submodule.mem_bot K).mp hh

theorem seed_rank_cases : finrank K (back A b 0)=0∨finrank K (back A b 0)=1 := by
  by_cases h:backSeed1 A b=0
  · left
    change finrank K (Submodule.span K {backSeed1 A b})=0
    rw [h,Submodule.span_singleton_eq_bot.mpr rfl,finrank_bot]
  · exact Or.inr (finrank_span_singleton h)

structure Margin (A : Fin (s+1)→Fin (s+1)→K) (b:Vec K (s+1)) (q ε d:ℕ) : Prop where
  budget : d+finrank K (back A b 0)=ε
  atOne : d≠0→nodes A (Fin.last s)=1
  noTail : treeSpace A q ⊓ tailPlane K s d=⊥
  backTail : ∀ n,back A b n≤annih (tailPlane K s d)
  eMid : finrank K (treePlus A d q)=2*q+1+d
  ePrev : finrank K (treePlus A d (q-1))=2*q-1+d
  cap : ∀ j≤2*q+ε-2,finrank K (treePlus A d j)≤q+j+1+d

theorem margin [CharZero K] {q ε:ℕ} (ha:StrictLower A) (ho:HasTreeOrderAtLeast A b (2*q+ε))
    (hq:8≤q) (he:ε≤1) (S:Saturated A b q ε) :
    Margin A b q ε (ε-finrank K (back A b 0)) := by
  classical
  let d:=ε-finrank K (back A b 0)
  have dd : d+finrank K (back A b 0)=ε := by
    dsimp [d];have := S.seedCap;omega
  have d1 : d≤1 := by omega
  have hs0 (h:d≠0) : backSeed1 A b=0 := by
    apply seed_zero_of_rank_zero
    omega
  have no : ∀ j,Fin.last s<j→b j=0 := fun _ hj=>False.elim ((not_lt_of_ge (Fin.le_last _)) hj)
  have hnode (h:d≠0) : nodes A (Fin.last s)=1 := (sub_eq_zero.mp
    (last_mirror_zero ha S.lastLive no (hs0 h))).symm
  have htail (n:ℕ) : back A b n≤annih (tailPlane K s d) := by
    intro w hw
    apply mem_annih.mpr
    by_cases h:d=0
    · intro v hv
      have hz:v=0 := (Submodule.mem_bot K).mp (by simpa [tailPlane,h] using hv)
      rw [hz,map_zero]
    · rw [tailPlane,ite_eq_right h]
      change Submodule.span K {terminal s} ≤ (row w).ker
      apply (Submodule.span_singleton_le_iff_mem ..).mpr
      change row w (terminal s)=0
      rw [row_terminal]
      exact back_vanish ha S.lastLive no (hs0 h) n hw _ le_rfl
  have dis : treeSpace A q⊓tailPlane K s d=⊥ := by
    by_cases h:d=0
    · simp [tailPlane,h]
    · apply le_antisymm _ bot_le
      intro u hu
      obtain ⟨hE,hT⟩:=Submodule.mem_inf.mp hu
      rw [tailPlane,ite_eq_right h] at hT
      obtain ⟨a,rfl⟩:=Submodule.mem_span_singleton.mp hT
      have ne : terminal (K:=K) s ∉treeSpace A q :=
        terminal_single_not_mem ha ho (by omega : 2*q+1≤2*q+ε) _ S.lastLive (hnode h)
      have az : a=0 := by
        by_contra hn
        exact ne (((treeSpace A q).smul_mem_iff_of_isUnit (isUnit_iff_ne_zero.mpr hn)).mp hE)
      rw [az,zero_smul]
      exact (⊥:Submodule K (Vec K (s+1))).zero_mem
  have Eplus (j:ℕ) (h:j≤q) : finrank K (treePlus A d j)=finrank K (treeSpace A j)+d := by
    have small : treeSpace A j⊓tailPlane K s d=⊥ := by
      exact le_antisymm ((inf_le_inf (treeSpace_mono A h) le_rfl).trans (le_of_eq dis)) bot_le
    have ht := Submodule.finrank_sup_add_finrank_inf_eq (treeSpace A j) (tailPlane K s d)
    rw [Submodule.finrank_eq_zero.mpr small,Nat.add_zero,tail_rank d d1] at ht
    exact ht
  refine ⟨dd,hnode,dis,htail,(Eplus _ le_rfl).trans (by rw [S.eMid]),
    (Eplus _ (by omega)).trans (by rw [S.ePrev]),?_⟩
  intro j hj
  let n:=2*q+ε-2-j
  have hb : back A b n≤annih (treePlus A d j) := by
    intro w hw
    apply mem_annih.mpr
    change treePlus A d j≤(row w).ker
    exact sup_le (mem_annih.mp (back_annih ho j n (by dsimp [n];omega) hw))
      (mem_annih.mp (htail n hw))
  have hcap:=finrank_annih_le hb
  have hr:=back_finrank ha ho n (by dsimp [n];omega)
  have sz:=S.size
  change finrank K (back A b 0)+n≤finrank K (back A b n) at hr
  change finrank K (treePlus A d j)≤q+j+1+d
  have hn : n+j+2=2*q+ε := by dsimp [n];omega
  omega

theorem even_terminal_column [CharZero K] {q:ℕ} (ha:StrictLower A)
    (ho:HasTreeOrderAtLeast A b (2*q)) (hq:8≤q) (S:Saturated A b q 0) :
    nodes A (Fin.last s)=1 ∧ terminal (K:=K) s∈treeSpace A q := by
  have h0 : finrank K (back A b 0)=0 := by have := S.seedCap;omega
  have hz := seed_zero_of_rank_zero h0
  have no : ∀ j,Fin.last s<j→b j=0 := fun _ hj=>False.elim ((not_lt_of_ge (Fin.le_last _)) hj)
  have hy:=last_mirror_zero ha S.lastLive no hz
  refine ⟨(sub_eq_zero.mp hy).symm,?_⟩
  have l := back_finrank ha ho (q-2) (by omega)
  have h := back_annih ho q (q-2) (by omega)
  have hc := RKCert.Paired.OrderTwelve.backward_exact_dim (treeSpace A q)
  have exactBack : back A b (q-2)=annih (treeSpace A q) := by
    apply Submodule.eq_of_le_of_finrank_le h
    have := S.eMid
    have := S.size
    omega
  apply row_annih_test
  intro w hw
  rw [←exactBack] at hw
  rw [row_terminal]
  exact back_vanish ha S.lastLive no hz (q-2) hw _ le_rfl

theorem even_last_zero [CharZero K] {q:ℕ} (ha:StrictLower A)
    (ho:HasTreeOrderAtLeast A b (2*q)) (hq:8≤q) (S:Saturated A b q 0) :
    ∀ v∈zeroSpace A q,v (Fin.last s)=0 := by
  have ⟨_,h⟩:=even_terminal_column ha ho hq S
  have hprev (v) (hv:v∈zeroSpace A (q-1)) : v (Fin.last s)=0 := by
    have hprod := zeroSpace_mul_treeSpace ho (by omega : q+1≤2*q) hv h
    have hp := probe_zeroSpace ho (k:=0) (by omega) hprod
    change probe A b 0 (v*terminal s)=0 at hp
    rw [mul_comm,terminal_mul,map_smul,smul_eq_mul] at hp
    have ev : probe A b 0 (terminal s)=b (Fin.last s) := by
      rw [show probe A b 0 (terminal s)=row b (terminal s) by simp [probe],row_terminal]
    rw [ev] at hp
    exact (mul_eq_zero.mp hp).resolve_right S.lastLive
  have eq:=Clock.ordinary_step (A:=A) (j:=q-1)
    (by rw [show q-1+1=q by omega,S.fRank q (by omega) le_rfl,S.fRank (q-1) (by omega) (by omega)];omega)
    (midpoint_noninvariant (ε:=0) ha (by simpa using ho) S hq (by omega) (by omega))
  rw [show q-1+1=q by omega] at eq
  intro v hv
  rw [eq] at hv
  obtain ⟨u,hu,_,⟨w,hw,rfl⟩,rfl⟩:=Submodule.mem_sup.mp hv
  simp [hprev u hu,hprev w hw]

end RKCert.Paired.FiniteMidpoint

