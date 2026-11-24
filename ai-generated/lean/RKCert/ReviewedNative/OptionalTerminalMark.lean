module

public import RKCert.ReviewedNative.TerminalCapacity
public import RKCert.ReviewedNative.PolynomialStageSeparation

@[expose] public section

/-! # A native optional terminal line
A nonzero first reverse seed is retained as reverse rank. If it is zero,
the line on the last stage is bought instead. This is a statement about
the original physical coordinate, not a removed stage or a new tableau. -/
namespace RKResearch.Certified.Graded.Reverse

open RKResearch Module Polynomial
noncomputable section
variable {K : Type*} [Field K] {s p q j : ℕ}
variable {A : Matrix (Fin (s+1)) (Fin (s+1)) K} {b : Fin (s+1) → K}

def terminalMark (A : Matrix (Fin (s+1)) (Fin (s+1)) K) (b : Fin (s+1) → K) :
    Submodule K (Fin (s+1) → K) := by
  classical
  exact if firstSeed A b=0 then K ∙ coordinate (Fin.last s) else ⊥

def terminalDebit (A : Matrix (Fin (s+1)) (Fin (s+1)) K) (b : Fin (s+1) → K) : ℕ := by
  classical
  exact if firstSeed A b=0 then 1 else 0

abbrev markedTreeSpace (A : Matrix (Fin (s+1)) (Fin (s+1)) K) (b : Fin (s+1) → K)
    (j : ℕ) : Submodule K (Fin (s+1) → K) := treeSpace A j ⊔ terminalMark A b

abbrev markedDefectSpace (A : Matrix (Fin (s+1)) (Fin (s+1)) K) (b : Fin (s+1) → K)
    (j : ℕ) : Submodule K (Fin (s+1) → K) := zeroSpace A j ⊔ terminalMark A b

theorem terminalDebit_balance (A : Matrix (Fin (s+1)) (Fin (s+1)) K)
    (b : Fin (s+1) → K) : terminalDebit A b + finrank K (back A b 0)=1 := by
  by_cases z : firstSeed A b=0
  · simp [terminalDebit,z,first_dim_zero z]
  · simp [terminalDebit,z,first_dim_one z]

theorem terminalMark_clock (A : Matrix (Fin (s+1)) (Fin (s+1)) K)
    (b : Fin (s+1) → K) : (terminalMark A b).map (diag (nodes A))≤terminalMark A b := by
  classical
  by_cases z : firstSeed A b=0
  · simp only [terminalMark,z,ite_true]
    rintro _ ⟨v,hv,rfl⟩
    obtain ⟨a,rfl⟩:=Submodule.mem_span_singleton.mp hv
    have e : diag (nodes A) (coordinate (K:=K) (Fin.last s)) =
        nodes A (Fin.last s) • coordinate (Fin.last s) := by
      ext i
      by_cases eq : i=Fin.last s
      · subst i
        simp [coordinate]
      · simp [coordinate,eq]
    rw [map_smul,e]
    exact (K ∙ coordinate (Fin.last s)).smul_mem _ ((K ∙ coordinate (Fin.last s)).smul_mem _
      (Submodule.mem_span_singleton_self _))
  · simp [terminalMark,z]

set_option maxHeartbeats 500000 in
theorem rank_sup_terminalMark (V : Submodule K (Fin (s+1)→K))
    (outside : firstSeed A b=0 → coordinate (K:=K) (Fin.last s) ∉ V) :
    finrank K (V ⊔ terminalMark A b : Submodule K (Fin (s+1)→K))=finrank K V+terminalDebit A b := by
  by_cases z : firstSeed A b=0
  · have line : terminalMark A b=K ∙ coordinate (Fin.last s) := by simp [terminalMark,z]
    rw [line,show terminalDebit A b=1 by simp [terminalDebit,z]]
    exact Submodule.finrank_sup_span_singleton (outside z)
  · have line : terminalMark A b=⊥ := by simp [terminalMark,z]
    rw [line,sup_bot_eq,show terminalDebit A b=0 by simp [terminalDebit,z]]
    exact (Nat.add_zero (finrank K V)).symm

theorem last_coordinate_not_defect (ho : HasOrder p A b)
    (L : LastActive b (Fin.last s)) (pay : j+1≤p) :
    coordinate (K:=K) (Fin.last s) ∉ zeroSpace A j := by
  intro hm
  have k := probe_zeroSpace (k:=0) ho (by omega) hm
  change row (fun i=>b i*(nodes A i)^0) (coordinate (Fin.last s))=0 at k
  rw [row_coordinate,pow_zero,mul_one] at k
  exact L.live k

theorem marked_defect_rank (ho : HasOrder p A b) (L : LastActive b (Fin.last s))
    (pay : j+1≤p) :
    finrank K (markedDefectSpace A b j)=finrank K (zeroSpace A j)+terminalDebit A b :=
  rank_sup_terminalMark _ (fun _=>last_coordinate_not_defect ho L pay)

theorem mark_paid_by_backward (ha : ∀ i k,i ≤ k → A i k=0) (L : LastActive b (Fin.last s))
    (n : ℕ) : back A b n ≤ annih (terminalMark A b) := by
  by_cases z : firstSeed A b=0
  · intro w hw
    rw [terminalMark,ite_eq_left z]
    apply mem_annih.mpr
    intro v hv
    obtain ⟨a,rfl⟩:=Submodule.mem_span_singleton.mp hv
    have atLast := mem_tailZero.mp (L.back_tail ha z n hw) (Fin.last s) le_rfl
    rw [map_smul,row_coordinate,atLast,smul_zero]
  · intro w _
    rw [terminalMark,ite_eq_right z]
    apply mem_annih.mpr
    intro v hv
    rw [(Submodule.mem_bot K).mp hv,map_zero]

theorem marked_tree_backward_room (ha : ∀ i k,i ≤ k → A i k=0) (ho : HasOrder p A b)
    (L : LastActive b (Fin.last s)) (j n : ℕ) (pay : j+n+2≤p) :
    finrank K (markedTreeSpace A b j)+n ≤ s+terminalDebit A b := by
  have inc : back A b n ≤ annih (markedTreeSpace A b j) := by
    intro w hw
    apply mem_annih.mpr
    change treeSpace A j ⊔ terminalMark A b ≤ (row w).ker
    exact sup_le (mem_annih.mp (back_annih ho j n pay hw))
      (mem_annih.mp (mark_paid_by_backward ha L n hw))
  have dim := finrank_annih (markedTreeSpace A b j)
  rw [Fintype.card_fin] at dim
  have low := back_finrank ha ho n (by omega)
  have hi := Submodule.finrank_mono inc
  have credit := terminalDebit_balance A b
  omega

theorem probe_terminalMark_equal (ha : ∀ i k,i ≤ k → A i k=0)
    (L : LastActive b (Fin.last s)) {v : Fin (s+1)→K}
    (h : v∈terminalMark A b) (k : ℕ) : probe A b k v=probe A b 0 v := by
  by_cases z : firstSeed A b=0
  · rw [terminalMark,ite_eq_left z] at h
    obtain ⟨a,rfl⟩:=Submodule.mem_span_singleton.mp h
    rw [map_smul,map_smul]
    congr 1
    change row (fun i=>b i*(nodes A i)^k) (coordinate (Fin.last s))=
      row (fun i=>b i*(nodes A i)^0) (coordinate (Fin.last s))
    simp only [row_coordinate,L.node_eq_one ha z,one_pow]
  · rw [terminalMark,ite_eq_right z] at h
    rw [(Submodule.mem_bot K).mp h,map_zero,map_zero]

theorem paid_probe_marked_defect (ha : ∀ i k,i ≤ k → A i k=0) (ho : HasOrder p A b)
    (L : LastActive b (Fin.last s)) {v : Fin (s+1) → K}
    (hv : v∈markedDefectSpace A b j) (k : ℕ) (pay : k+j+1≤p) :
    probe A b k v=probe A b 0 v := by
  obtain ⟨u,hu,w,hw,rfl⟩:=Submodule.mem_sup.mp hv
  have a : probe A b k u=0 := probe_zeroSpace ho pay hu
  have a0 : probe A b 0 u=0 := probe_zeroSpace ho (by omega) hu
  rw [map_add,map_add,a,a0,probe_terminalMark_equal ha L hw]

/-- The mark is physically distinct from the origin. -/
theorem origin_marked_defect (ha : ∀ i k,i ≤ k → A i k=0) (size : 0<s)
    {v : Fin (s+1)→K} (hv : v∈markedDefectSpace A b j) : v 0=0 := by
  obtain ⟨u,hu,w,hw,rfl⟩:=Submodule.mem_sup.mp hv
  have u0 : u 0=0 := origin_zeroSpace ha j hu
  suffices w0 : w 0=0 by simp [u0,w0]
  by_cases z : firstSeed A b=0
  · rw [terminalMark,ite_eq_left z] at hw
    obtain ⟨a,rfl⟩:=Submodule.mem_span_singleton.mp hw
    simp [coordinate,Nat.ne_of_gt size]
  · rw [terminalMark,ite_eq_right z] at hw
    rw [(Submodule.mem_bot K).mp hw]
    rfl

/-- The physical terminal can pay only a constant moment. The native
constant Cauchy test preserves polynomial separation through q. -/
theorem marked_coeff_separated (ha : ∀ i k,i ≤ k → A i k=0) (ho : HasOrder p A b)
    (L : LastActive b (Fin.last s)) (size : 0<s)
    (pay : q+j+1≤p) (moment : 2*q+1≤p)
    (a : Fin (q+1)→K) (hv : coeffEval A q a∈markedDefectSpace A b j) : a=0 := by
  have az := origin_marked_defect ha size hv
  rw [coeffEval_origin ha] at az
  have test (i : Fin (q+1)) :
      (∑ k : Fin q,a k.succ/((i.val+k.val+2:ℕ):K)) = probe A b 0 (coeffEval A q a) := by
    have e := paid_probe_marked_defect ha ho L hv i.val (by have :=i.isLt;omega)
    rw [probe_coeffEval ho (k:=i.val) (q:=q) (by have :=i.isLt;omega),
      Fin.sum_univ_succ,az,zero_div,zero_add] at e
    simpa only [Fin.val_succ,Nat.add_assoc] using e
  have z := (paid_constant_cauchy ho moment (fun k : Fin q=>a k.succ) _ test).1
  ext i
  exact Fin.cases az (congrFun z) i

/-- Any subspace admitting coefficient separation also separates polynomials. -/
theorem eval_eq_zero_of_coeff_separated {V : Submodule K (Fin (s+1)→K)}
    (sep : ∀ a,coeffEval A q a∈V → a=0)
    (P : K[X]) (pd : P.natDegree≤q) (ev : evalNodes A P∈V) : P=0 := by
  rw [evalNodes_eq_coeffEval A P pd] at ev
  have z := sep _ ev
  ext n
  rw [coeff_zero]
  by_cases h : n≤q
  · exact congrFun z (⟨n,by omega⟩ : Fin (q+1))
  · exact coeff_eq_zero_of_natDegree_lt (pd.trans_lt (by omega))

/-- Exact rank of a separated coefficient band adjoined to any subspace. -/
theorem rank_coeff_sup_of_separated (V : Submodule K (Fin (s+1)→K))
    (sep : ∀ a,coeffEval A q a∈V → a=0) :
    finrank K ((coeffEval A q).range ⊔ V : Submodule K (Fin (s+1)→K))=
      q+1+finrank K V := by
  let P := (coeffEval A q).range
  have dis : P⊓V=⊥ := by
    apply le_antisymm _ bot_le
    rintro v hv
    obtain ⟨⟨a,rfl⟩,hm⟩:=Submodule.mem_inf.mp hv
    rw [sep a hm,map_zero]
    exact (⊥ : Submodule K (Fin (s+1)→K)).zero_mem
  have inj : Function.Injective (coeffEval A q) := by
    apply (injective_iff_map_eq_zero _).mpr
    intro a za
    exact sep _ (za ▸ V.zero_mem)
  have poly := (LinearMap.finrank_range_of_inj inj).trans (Module.finrank_fin_fun K)
  have e := Submodule.finrank_sup_add_finrank_inf_eq P V
  rwa [dis,finrank_bot,add_zero,show finrank K P=q+1 from poly] at e

end
end RKResearch.Certified.Graded.Reverse
