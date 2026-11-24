module

public import RKCert.DirkMarkedBudget
public import RKCert.TerminalClean

@[expose] public section

/-! # Physical order-fifteen saturation, with and without C(2)

These facts derive the terminal *before* any deletion and retain the
original all-tree hypotheses. The middle marked branches are dimension
alternatives, not assertions that twenty stages exist or are excluded. -/

namespace RKCert.Paired
open Module

variable {K : Type*} [Field K] {s p j : ℕ}
variable {A : Fin s → Fin s → K} {b : Vec K s}

noncomputable abbrev terminalCardinal (K : Type*) [Field K] (s : ℕ) : Vec K (s+1) :=
  Pi.single (Fin.last s) (1:K)

theorem terminalCardinal_apply_ne {i : Fin (s+1)} (h : i≠Fin.last s) :
    terminalCardinal K s i=0 := by
  classical
  simp [terminalCardinal,h]

/-- A declaration of no future taps together with vanishing first two
reverse seeds fixes the *true* terminal row and column. -/
structure PhysicalTerminal (A : Fin (s+1) → Fin (s+1) → K)
    (b : Vec K (s+1)) : Prop where
  weight_ne : b (Fin.last s)≠0
  node_one : nodes A (Fin.last s)=1
  annihilated : mat A (terminalCardinal K s)=0
  trans_zero_terminal : ∀ u : Vec K (s+1), (transMat A) u (Fin.last s)=0
  seed1_zero : backSeed1 A b=0
  seed2_zero : q₂ (transMat A) (mirror A) b=0

theorem terminal_diag_from_seeds {A : Fin (s+1) → Fin (s+1) → K} {b : Vec K (s+1)}
    (ha : LowerArray A) (hb : b (Fin.last s)≠0)
    (h₁ : backSeed1 A b=0) (h₂ : q₂ (transMat A) (mirror A) b=0) :
    PhysicalTerminal A b := by
  classical
  let i := Fin.last s
  have ht (v : Vec K (s+1)) : transMat A v i = A i i*v i := by
    apply causalDiag_transpose ha
    intro j hj
    exact False.elim ((not_lt_of_ge (Fin.le_last j)) (Fin.rev_lt_rev.mp hj))
  have hc : mirror A i=0 :=
    dirk_last_node ha i hb (fun j hj => (not_lt_of_ge (Fin.le_last j) hj).elim) h₁ h₂
  have hdiag : A i i=0 := by
    have h := congrFun h₁ i
    change transMat A b i - mirror A i*b i=0 at h
    rw [ht,hc,zero_mul,sub_zero] at h
    exact (mul_eq_zero.mp h).resolve_right hb
  have hcol (j : Fin (s+1)) : A j i=0 := by
    rcases lt_or_eq_of_le (Fin.le_last j) with hlt|hEq
    · exact ha j i hlt
    · exact hEq ▸ hdiag
  refine ⟨hb,?_,?_,fun u => by rw [ht,hdiag,zero_mul],h₁,h₂⟩
  · change 1-nodes A i=0 at hc
    exact (sub_eq_zero.mp hc).symm
  · ext j
    change mat A (terminalCardinal K s) j=0
    rw [mat_apply,Finset.sum_eq_zero (fun k _ => ?_)]
    by_cases he : k=i
    · exact he ▸ (by rw [hcol j,zero_mul])
    · have hne : k≠Fin.last s := he
      have hk : (terminalCardinal K s) k=0 := by simp [terminalCardinal,hne]
      rw [hk,mul_zero]

theorem terminal_mirror_zero {A : Fin (s+1) → Fin (s+1) → K} {b : Vec K (s+1)}
    (ht : PhysicalTerminal A b) : mirror A (Fin.last s)=0 := by
  simp [mirror,ht.node_one]

theorem terminal_weight_from_native {A : Fin 20 → Fin 20 → K} {b : Vec K 20}
    [CharZero K] (ha : LowerArray A) (ho : HasTreeOrderAtLeast A b 15) :
    b (Fin.last 19)≠0 := by
  intro hb
  let h : 19≤20 := by decide
  have ht := order_on_lower_prefix ha ho h (fun i hi => by
    have he : i=Fin.last 19 := Fin.ext (by simp only [Fin.val_last]; have := i.isLt; omega)
    rwa [he])
  have hcount := dirk_order15_native_rank (lower_prefix ha h) ht
  omega

theorem first_row_anchored_terminal_not_mem
    {A : Fin (s+1) → Fin (s+1) → K} {b : Vec K (s+1)}
    (ho : HasTreeOrderAtLeast A b p) {m : ℕ} (hp : 2*m+1≤p)
    (ht : PhysicalTerminal A b) (h0 : ∀ j, A 0 j=0) :
    terminalCardinal K s∉treeSpace A m := by
  intro h
  obtain ⟨a,ha⟩ := exists_poly_zeroSpace ho (by omega) h
  apply terminal_not_decomposable ho hp h0 (Fin.last s) ht.node_one ht.weight_ne a _ ha
  abel

theorem terminal_last_space_of_budget
    {A : Fin (s+1) → Fin (s+1) → K} {b : Vec K (s+1)}
    (ha : LowerArray A) (ho : HasTreeOrderAtLeast A b p) (hb : b (Fin.last s)≠0)
    {m r : ℕ} (hr : m+r+3≤p) (he : s+1 ≤ finrank K (treeSpace A m)+r) :
    PhysicalTerminal A b ∧ terminalCardinal K s∈treeSpace A m := by
  have hc := dirk_end_count ha ho hr
  have hz : finrank K (dirkBack A b 0)=0 := by omega
  obtain ⟨h₁,h₂⟩ := twoOrbit_initial_zero hz
  have ht := terminal_diag_from_seeds ha hb h₁ h₂
  -- The generic witness does not record the maximality premise. Recover the
  -- specific last weighted cardinal directly from its annihilator instead.
  have hAnn := annih_flip_le (dirkBack_annih ho m r hr)
  have hd := finrank_annih_eq (dirkBack A b r)
  have hrank := dirkBack_rank ha ho r (by omega)
  have hle := Submodule.finrank_mono hAnn
  have hEq := Submodule.eq_of_le_of_finrank_eq hAnn (by omega)
  refine ⟨ht,?_⟩
  rw [hEq,mem_annih]
  intro w hw
  have hpri := dirkBack_prior ha (Fin.last s)
    (fun j hj => (not_lt_of_ge (Fin.le_last j) hj).elim)
    (terminal_mirror_zero ht) h₁ h₂ r hw
  rw [row_single_left]
  exact hpri (Fin.last s) (show Fin.last s ≤ Fin.last s from le_rfl)

theorem order15_tree_band (ha : LowerArray A) (ho : HasTreeOrderAtLeast A b 15)
    (h₇ : 7≤j) (h₁₂ : j≤12) :
    finrank K (treeSpace A 7)+(j-7) ≤ finrank K (treeSpace A j) ∧
      finrank K (treeSpace A j)+(12-j) ≤ finrank K (treeSpace A 12) := by
  have grow (k : ℕ) (hk : k≤11) :
      finrank K (treeSpace A k)+1 ≤ finrank K (treeSpace A (k+1)) :=
    Submodule.finrank_lt_finrank_of_lt (dirk_treeSpace_lt_succ ha ho (by omega))
  have bound (a n : ℕ) (hn : a+n≤12) :
      finrank K (treeSpace A a)+n ≤ finrank K (treeSpace A (a+n)) := by
    induction n with
    | zero => simp
    | succ n ih =>
      have h := ih (by omega)
      have h' := grow (a+n) (by omega)
      rw [show a+(n+1)=a+n+1 by omega]
      omega
  constructor
  · have h := bound 7 (j-7) (by omega)
    rwa [show 7+(j-7)=j by omega] at h
  · have h := bound j (12-j) (by omega)
    rwa [show j+(12-j)=12 by omega] at h

structure Order15NonC2Chart (A : Fin 20 → Fin 20 → K) (b : Vec K 20) : Prop where
  f3 : finrank K (zeroSpace A 3)=2
  f6 : finrank K (zeroSpace A 6)=6
  f7 : finrank K (zeroSpace A 7)=7
  e6 : finrank K (treeSpace A 6)=13
  treeBand : ∀ j : ℕ, 7≤j → j≤12 → finrank K (treeSpace A j)=j+8
  terminal : PhysicalTerminal (s:=19) A b
  terminal_mem : terminalCardinal K 19∈treeSpace A 7
  terminal_pure_zero : ∀ v∈zeroSpace A 7, v (Fin.last 19)=0
  all_paid : ∀ j : ℕ, 2≤j → j≤7 → marked A 15 j=dirkBack A b (j-2)

/-- This still describes a hypothetical non-C(2) extremizer. Its Radau
port exclusion must be proved separately. -/
theorem order15_nonC2_rank_chart [CharZero K] {A : Fin 20 → Fin 20 → K} {b : Vec K 20}
    (ha : LowerArray A) (ho : HasTreeOrderAtLeast A b 15)
    (hq : q₂ (mat A) (nodes A) 1≠0) : Order15NonC2Chart A b := by
  have h6 := dirk_grade_six_surplus ha ho (by decide)
  obtain ⟨h₃,h₆,h₇,e₆,e₇,_⟩ := dirk_chart15_nonorigin_of_grade6 ha ho hq h6
  have hw := terminal_weight_from_native ha ho
  have hbudget : 20≤finrank K (treeSpace A 7)+5 := by rw [e₇]
  obtain ⟨ht,hcard⟩ := terminal_last_space_of_budget (s:=19) ha ho hw (m:=7) (r:=5)
    (by decide) hbudget
  have hband (j : ℕ) (hl : 7≤j) (hu : j≤12) :
      finrank K (treeSpace A j)=j+8 := by
    obtain ⟨hl',hu'⟩ := order15_tree_band ha ho hl hu
    have h12 := Submodule.finrank_le (treeSpace A 12)
    rw [Module.finrank_fin_fun] at h12
    omega
  refine ⟨h₃,h₆,h₇,e₆,hband,ht,hcard,
    Terminal.cardinal_clean_lower ho (by decide) (Fin.last 19) hw hcard,?_⟩
  intro j hj hcap
  have hle := back_sub_marked ho hj (by omega : j+1≤15)
  have hr := dirkBack_rank ha ho (j-2) (by omega)
  have hE := hband (15-1-j) (by omega) (by omega)
  have hM := marked_rank A 15 j
  symm
  exact Submodule.eq_of_le_of_finrank_le hle (by omega)

end RKCert.Paired
