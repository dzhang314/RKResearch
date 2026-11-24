module

public import RKCert.ReviewedNative.ERKOrder15EscapeMoments
public import RKCert.ReviewedNative.MarkedReverseDebit

@[expose] public section

/-! # The actual marked order-15 chart through grade twelve

The alias starts at seven. Its first jump costs four if the forward
space is clock-invariant, while the measured previous jump was only two.
Later paid grades 8--11 have a previous jump of one, and the same native
reverse gain costs at least two. No scalar arithmetic from the eventual
lower-bound endpoint is used. -/
namespace RKResearch.Certified.Graded

open RKResearch Reverse Module Polynomial RKCert.OneEscape
noncomputable section
variable {K : Type*} [Field K] {s : ℕ}
variable {A : Matrix (Fin (s+1)) (Fin (s+1)) K} {b : Fin (s+1)→K}

theorem marked_tree_clock_le (A : Matrix (Fin (s+1)) (Fin (s+1)) K)
    (b : Fin (s+1)→K) (j : ℕ) :
    (markedTreeSpace A b j).map (diag (nodes A))≤markedTreeSpace A b (j+1) := by
  change (treeSpace A j ⊔ terminalMark A b).map (diag (nodes A)) ≤ _
  rw [Submodule.map_sup]
  exact sup_le_sup (Submodule.map_le_iff_le_comap.mpr (diag_treeSpace A j)) (terminalMark_clock A b)

private theorem marked_band_clock_next {a j l : ℕ} {U : Submodule K (Fin (s+1)→K)}
    {w : Fin (s+1)→K} (start : a+1≤j) (len : 0<l) (stable : U.map (diag (nodes A))≤U)
    (shape : markedTreeSpace A b j=(coeffEval A a).range ⊔ chain (diag (nodes A)) U w l) :
    markedTreeSpace A b j ⊔ (markedTreeSpace A b j).map (diag (nodes A))=
      (coeffEval A a).range ⊔ chain (diag (nodes A)) U w (l+1) := by
  let P := (coeffEval A a).range
  let D := diag (nodes A)
  let H := chain D U w l
  have hm : P.map D≤markedTreeSpace A b j := by
    rintro _ ⟨v,⟨t,rfl⟩,rfl⟩
    apply (show treeSpace A j≤markedTreeSpace A b j from le_sup_left)
    exact treeSpace_mono A start (diag_treeSpace A a (coeffEval_mem_treeSpace A a t))
  change markedTreeSpace A b j=P⊔H at shape
  change markedTreeSpace A b j ⊔ (markedTreeSpace A b j).map D=P⊔chain D U w (l+1)
  rw [shape] at hm
  rw [shape,Submodule.map_sup,←clock_chain_next stable len]
  change (P⊔H)⊔(P.map D⊔H.map D)=P⊔(H⊔H.map D)
  calc
    _ = ((P⊔H)⊔P.map D)⊔H.map D := by ac_rfl
    _ = _ := by rw [sup_eq_left.mpr hm,sup_assoc]

variable [CharZero K]

/-- At a saturated paid grade j, an invariant physical forward space
pays floor((15-j)/2) against the immediately preceding physical grade. -/
theorem order15_marked_clock_debit (ha : ∀ i k,i ≤ k → A i k=0) (ho : HasOrder A b 15)
    (F : Order15PaidFrame A b) {j : ℕ} (pos : 1≤j) (hi : j≤13)
    (sat : finrank K (markedTreeSpace A b j)=j+8+terminalDebit A b)
    (stable : (markedTreeSpace A b j).map (diag (nodes A))≤markedTreeSpace A b j) :
    finrank K (markedTreeSpace A b (j-1))+(15-j)/2≤finrank K (markedTreeSpace A b j) := by
  have d := terminalDebit_balance A b
  have sz := F.size
  have need : s+1≤finrank K (markedTreeSpace A b j)+(13-j)+finrank K (back A b 0) := by omega
  have paid := marked_clock_invariant_debit ha ho F.lastActive pos (n:=13-j) (by omega) need stable
  rwa [show 13-j+2=15-j by omega] at paid

/-- The first potential alias edge specifically costs four dimensions
under invariance, not merely the two sufficient for later edges. -/
theorem order15_grade7_clock_debit (ha : ∀ i k,i ≤ k → A i k=0) (ho : HasOrder A b 15)
    (F : Order15PaidFrame A b)
    (stable : (markedTreeSpace A b 7).map (diag (nodes A))≤markedTreeSpace A b 7) :
    finrank K (markedTreeSpace A b 6)+4≤finrank K (markedTreeSpace A b 7) :=
  order15_marked_clock_debit ha ho F (j:=7) (by decide) (by decide) F.rankMid stable

theorem order15_grade7_clock_escapes (ha : ∀ i k,i ≤ k → A i k=0) (ho : HasOrder A b 15)
    (F : Order15PaidFrame A b) :
    ¬(markedTreeSpace A b 7).map (diag (nodes A))≤markedTreeSpace A b 7 := by
  intro stable
  have cost := order15_grade7_clock_debit ha ho F stable
  rw [F.rankPrev,F.rankMid] at cost
  omega

/-- One actual clock step at any already full marked edge up to grade 11. -/
theorem order15_paid_clock_step (ha : ∀ i k,i ≤ k → A i k=0) (ho : HasOrder A b 15)
    (F : Order15PaidFrame A b) {j : ℕ} (lo : 7≤j) (hi : j≤11)
    (rank : finrank K (markedTreeSpace A b j)=j+8+terminalDebit A b)
    (prev : finrank K (markedTreeSpace A b (j-1))=
      if j=7 then 13+terminalDebit A b else j+7+terminalDebit A b) :
    markedTreeSpace A b (j+1)=markedTreeSpace A b j⊔(markedTreeSpace A b j).map (diag (nodes A)) ∧
      finrank K (markedTreeSpace A b (j+1))=j+1+8+terminalDebit A b := by
  have esc : ¬ (markedTreeSpace A b j).map (diag (nodes A))≤markedTreeSpace A b j := by
    intro inv
    by_cases e : j=7
    · subst j
      exact order15_grade7_clock_escapes ha ho F inv
    · have d := order15_marked_clock_debit ha ho F (j:=j) (by omega) (by omega) rank inv
      have lo : 2≤(15-j)/2 := by omega
      rw [ite_eq_right e] at prev
      omega
  let V := markedTreeSpace A b j
  let Z := V⊔V.map (diag (nodes A))
  have inc : Z≤markedTreeSpace A b (j+1) :=
    sup_le (sup_le_sup (treeSpace_mono A (Nat.le_succ j)) le_rfl) (marked_tree_clock_le A b j)
  have strict : V<Z := lt_of_le_of_ne le_sup_left (fun e=>esc (le_sup_right.trans e.ge))
  have low := Submodule.finrank_lt_finrank_of_lt strict
  have mid := Submodule.finrank_mono inc
  have high := F.upper (j+1) (by omega)
  change finrank K V<finrank K Z at low
  change finrank K V=_ at rank
  exact ⟨(Submodule.eq_of_le_of_finrank_le inc (by omega)).symm,by omega⟩

/-- Propagate from the actual marked alias/no-alias entrance along the
existing one-head chain. The statement carries the preceding rank so
the earliest two-dimensional jump is never mistaken for a unit step. -/
theorem order15_paid_staircase_of_first (ha : ∀ i k,i ≤ k → A i k=0) (ho : HasOrder A b 15)
    (F : Order15PaidFrame A b) {a l : ℕ} {G : K[X]} {U : Submodule K (Fin (s+1)→K)}
    {w : Fin (s+1)→K} (C : Order15FirstEscapeChart A b a G)
    (len : 0<l) (stable : U.map (diag (nodes A))≤U)
    (escape : order15FirstEscape A b=chain (diag (nodes A)) U w l) :
    ∀ n, a+1+n≤12 →
      markedTreeSpace A b (a+1+n)=(coeffEval A a).range⊔chain (diag (nodes A)) U w (l+n) ∧
      finrank K (markedTreeSpace A b (a+1+n))=a+1+n+8+terminalDebit A b ∧
      finrank K (markedTreeSpace A b (a+1+n-1))=
        if a+1+n=7 then 13+terminalDebit A b else a+1+n+7+terminalDebit A b := by
  have top : 7≤a+1 := by rcases C.chartType with e|⟨e,_⟩ <;> omega
  intro n
  induction n with
  | zero =>
    intro _
    simp only [Nat.add_zero]
    refine ⟨C.decomposition.trans (congrArg ((coeffEval A a).range ⊔ ·) escape),?_,?_⟩
    · have h := C.rank
      omega
    · rcases C.chartType with h|⟨h,_⟩ <;> subst a
      · exact F.rankMid
      · exact F.rankPrev
  | succ n ih =>
    intro bnd
    obtain ⟨e,r,prev⟩ := ih (by omega)
    obtain ⟨step,rnext⟩ := order15_paid_clock_step ha ho F (j:=a+1+n) (by omega) (by omega) r prev
    have out := step.trans (marked_band_clock_next (by omega) (by omega : 0<l+n) stable e)
    rw [show a+1+(n+1)=a+1+n+1 by omega,show l+(n+1)=l+n+1 by omega,
      show a+1+n+1-1=a+1+n by omega,ite_eq_right (by omega)]
    exact ⟨out,rnext,by omega⟩

structure Order15PaidStaircase (A : Matrix (Fin (s+1)) (Fin (s+1)) K) (b : Fin (s+1)→K)
    (a : ℕ) (G : K[X]) (r : ℕ) (U : Submodule K (Fin (s+1)→K)) (w : Fin (s+1)→K) : Prop where
  frame : Order15PaidFrame A b
  first : Order15FirstEscapeChart A b a G
  headLength : 2≤r
  headRank : finrank K U+r=5+terminalDebit A b
  stable : U.map (diag (nodes A))≤U
  earlyCore : U≤markedDefectSpace A b 5
  early : ∀ n≤2, markedDefectSpace A b (5+n)=chain (diag (nodes A)) U w (r+n)
  escape : order15FirstEscape A b=chain (diag (nodes A)) U w (r+3)
  full : ∀ j, a+1≤j → j≤12 →
    markedTreeSpace A b j=(coeffEval A a).range⊔chain (diag (nodes A)) U w (r+3+(j-(a+1))) ∧
    finrank K (markedTreeSpace A b j)=j+8+terminalDebit A b

/-- Complete actual initial-and-paid bands through grade twelve, with
no assumed stage ranks or scalar mesh choices. -/
theorem order15_physical_staircase (ha : ∀ i k,i ≤ k → A i k=0) (ho : HasOrder A b 15)
    (cap : s+1≤22) :
    ∃ (a : ℕ) (G : K[X]) (r : ℕ) (U : Submodule K (Fin (s+1)→K)) (w : Fin (s+1)→K),
      Order15PaidStaircase A b a G r U w := by
  obtain ⟨a,G,F,C⟩ := order15_first_escape_chart ha ho cap
  obtain ⟨r,U,w,len,rk,stable,core,early,escape⟩ := order15_paid_head ha ho cap
  refine ⟨a,G,r,U,w,⟨F,C,len,rk,stable,core,early,escape,?_⟩⟩
  intro j start cutoff
  have out := order15_paid_staircase_of_first ha ho F C (by omega) stable escape (j-(a+1)) (by omega)
  rw [show a+1+(j-(a+1))=j by omega] at out
  exact ⟨out.1,out.2.1⟩

/-- Both entrances force the same exact paid ranks at grades eight
through twelve (in particular rank 20+d at grade twelve). -/
theorem order15_marked_high_ranks (ha : ∀ i k,i ≤ k → A i k=0) (ho : HasOrder A b 15)
    (cap : s+1≤22) {j : ℕ} (lo : 8≤j) (hi : j≤12) :
    finrank K (markedTreeSpace A b j)=j+8+terminalDebit A b := by
  obtain ⟨a,G,r,U,w,S⟩ := order15_physical_staircase ha ho cap
  have lower : a+1≤j := by rcases S.first.chartType with e|⟨e,_⟩ <;> omega
  exact (S.full j lower hi).2

end
end RKResearch.Certified.Graded
