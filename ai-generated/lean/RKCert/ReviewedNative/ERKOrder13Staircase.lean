module
public import RKCert.ReviewedNative.ERKOrder13FirstMesh

@[expose] public section

/-! # Native physical order-thirteen forward staircase through grade ten -/
namespace RKResearch.Certified.Graded

open RKResearch Reverse Module Polynomial RKCert.OneEscape
open scoped Classical
noncomputable section
variable {K : Type*} [Field K] {A : Matrix (Fin 19) (Fin 19) K} {b : Fin 19→K}

private theorem order13_marked_band_next {a j l : ℕ} {U : Submodule K (Fin 19→K)}
    {w : Fin 19→K} (start : a+1≤j) (len : 0<l) (stable : U.map (diag (nodes A))≤U)
    (shape : markedTreeSpace A b j=(coeffEval A a).range⊔chain (diag (nodes A)) U w l) :
    markedTreeSpace A b j⊔(markedTreeSpace A b j).map (diag (nodes A))=
      (coeffEval A a).range⊔chain (diag (nodes A)) U w (l+1) := by
  let P := (coeffEval A a).range
  let D := diag (nodes A)
  let H := chain D U w l
  have hm : P.map D≤markedTreeSpace A b j := by
    rintro _ ⟨v,⟨t,rfl⟩,rfl⟩
    apply (show treeSpace A j≤markedTreeSpace A b j from le_sup_left)
    exact treeSpace_mono A start (diag_treeSpace A a (coeffEval_mem_treeSpace A a t))
  change markedTreeSpace A b j=P⊔H at shape
  change markedTreeSpace A b j⊔(markedTreeSpace A b j).map D=P⊔chain D U w (l+1)
  rw [shape] at hm
  rw [shape,Submodule.map_sup,←clock_chain_next stable len]
  change (P⊔H)⊔(P.map D⊔H.map D)=P⊔(H⊔H.map D)
  calc
    _ = ((P⊔H)⊔P.map D)⊔H.map D := by ac_rfl
    _ = _ := by rw [sup_eq_left.mpr hm,sup_assoc]

theorem order13_marked_clock_le (A : Matrix (Fin 19) (Fin 19) K) (b : Fin 19→K) (j : ℕ) :
    (markedTreeSpace A b j).map (diag (nodes A))≤markedTreeSpace A b (j+1) := by
  change (treeSpace A j ⊔ terminalMark A b).map (diag (nodes A)) ≤ _
  rw [Submodule.map_sup]
  exact sup_le_sup (Submodule.map_le_iff_le_comap.mpr (diag_treeSpace A j)) (terminalMark_clock A b)

variable [CharZero K]

theorem order13_marked_debit (ha : ∀i k,i≤k → A i k=0) (ho : HasOrder 13 A b)
    (F : Order13PaidFrame A b) {j : ℕ} (pos : 1≤j) (hi : j≤11)
    (sat : finrank K (markedTreeSpace A b j)=j+7+terminalDebit A b)
    (stable : (markedTreeSpace A b j).map (diag (nodes A))≤markedTreeSpace A b j) :
    finrank K (markedTreeSpace A b (j-1))+(13-j)/2≤finrank K (markedTreeSpace A b j) := by
  have need : 19≤finrank K (markedTreeSpace A b j)+(11-j)+finrank K (back A b 0) := by
    apply le_of_eq
    symm
    rw [sat]
    calc
      _ = j+7+(11-j)+(terminalDebit A b+finrank K (back A b 0)) := by ac_rfl
      _ = 19 := by rw [terminalDebit_balance A b]; omega
  have loss := marked_clock_invariant_debit ha ho F.lastActive pos (n:=11-j) (by omega) need stable
  rwa [show 11-j+2=13-j by omega] at loss

-- Keeping the preceding rank explicit is essential in the degree-six alias.
theorem order13_paid_clock_step (ha : ∀i k,i≤k → A i k=0) (ho : HasOrder 13 A b)
    (F : Order13PaidFrame A b) {j : ℕ} (lo : 6≤j) (hi : j≤9)
    (rank : finrank K (markedTreeSpace A b j)=j+7+terminalDebit A b)
    (prev : finrank K (markedTreeSpace A b (j-1))=
      if j=6 then 11+terminalDebit A b else j+6+terminalDebit A b) :
    markedTreeSpace A b (j+1)=markedTreeSpace A b j⊔(markedTreeSpace A b j).map (diag (nodes A)) ∧
      finrank K (markedTreeSpace A b (j+1))=j+1+7+terminalDebit A b := by
  have esc : ¬(markedTreeSpace A b j).map (diag (nodes A))≤markedTreeSpace A b j := by
    intro inv
    have d := order13_marked_debit ha ho F (by omega) (by omega) rank inv
    by_cases e : j=6
    · subst j
      rw [ite_eq_left (show (6:ℕ)=6 from rfl)] at prev
      omega
    · rw [ite_eq_right e] at prev
      omega
  let V := markedTreeSpace A b j
  let Z := V⊔V.map (diag (nodes A))
  have inc : Z≤markedTreeSpace A b (j+1) :=
    sup_le (sup_le_sup (treeSpace_mono A (Nat.le_succ j)) le_rfl) (order13_marked_clock_le A b j)
  have strict : V<Z := lt_of_le_of_ne le_sup_left (fun e=>esc (le_sup_right.trans e.ge))
  have low := Submodule.finrank_lt_finrank_of_lt strict
  have mid := Submodule.finrank_mono inc
  have high := F.upper (j+1) (by omega)
  change finrank K V<finrank K Z at low
  change finrank K V=_ at rank
  exact ⟨(Submodule.eq_of_le_of_finrank_le inc (by omega)).symm,by omega⟩

theorem order13_staircase_of_mesh (ha : ∀i k,i≤k → A i k=0) (ho : HasOrder 13 A b)
    (F : Order13PaidFrame A b) {a l : ℕ} {G : K[X]} {U : Submodule K (Fin 19→K)}
    {w : Fin 19→K} (M : Order13FirstMesh A b a G)
    (len : 0<l) (stable : U.map (diag (nodes A))≤U)
    (escape : order13FirstEscape A b=chain (diag (nodes A)) U w l) :
    ∀ n, a+1+n≤10 →
      markedTreeSpace A b (a+1+n)=(coeffEval A a).range⊔chain (diag (nodes A)) U w (l+n) ∧
      finrank K (markedTreeSpace A b (a+1+n))=a+1+n+7+terminalDebit A b ∧
      finrank K (markedTreeSpace A b (a+1+n-1))=
        if a+1+n=6 then 11+terminalDebit A b else a+1+n+6+terminalDebit A b := by
  have top : 6≤a+1 := by rcases M.width with e|⟨e,_⟩ <;> omega
  intro n
  induction n with
  | zero =>
    intro _
    simp only [Nat.add_zero]
    refine ⟨M.decomposition.trans (congrArg ((coeffEval A a).range ⊔ ·) escape),?_,?_⟩
    · have r := M.rank
      omega
    · rcases M.width with h|⟨h,_⟩ <;> subst a
      · exact F.rankMid
      · exact F.rankPrev
  | succ n ih =>
    intro bnd
    obtain ⟨e,r,prev⟩ := ih (by omega)
    obtain ⟨step,rnext⟩ := order13_paid_clock_step ha ho F (j:=a+1+n) (by omega) (by omega) r prev
    have out := step.trans (order13_marked_band_next (by omega) (by omega : 0<l+n) stable e)
    rw [show a+1+(n+1)=a+1+n+1 by omega,show l+(n+1)=l+n+1 by omega,
      show a+1+n+1-1=a+1+n by omega,ite_eq_right (by omega)]
    exact ⟨out,rnext,by omega⟩

structure Order13PhysicalStaircase (A : Matrix (Fin 19) (Fin 19) K) (b : Fin 19→K)
    (a : ℕ) (G : K[X]) (r : ℕ) (U : Submodule K (Fin 19→K)) (w : Fin 19→K) : Prop where
  frame : Order13PaidFrame A b
  first : Order13FirstMesh A b a G
  headLength : 2≤r ∧ r≤5
  headRank : finrank K U+r=5+terminalDebit A b
  stable : U.map (diag (nodes A))≤U
  earlyCore : U≤markedDefectSpace A b 5
  early : ∀ n≤1, markedDefectSpace A b (5+n)=chain (diag (nodes A)) U w (r+n)
  escape : order13FirstEscape A b=chain (diag (nodes A)) U w (r+2)
  full : ∀ j, a+1≤j → j≤10 →
    markedTreeSpace A b j=(coeffEval A a).range⊔chain (diag (nodes A)) U w (r+2+(j-(a+1))) ∧
    finrank K (markedTreeSpace A b j)=j+7+terminalDebit A b

theorem order13_physical_staircase (ha : ∀i k,i≤k → A i k=0) (ho : HasOrder 13 A b) :
    ∃ a G r U w, Order13PhysicalStaircase A b a G r U w := by
  have F := order13_paid_frame ha ho
  obtain ⟨a,G,M⟩ := order13_first_mesh_of_frame ha ho F
  obtain ⟨r,U,w,lo,hi,rk,stable,inc,e,escape⟩ := order13_paid_head ha ho
  refine ⟨a,G,r,U,w,⟨F,M,⟨lo,hi⟩,rk,stable,inc,e,escape,?_⟩⟩
  intro j start cutoff
  have out := order13_staircase_of_mesh ha ho F M (by omega) stable escape (j-(a+1)) (by omega)
  rw [show a+1+(j-(a+1))=j by omega] at out
  exact ⟨out.1,out.2.1⟩

theorem order13_paid_high_ranks (ha : ∀i k,i≤k → A i k=0) (ho : HasOrder 13 A b)
    {j : ℕ} (lo : 7≤j) (hi : j≤10) :
    finrank K (markedTreeSpace A b j)=j+7+terminalDebit A b := by
  obtain ⟨a,G,r,U,w,C⟩ := order13_physical_staircase ha ho
  have l : a+1≤j := by rcases C.first.width with e|e <;> omega
  exact (C.full j l hi).2

end
end RKResearch.Certified.Graded
