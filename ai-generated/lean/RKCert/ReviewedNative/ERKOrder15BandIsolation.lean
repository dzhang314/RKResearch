module

public import RKCert.ReviewedNative.ERKOrder15Staircase

@[expose] public section

/-! # Separate the paid head from the coefficient band

Every paid chart has exact direct-sum rank, so an evaluation of degree
at most the base degree cannot hide inside the actual head band. -/
namespace RKResearch.Certified.Graded

open RKResearch Reverse Module Polynomial RKCert.OneEscape
noncomputable section
variable {K : Type*} [Field K] {s a r : ℕ}
variable {A : Matrix (Fin (s+1)) (Fin (s+1)) K} {b : Fin (s+1)→K}
variable {G : K[X]} {w : Fin (s+1)→K} {U : Submodule K (Fin (s+1)→K)}

def order15HeadLength (a r j : ℕ) := r+3+(j-(a+1))

abbrev order15HeadBand (A : Matrix (Fin (s+1)) (Fin (s+1)) K) (a r j : ℕ)
    (U : Submodule K (Fin (s+1)→K)) (w : Fin (s+1)→K) : Submodule K (Fin (s+1)→K) :=
  chain (diag (nodes A)) U w (order15HeadLength a r j)

theorem clock_chain_rank_le {V : Type*} [AddCommGroup V] [Module K V] [FiniteDimensional K V]
    (D : V→ₗ[K] V) (W : Submodule K V) (v : V) (n : ℕ) :
    finrank K (chain D W v n)≤finrank K W+n := by
  classical
  induction n with
  | zero => exact le_rfl
  | succ n ih =>
    change finrank K (chain D W v n⊔Submodule.span K {(D^n) v} : Submodule K V)≤_
    have h := Submodule.finrank_add_le_finrank_add_finrank (chain D W v n) (K ∙ (D^n) v)
    have l : finrank K (K ∙ (D^n) v)≤1 := (finrank_span_le_card ({(D^n) v}:Set V)).trans (by simp)
    omega

theorem Order15PaidStaircase.base_degree (C : Order15PaidStaircase A b a G r U w) : 6≤a ∧ a≤7 := by
  rcases C.first.chartType with e|⟨e,_⟩ <;> omega

theorem Order15PaidStaircase.band_direct_rank (C : Order15PaidStaircase A b a G r U w)
    (ho : HasOrder 15 A b) {j : ℕ} (hj : a+1≤j) (hp : j≤12) :
    ((coeffEval A a).range ⊓ order15HeadBand A a r j U w)=⊥ ∧
      finrank K (order15HeadBand A a r j U w)=finrank K U+order15HeadLength a r j := by
  let P := (coeffEval A a).range
  let B := order15HeadBand A a r j U w
  change P⊓B=⊥ ∧ finrank K B=finrank K U+order15HeadLength a r j
  have qa := C.base_degree
  have inj : Function.Injective (coeffEval A a) := by
    apply (injective_iff_map_eq_zero _).mpr
    intro x h
    exact coeff_separated ho (by omega) x (h ▸ (zeroSpace A a).zero_mem)
  have pr : finrank K P=a+1 :=
    (LinearMap.finrank_range_of_inj inj).trans (Module.finrank_fin_fun K)
  have cap : finrank K B≤finrank K U+order15HeadLength a r j := clock_chain_rank_le _ _ _ _
  have eq : markedTreeSpace A b j=P⊔B := (C.full j hj hp).1
  have rankE := (C.full j hj hp).2
  have h := Submodule.finrank_sup_add_finrank_inf_eq P B
  rw [←eq,pr,rankE] at h
  have ur := C.headRank
  unfold order15HeadLength at cap ⊢
  have zero : finrank K (P⊓B : Submodule K (Fin (s+1)→K))=0 := by omega
  exact ⟨Submodule.finrank_eq_zero.mp zero,by omega⟩

theorem Order15PaidStaircase.band_separated (C : Order15PaidStaircase A b a G r U w)
    (ho : HasOrder 15 A b) {j : ℕ} (hj : a+1≤j) (hp : j≤12)
    (P : K[X]) (pd : P.natDegree≤a) (ev : evalNodes A P∈order15HeadBand A a r j U w) :
    P=0 := by
  have e := (C.band_direct_rank ho hj hp).1
  have lower := C.base_degree
  apply eval_eq_zero_of_coeff_separated (V:=order15HeadBand A a r j U w) _ P pd ev
  intro x xv
  have h : coeffEval A a x∈(coeffEval A a).range⊓order15HeadBand A a r j U w :=
    Submodule.mem_inf.mpr ⟨⟨x,rfl⟩,xv⟩
  rw [e,Submodule.mem_bot] at h
  exact coeff_separated ho (by omega) x (h ▸ (zeroSpace A a).zero_mem)

theorem Order15PaidStaircase.band_next (C : Order15PaidStaircase A b a G r U w)
    {j : ℕ} (hj : a+1≤j) :
    order15HeadBand A a r j U w ⊔ (order15HeadBand A a r j U w).map (diag (nodes A))=
      order15HeadBand A a r (j+1) U w := by
  have len : order15HeadLength a r (j+1)=order15HeadLength a r j+1 := by
    unfold order15HeadLength
    omega
  change chain (diag (nodes A)) U w (order15HeadLength a r j) ⊔
    (chain (diag (nodes A)) U w (order15HeadLength a r j)).map (diag (nodes A))=
    chain (diag (nodes A)) U w (order15HeadLength a r (j+1))
  rw [len]
  exact clock_chain_next C.stable (by unfold order15HeadLength;omega)

theorem Order15PaidStaircase.mesh_in_band (C : Order15PaidStaircase A b a G r U w) (j : ℕ) :
    evalNodes A G∈order15HeadBand A a r j U w := by
  have sub : chain (diag (nodes A)) U w (r+3)≤order15HeadBand A a r j U w := by
    have h := (clock_chain_le_iff (T:=diag (nodes A)) (U:=U) (w:=w) (order15HeadLength a r j)).mp le_rfl
    exact (clock_chain_le_iff _).mpr ⟨h.1,fun k hk=>h.2 k (by unfold order15HeadLength;omega)⟩
  exact sub (C.escape ▸ C.first.paid)

/-- The physical head is charged at grade j, or j+1 in the lower alias
branch. Both cases use the actual homogeneous defect flag. -/
theorem Order15PaidStaircase.band_paid (C : Order15PaidStaircase A b a G r U w)
    {j : ℕ} (hj : a+1≤j) :
    order15HeadBand A a r j U w≤markedDefectSpace A b (j+(7-a)) := by
  have part (n : ℕ) : order15HeadBand A a r (a+1+n) U w≤markedDefectSpace A b (8+n) := by
    induction n with
    | zero =>
      change chain (diag (nodes A)) U w (order15HeadLength a r (a+1+0))≤markedDefectSpace A b 8
      have e : order15HeadLength a r (a+1+0)=r+3 := by simp [order15HeadLength]
      rw [e,←C.escape]
      exact C.frame.escapePaid
    | succ n ih =>
      rw [show a+1+(n+1)=a+1+n+1 by omega,←C.band_next (by omega),
        show 8+(n+1)=8+n+1 by omega]
      apply sup_le (ih.trans (sup_le_sup (zeroSpace_mono A (Nat.le_succ _)) le_rfl))
      have step : (markedDefectSpace A b (8+n)).map (diag (nodes A))≤markedDefectSpace A b (8+n+1) := by
        change (zeroSpace A (8+n)⊔terminalMark A b).map (diag (nodes A))≤_
        rw [Submodule.map_sup]
        exact sup_le_sup (Submodule.map_le_iff_le_comap.mpr (diag_zeroSpace A _)) (terminalMark_clock A b)
      exact (Submodule.map_mono ih).trans step
  have h := part (j-(a+1))
  have e := C.base_degree
  rwa [show a+1+(j-(a+1))=j by omega,show 8+(j-(a+1))=j+(7-a) by omega] at h

/-- The degree-seven alias earns the actual last coordinate by grade
eight, and not by grade seven. This is physical terminal entry,
not the artificial inclusion of a charged mark. -/
theorem order15_alias_terminal_eight (ha : ∀ i l,i ≤ l → A i l=0) (ho : HasOrder 15 A b)
    (F : Order15PaidFrame A b) (C : Order15FirstEscapeChart A b 6 G) :
    coordinate (K:=K) (Fin.last s)∈treeSpace A 8 ∧ coordinate (K:=K) (Fin.last s)∉treeSpace A 7 := by
  have z := (C.chartType.resolve_left (by decide)).2
  have gd : G.natDegree=7 := C.degree
  have gn : G≠0 := by intro g; rw [g,natDegree_zero] at gd; omega
  refine ⟨?_,endpoint_coordinate_out ha ho (q:=7) (by decide) _ F.lastActive.live (F.lastActive.node_eq_one ha z)⟩
  obtain ⟨v,hv,y,hy,e⟩:=Submodule.mem_sup.mp (F.escapePaid C.paid)
  have nz : y≠0 := by
    intro h
    have ev : evalNodes A G∈zeroSpace A 8 := by rw [←e,h,add_zero]; exact hv
    exact gn (eval_eq_zero_of_coeff_separated (coeff_separated_next ha ho (by decide)) G gd.le ev)
  have yy : y∈treeSpace A 8 := by
    have eq : y=evalNodes A G-v := by rw [←e]; abel
    rw [eq]
    exact (treeSpace A 8).sub_mem (evalNodes_mem_treeSpace A G (by omega))
      (zeroSpace_le_treeSpace A 8 hv)
  rw [terminalMark,ite_eq_left z] at hy
  obtain ⟨t,rfl⟩ := Submodule.mem_span_singleton.mp hy
  have tn : t≠0 := by intro t0; exact nz (by rw [t0,zero_smul])
  exact ((treeSpace A 8).smul_mem_iff_of_isUnit (isUnit_iff_ne_zero.mpr tn)).mp yy

/-- If the mark was not charged, or its coordinate has not actually
entered by grade eight, the ordinary grade-eight defect flag is exactly
the ordinary first clock escape. -/
theorem order15_absent_terminal_grade_eight_rigid (ha : ∀ i l,i ≤ l → A i l=0)
    (ho : HasOrder 15 A b) (S : Order15PaidStaircase A b a G r U w)
    (absent : firstSeed A b≠0 ∨ coordinate (K:=K) (Fin.last s)∉treeSpace A 8) :
    zeroSpace A 8=zeroSpace A 7⊔(zeroSpace A 7).map (diag (nodes A)) := by
  let W := zeroSpace A 7⊔(zeroSpace A 7).map (diag (nodes A))
  have low : W≤zeroSpace A 8 :=
    sup_le (zeroSpace_mono A (by decide)) (Submodule.map_le_iff_le_comap.mpr (diag_zeroSpace A 7))
  have d := S.base_degree
  have m : finrank K (markedTreeSpace A b 8)=16+terminalDebit A b :=
    (S.full 8 (by omega) (by decide)).2
  have mr := rank_sup_terminalMark (treeSpace A 8)
    (fun z => absent.elim (fun h=>(h z).elim) id)
  change finrank K (markedTreeSpace A b 8)=_ at mr
  have e := odd_next_tree_rank_lower ha ho (q:=7) (by decide)
  change 8+finrank K (zeroSpace A 8)≤finrank K (treeSpace A 8) at e
  have wc := rank_sup_terminalMark (A:=A) (b:=b) W
    (fun _ h=>last_coordinate_not_defect ho (j:=8) S.frame.lastActive (by decide) (low h))
  change finrank K (order15FirstEscape A b)=_ at wc
  have rw := S.frame.escapeRank
  exact (Submodule.eq_of_le_of_finrank_le low (by omega)).symm

end
end RKResearch.Certified.Graded
