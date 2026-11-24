module

public import RKCert.ReviewedNative.ERKOrderTwelveSaturation
public import RKCert.ReviewedNative.TwoEndpointClockSeparation
public import RKCert.ReviewedNative.ReverseClockGain

public section

/-! # Native physical terminal band at order twelve

At a 17-stage cap the true seventh tree space is the degree-six clock
band plus the next clock escape of the original forward defects. The
seventh-grade terminal cut and the reverse flags supply exact rank-eight
and rank-nine spaces. The rank-one final reverse escape is separate.
-/
namespace RKResearch.Certified.Graded.ERK12

open RKResearch Module Reverse RKCert.OneEscape

variable {K : Type*} [Field K] {s : ℕ}
variable {A : Matrix (Fin (s+1)) (Fin (s+1)) K} {b : Fin (s+1) → K}

noncomputable abbrev clockBand6 (A : Matrix (Fin (s+1)) (Fin (s+1)) K) :=
  (coeffEval A 6).range

noncomputable abbrev escape7 (A : Matrix (Fin (s+1)) (Fin (s+1)) K) :=
  zeroSpace A 6 ⊔ (zeroSpace A 6).map (diag (nodes A))

private theorem clockBand6_le {j : ℕ} (h : 6≤j) : clockBand6 A ≤ treeSpace A j := by
  rintro _ ⟨a,rfl⟩
  exact treeSpace_mono A h (coeffEval_mem_treeSpace A 6 a)

private theorem clockBand6_rank_sup {V : Submodule K (Fin (s+1) → K)}
    (sep : ∀ a, coeffEval A 6 a∈V → a=0) :
    finrank K ↥(clockBand6 A ⊔ V)=7+finrank K V := by
  have inj : Function.Injective (coeffEval A 6) :=
    (injective_iff_map_eq_zero _).mpr (fun a h => sep a (h ▸ V.zero_mem))
  have dim : finrank K (clockBand6 A)=7 := by
    exact (LinearMap.finrank_range_of_inj inj).trans (finrank_fin_fun K)
  have dis : clockBand6 A ⊓ V=⊥ := by
    apply le_antisymm _ bot_le
    intro v h
    obtain ⟨⟨a,rfl⟩,hv⟩ := Submodule.mem_inf.mp h
    rw [sep a hv,map_zero]
    exact (⊥ : Submodule K (Fin (s+1) → K)).zero_mem
  have d := Submodule.finrank_sup_add_finrank_inf_eq (clockBand6 A) V
  rwa [dis,finrank_bot,add_zero,dim] at d

/-- A true tree grade strictly grows when its clock image escapes. -/
theorem tree_rank_lt_of_clock_escape {j : ℕ}
    (esc : ¬(treeSpace A j).map (diag (nodes A))≤treeSpace A j) :
    finrank K (treeSpace A j)<finrank K (treeSpace A (j+1)) := by
  apply Submodule.finrank_lt_finrank_of_lt
  refine lt_of_le_of_ne (treeSpace_mono A (Nat.le_succ j)) ?_
  intro eq
  exact esc ((Submodule.map_le_iff_le_comap.mpr (diag_treeSpace A j)).trans eq.ge)

structure TerminalBand (A : Matrix (Fin (s+1)) (Fin (s+1)) K) (b : Fin (s+1) → K) : Prop where
  cut : escape7 A=zeroAt (zeroSpace A 7) (Fin.last s)
  cutRank : finrank K (escape7 A)=7
  e7 : treeSpace A 7=clockBand6 A ⊔ escape7 A
  e7Rank : finrank K (treeSpace A 7)=14
  back3 : back A b 3=annih (treeSpace A 7)

structure ReverseSevenNine (A : Matrix (Fin (s+1)) (Fin (s+1)) K) (b : Fin (s+1) → K) : Prop where
  treeEscape7 : ¬(treeSpace A 7).map (diag (nodes A))≤treeSpace A 7
  e8Rank : finrank K (treeSpace A 8)=15
  back2 : back A b 2=annih (treeSpace A 8)
  treeEscape8 : ¬(treeSpace A 8).map (diag (nodes A))≤treeSpace A 8
  e9Rank : finrank K (treeSpace A 9)=16
  back1 : back A b 1=annih (treeSpace A 9)
  reverseEscape2 : ¬(back A b 2).map (diag (reflectedClock A))≤back A b 2
  reverseEscape3 : ¬(back A b 3).map (diag (reflectedClock A))≤back A b 3

variable [CharZero K]

theorem terminal_band (ha : ∀ i k, i ≤ k → A i k=0) (ho : HasOrder 12 A b)
    (S : Saturation A b) : TerminalBand A b := by
  let t := Fin.last s
  let Z := zeroAt (zeroSpace A 7) t
  have sep : ∀ a, coeffEval A 6 a ∈ Z → a=0 :=
    coeff_separated_two_endpoints ha ho (n:=5) (j:=7) (by decide) (by decide) S.terminalClock
  have dim := clockBand6_rank_sup (A:=A) sep
  have inc : clockBand6 A ⊔ Z ≤ treeSpace A 7 :=
    sup_le (clockBand6_le (by decide)) (inf_le_left.trans (zeroSpace_le_treeSpace A 7))
  have cap := S.caps 7 (by decide)
  have dcap := Submodule.finrank_mono inc
  have zcap : finrank K Z≤7 := by omega
  have here : escape7 A≤Z := by
    apply sup_le
    · intro v hv
      exact mem_zeroAt.mpr ⟨zeroSpace_mono A (by decide : 6≤7) hv,
        grade_six_zero_at_terminal ha ho S hv⟩
    · rintro _ ⟨v,hv,rfl⟩
      exact mem_zeroAt.mpr ⟨diag_zeroSpace A 6 hv,
        by rw [diag_apply,grade_six_zero_at_terminal ha ho S hv,mul_zero]⟩
  obtain ⟨r,U,w,_,H⟩ := exists_order_twelve_head ha ho S
  have eq : zeroSpace A 6=chain (diag (nodes A)) U w (r+1) := H.flags 1 (by decide)
  have escape : ¬ (zeroSpace A 6).map (diag (nodes A))≤zeroSpace A 6 := by
    intro inv
    apply H.unpaid
    have paid := ((clock_chain_le_iff (T:=diag (nodes A)) (U:=U) (w:=w) (r+1)).mp eq.ge).2 r (by omega)
    rw [pow_succ',Module.End.mul_eq_comp,LinearMap.comp_apply]
    exact inv (Submodule.mem_map_of_mem paid)
  have step : zeroSpace A 6 < escape7 A := lt_of_le_of_ne le_sup_left
    (fun e => escape (le_sup_right.trans e.ge))
  have low := Submodule.finrank_lt_finrank_of_lt step
  have incRank := Submodule.finrank_mono here
  have r6 := S.f6
  have rank : finrank K (escape7 A)=7 := by omega
  have cut : escape7 A=Z := Submodule.eq_of_le_of_finrank_le here (by omega)
  have zr : finrank K Z=7 := by rwa [←cut]
  rw [zr] at dim
  have e7 : treeSpace A 7=clockBand6 A ⊔ escape7 A := by
    rw [cut]
    exact (Submodule.eq_of_le_of_finrank_le inc (by omega)).symm
  have e7Rank : finrank K (treeSpace A 7)=14 := by
    rw [e7,cut]
    exact dim
  have rb3 := (S.backExact 3 (by decide)).1
  have size := S.size
  exact ⟨cut,rank,e7,e7Rank,back_eq_annih_of_rank ho (by decide) (by omega)⟩

/-- The same single head now extends to the actual seventh tree space,
without spending a second polynomial direction. -/
theorem exists_order_twelve_head_at_seven (ha : ∀ i k, i ≤ k → A i k=0) (ho : HasOrder 12 A b)
    (S : Saturation A b) (T : TerminalBand A b) :
    ∃ r U w, 2≤r ∧ FlatClockHead A 5 1 r U w ∧
      escape7 A=chain (diag (nodes A)) U w (r+2) ∧
      treeSpace A 7=clockBand6 A ⊔ chain (diag (nodes A)) U w (r+2) := by
  obtain ⟨r,U,w,r2,H⟩ := exists_order_twelve_head ha ho S
  have e : zeroSpace A 6=chain (diag (nodes A)) U w (r+1) := H.flags 1 (by decide)
  have last : escape7 A=chain (diag (nodes A)) U w (r+2) := by
    change zeroSpace A 6 ⊔ (zeroSpace A 6).map (diag (nodes A))=_
    rw [e,clock_chain_next H.coreStable (by omega)]
  exact ⟨r,U,w,r2,H,last,T.e7.trans (congrArg (fun V => clockBand6 A ⊔ V) last)⟩

/-- The actual reverse flags at levels two and three would gain two
dimensions if clock invariant, but their paid next ranks gain only one. -/
theorem reverse_clock_escape (ha : ∀ i k, i ≤ k → A i k=0) (ho : HasOrder 12 A b)
    (S : Saturation A b) {n : ℕ} (lo : 2≤n) (hi : n<4) :
    ¬(back A b n).map (diag (reflectedClock A))≤back A b n := by
  intro inc
  obtain ⟨rank,eq⟩ := S.backExact n (by omega)
  obtain ⟨next,nextEq⟩ := S.backExact (n+1) (by omega)
  rw [eq] at inc
  have g := reverse_clock_invariant_gain ha ho n (by omega) inc
  rw [←eq,←nextEq,rank,next] at g
  omega

omit [CharZero K] in
theorem tree_escape_of_reverse_escape {j n : ℕ}
    (backEq : back A b n=annih (treeSpace A j))
    (esc : ¬(back A b n).map (diag (reflectedClock A))≤back A b n) :
    ¬(treeSpace A j).map (diag (nodes A))≤treeSpace A j := by
  intro inc
  apply esc
  rw [backEq]
  rintro _ ⟨v,vAnn,rfl⟩
  apply mem_annih.mpr
  intro w wIn
  rw [row_diag]
  apply mem_annih.mp vAnn
  have e : diag (reflectedClock A) w = w - diag (nodes A) w := by
    ext i
    simp [reflectedClock,sub_mul]
  rw [e]
  exact (treeSpace A j).sub_mem wIn (inc (Submodule.mem_map_of_mem wIn))

/-- Exact paid tree and actual backward flags through grade nine. This
does not assert that the final one-dimensional reverse flag escapes. -/
theorem reverse_seven_nine (ha : ∀ i k, i ≤ k → A i k=0) (ho : HasOrder 12 A b)
    (S : Saturation A b) (T : TerminalBand A b) : ReverseSevenNine A b := by
  have e7 := tree_escape_of_reverse_escape T.back3
    (reverse_clock_escape ha ho S (n:=3) (by decide) (by decide))
  have r8lo := tree_rank_lt_of_clock_escape e7
  change finrank K (treeSpace A 7)<finrank K (treeSpace A 8) at r8lo
  have r8hi := S.caps 8 (by decide)
  have r7 := T.e7Rank
  have r8 : finrank K (treeSpace A 8)=15 := by omega
  have b2 := (S.backExact 2 (by decide)).1
  have size := S.size
  have eB2 := back_eq_annih_of_rank (n:=2) (j:=8) ho (by decide) (by omega)
  have e8 := tree_escape_of_reverse_escape eB2
    (reverse_clock_escape ha ho S (n:=2) (by decide) (by decide))
  have r9lo := tree_rank_lt_of_clock_escape e8
  change finrank K (treeSpace A 8)<finrank K (treeSpace A 9) at r9lo
  have r9hi := S.caps 9 (by decide)
  have r9 : finrank K (treeSpace A 9)=16 := by omega
  have b1 := (S.backExact 1 (by decide)).1
  have eB1 := back_eq_annih_of_rank (n:=1) (j:=9) ho (by decide) (by omega)
  exact ⟨e7,r8,eB2,e8,r9,eB1,reverse_clock_escape ha ho S (by decide) (by decide),
    reverse_clock_escape ha ho S (by decide) (by decide)⟩

end RKResearch.Certified.Graded.ERK12
