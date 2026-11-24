module

public import RKCert.ReviewedNative.ERKOrderTwelveCubicAdmission

public section

/-! # Order twelve: the only surviving chart length is two

The same cubic gate excludes the real rank-three head when grade four
has rank four. Its primitive tests are paid by the first two members of
the genuine head, not by trimming its support or by moving any stage.
-/
namespace RKResearch.Certified.Graded.ERK12

open RKResearch Polynomial Module Reverse RKCert.OneEscape RKCert.Endpoint
open scoped Matrix

variable {K : Type*} [Field K] {s : ℕ}
variable {A : Matrix (Fin (s+1)) (Fin (s+1)) K} {b : Fin (s+1) → K}

/-- If the previous physical grade has the maximal rank, it is precisely
the same head shortened by one clock power. -/
theorem grade_four_of_rank_four (S : Saturation A b)
    {r : ℕ} {U : Submodule K (Fin (s+1) → K)} {w : Fin (s+1) → K}
    (H : ForwardStaircase A r U w) (four : finrank K (zeroSpace A 4)=4) :
    zeroSpace A 4=chain (diag (nodes A)) U w (r-1) := by
  classical
  let D := diag (nodes A)
  let F := zeroSpace A 5
  let L := chain D U w (r-1)
  let V := F⊓F.comap D
  have r2 := H.length
  have f5 : F=chain D U w r := by
    simpa only [Nat.add_zero] using H.initial.flags 0 (by decide)
  have next : r-1+1=r := by omega
  have lF : L⊔L.map D=F := by
    have e := clock_chain_next H.initial.coreStable (w:=w) (n:=r-1) (by omega)
    rw [next,←f5] at e
    exact e
  have low : L≤V := by
    intro x hx
    exact ⟨(show L≤F from le_sup_left.trans lF.le) hx,
      (show L.map D≤F from le_sup_right.trans lF.le) (Submodule.mem_map_of_mem hx)⟩
  have fourV : zeroSpace A 4≤V := by
    intro x hx
    exact ⟨zeroSpace_mono A (by decide : 4≤5) hx,diag_zeroSpace A 4 hx⟩
  have u : (D^r) w∉F := by
    intro tooSoon
    apply H.initial.unpaid
    change (D^(r+1)) w∈zeroSpace A 6
    rw [pow_succ',Module.End.mul_eq_comp,LinearMap.comp_apply]
    exact diag_zeroSpace A 5 tooSoon
  have p : (D^(r-1)) w∈F :=
    ((clock_chain_le_iff (T:=D) (U:=U) (w:=w) r).mp f5.ge).2 _ (by omega)
  have q : (D^(r-1)) w∉V := by
    intro h
    apply u
    have h' : D ((D^(r-1)) w)∈F := (Submodule.mem_inf.mp h).2
    rw [←next,pow_succ',Module.End.mul_eq_comp,LinearMap.comp_apply]
    exact h'
  have lt : V<F := lt_of_le_of_ne inf_le_left (fun e => q (e.symm ▸ p))
  have cap := Submodule.finrank_lt_finrank_of_lt lt
  change finrank K V < finrank K (zeroSpace A 5) at cap
  have shape : F=L⊔(K ∙ (D^(r-1)) w) := by
    calc
      _ = chain D U w r := f5
      _ = chain D U w (r-1+1) := congrArg (chain D U w) next.symm
      _ = _ := rfl
  have last : finrank K (K ∙ (D^(r-1)) w)≤1 :=
    (finrank_span_le_card ({(D^(r-1)) w}:Set (Fin (s+1) → K))).trans (by simp)
  have base := Submodule.finrank_add_le_finrank_add_finrank L (K ∙ (D^(r-1)) w)
  rw [←shape] at base
  change finrank K (zeroSpace A 5)≤finrank K L+finrank K (K ∙ (D^(r-1)) w) at base
  have f := S.f5
  have e : zeroSpace A 4=V := Submodule.eq_of_le_of_finrank_le fourV (by omega)
  exact e.trans (Submodule.eq_of_le_of_finrank_le low (by omega)).symm

variable [CharZero K]

set_option maxHeartbeats 600000 in
/-- This eliminates the rank-three/rank-four branch by direct intrinsic
head comparison, imposing no disjointness condition at any physical row. -/
theorem exclude_three_four (ha : ∀ i k, i ≤ k → A i k=0) (ho : HasOrder A b 12)
    (S : Saturation A b) (T : TerminalBand A b)
    {U : Submodule K (Fin (s+1) → K)} {w : Fin (s+1) → K}
    (H : ForwardStaircase A 3 U w) (four : finrank K (zeroSpace A 4)=4) : False := by
  let D := diag (nodes A)
  have exact4 : zeroSpace A 4=chain D U w 2 := grade_four_of_rank_four S H four
  obtain ⟨core,head⟩ := (clock_chain_le_iff (T:=D) (U:=U) (w:=w) 2).mp exact4.ge
  have w4 : w∈zeroSpace A 4 := by
    simpa only [pow_zero,Module.End.one_eq_id,LinearMap.id_apply] using head 0 (by decide)
  have dw4 : D w∈zeroSpace A 4 := by simpa only [pow_one] using head 1 (by decide)
  have f0 : w (Fin.last s)=0 :=
    grade_five_zero_at_terminal ho S (zeroSpace_mono A (by decide : 4≤5) w4)
  have f1 : D w (Fin.last s)=0 := by simp only [D,diag_apply,f0,mul_zero]
  have e1 : D (w*w)=w*(D w) := by ext i; simp only [D,diag_apply,Pi.mul_apply]; ring
  have e2 : D (w*D w)=D w*D w := by ext i; simp only [D,diag_apply,Pi.mul_apply,mul_assoc]
  have z0 : w*w∈zeroAt (zeroSpace A 8) (Fin.last s) :=
    mem_zeroAt.mpr ⟨zeroSpace_mul w4 w4,by simp only [Pi.mul_apply,f0,zero_mul]⟩
  have z1 : w*D w∈zeroAt (zeroSpace A 8) (Fin.last s) :=
    mem_zeroAt.mpr ⟨zeroSpace_mul w4 dw4,by simp only [Pi.mul_apply,f0,zero_mul]⟩
  have z2 : D w*D w∈zeroAt (zeroSpace A 8) (Fin.last s) :=
    mem_zeroAt.mpr ⟨zeroSpace_mul dw4 dw4,by simp only [Pi.mul_apply,f1,zero_mul]⟩
  have paid0 := grade_eight_no_double_leak ha ho S T H z0 (e1.symm ▸ z1)
  have paid1 := grade_eight_no_double_leak ha ho S T H z1 (e2.symm ▸ z2)
  have band (k : ℕ) (hk : k<3) : w*((D^k) w)∈chain D U w 6 := by
    rcases (show k=0 ∨ k=1 ∨ k=2 by omega) with rfl|rfl|rfl
    · simpa only [pow_zero,Module.End.one_eq_id,LinearMap.id_apply] using paid0.1
    · simpa only [pow_one] using paid1.1
    · rw [pow_two,Module.End.mul_eq_comp,LinearMap.comp_apply]
      have e : D (w*D w)=w*D (D w) := by ext i; simp only [D,diag_apply,Pi.mul_apply]; ring
      exact e ▸ paid1.2
  have stable : U.map (diag w)≤U :=
    grade_eight_multiplier_stable ha ho S T H core (by decide) w4
  have first : zeroSpace A 5=chain D U w 3 := by
    simpa only [Nat.add_zero] using H.initial.flags 0 (by decide)
  have h : w∈chain D U w 3 := first ▸ zeroSpace_mono A (by decide : 4≤5) w4
  have outside : w∉U := by
    intro wh
    have all (k : ℕ) : (D^k) w∈U := by
      induction k with
      | zero => simpa only [pow_zero,Module.End.one_eq_id,LinearMap.id_apply] using wh
      | succ k ih =>
        rw [pow_succ',Module.End.mul_eq_comp,LinearMap.comp_apply]
        exact H.initial.coreStable (Submodule.mem_map_of_mem ih)
    exact H.initial.unpaid (zeroSpace_mono A (by decide : 5≤6) (H.initial.coreInside (all 4)))
  have many := H.many
  obtain ⟨P,pn,dp,fit⟩ := HeadFiber.multiplier_profile_of_chart H.initial.coreStable stable
    (by omega : 6<(HeadFiber.escapeSites (nodes A) w U).card) (by decide : 0<3) band h outside
  apply exclude_paid_cubic_profile ha ho S T H stable pn (by omega) fit
  · intro R dR
    have dr : R.divX.natDegree≤1 := by rw [natDegree_divX_eq_natDegree_tsub_one];omega
    have g := weighted_clock_mem_grade ho dw4 (n:=1) (by decide) _ dr
    have head : R.coeff 0 • w∈zeroSpace A 5 :=
      (zeroSpace A 5).smul_mem _ (zeroSpace_mono A (by decide : 4≤5) w4)
    have e : weightedEval (nodes A) w R=weightedEval (nodes A) (D w) R.divX+R.coeff 0 • w := by
      ext i
      have p := congrArg (fun Q : K[X] => Q.eval (nodes A i)) (X_mul_divX_add R)
      simp only [eval_add,eval_mul,eval_X,eval_C] at p
      simp only [weightedEval_apply,Pi.add_apply,Pi.smul_apply,smul_eq_mul,D,diag_apply]
      rw [←p]
      ring
    exact e.symm ▸ (zeroSpace A 5).add_mem g head
  · have e : weightedEval (nodes A) w (X^3)=weightedEval (nodes A) (D w) (X^2) := by
      ext i
      simp only [weightedEval_apply,D,diag_apply,eval_pow,eval_X]
      ring
    exact e.symm ▸ weighted_clock_mem_grade ho dw4 (n:=2) (by decide) _ (by rw [natDegree_X_pow])

/-- The only two charts left at width 17 have length two. Their fourth
ranks, three and four, are both measured on the original tableau. -/
theorem remaining_rank_two_branches (ha : ∀ i k, i ≤ k → A i k=0) (ho : HasOrder A b 12)
    (S : Saturation A b) (T : TerminalBand A b)
    {r : ℕ} {U : Submodule K (Fin (s+1) → K)} {w : Fin (s+1) → K}
    (H : ForwardStaircase A r U w) :
    r=2 ∧ (finrank K (zeroSpace A 4)=3 ∨ finrank K (zeroSpace A 4)=4) := by
  have sep := explicit_coeff_separated ha ho (q:=6) (by decide)
  have l3 := zeroSpace_finrank ha ho (n:=2) (by decide)
  change 2≤finrank K (zeroSpace A 3) at l3
  have l34 := Submodule.finrank_lt_finrank_of_lt
    (zeroSpace_strict_of_separation ha sep (j:=3) (by decide) (by decide))
  have l45 := Submodule.finrank_lt_finrank_of_lt
    (zeroSpace_strict_of_separation ha sep (j:=4) (by decide) (by decide))
  change finrank K (zeroSpace A 3)<finrank K (zeroSpace A 4) at l34
  change finrank K (zeroSpace A 4)<finrank K (zeroSpace A 5) at l45
  have f := S.f5
  have three := grade_three_in_core ha ho S T H
  have size := Submodule.finrank_mono three
  have base := H.initial.baseRank
  change finrank K (zeroSpace A 5)=finrank K U+r at base
  have r2 := H.length
  have hr : r=2 := by
    by_contra n
    have eq : r=3 := by omega
    subst r
    have u3 := (Submodule.eq_of_le_of_finrank_le three (by omega)).symm
    have sep3 := (PolySeparated.of_coeff sep).mono (by decide : 3≤6)
    have g := clock_invariant_outgoing ha sep3 u3.le H.initial.coreStable
    change finrank K U+(3+1)/2≤finrank K (zeroSpace A 4) at g
    exact exclude_three_four ha ho S T H (by omega)
  exact ⟨hr,by omega⟩

end RKResearch.Certified.Graded.ERK12

