module

public import RKCert.ReviewedNative.LocalLinearHiddenKernel

@[expose] public section

/-! # Physical one-node masks and forced loss of trace degree -/
namespace RKResearch.Certified.Graded.Reverse.LocalLinear
open RKResearch Module Polynomial RKCert.Endpoint RKCert.Endpoint.WeightedClock
open scoped Classical Matrix
noncomputable section
variable {K : Type*} [Field K] [LinearOrder K] [IsStrictOrderedRing K] {s p : ℕ}
variable {A : Matrix (Fin s) (Fin s) K} {b : Fin s→K}
variable {r j : ℕ} {U : Submodule K (Fin s→K)} {τ f g : Fin s→K}

omit [LinearOrder K] [IsStrictOrderedRing K] in
private theorem weighted_head_annih (F : LocalLinearBand A b 8 r U τ) (P : K[X]) :
    weightedEval (reflectedClock A) τ P ∈ annih U := by
  apply mem_annih.mpr
  intro w hw
  have paid := mem_annih.mp F.headOrthogonal _ (reflected_clock_weighted_core F.invariant hw P)
  rw [row_apply,dotProduct] at paid ⊢
  convert paid using 1
  apply Finset.sum_congr rfl
  intro i _
  simp only [weightedEval_apply]
  ring

theorem hiddenKernel_of_zero_head {P Q : K[X]}
    (F : LocalLinearBand A b 8 r U τ)
    (fit : LocalLinearTraces A b U τ f r j P Q) (qz : Q=0) :
    f∈hiddenKernel b τ U := by
  have t : τ*f=0 := by rw [fit.tauTrace,qz,map_zero]
  let v := weightedEval (reflectedClock A) τ P
  have d : row v (b*f)=0 := by
    rw [row_apply,dotProduct]
    apply Finset.sum_eq_zero
    intro i _
    have zi : τ i*f i=0 := congrFun t i
    simp only [v,weightedEval_apply,Pi.mul_apply]
    rw [show P.eval (reflectedClock A i)*τ i*(b i*f i)=
      P.eval (reflectedClock A i)*b i*(τ i*f i) by ring,zi,mul_zero]
  have o : row v (b*f-v)=0 := mem_annih.mp (weighted_head_annih F P) _ fit.weightTrace
  rw [map_sub,d,zero_sub,neg_eq_zero] at o
  have vz := eq_zero_of_self_row_zero o
  have w : b*f-v∈U := fit.weightTrace
  rw [vz,sub_zero] at w
  exact mem_hiddenKernel.mpr ⟨t,w,fit.preserves⟩

omit [LinearOrder K] [IsStrictOrderedRing K] in
private theorem head_sites8 (F : LocalLinearBand A b 8 r U τ) :
    8≤(weightedSites (reflectedClock A) τ).card := by
  have h := F.site_count
  rcases F.coreRank with w|w <;> omega

/-- A low paid feature visible to the reverse head at no more than one
actual clock is in the hidden algebra, even when the clock has many rows. -/
theorem hiddenKernel_of_one_clock (ho : HasOrder p A b) (F : LocalLinearBand A b 8 r U τ)
    (full : primitiveBack A b 8=annih (treeSpace A 9)) (pay : 19≤p) (cap : j≤6)
    (hf : f∈zeroSpace A j) (a : K)
    (locality : ∀ i, reflectedClock A i≠a → τ i*f i=0) :
    f∈hiddenKernel b τ U := by
  have rb : r≤2 := by rcases F.coreRank with w|w <;> omega
  obtain ⟨P,Q,T⟩ := local_linear_two_traces ho F full (by omega) (by omega) hf
  apply hiddenKernel_of_zero_head F T
  let S := weightedSites (reflectedClock A) τ
  have many : 8≤S.card := head_sites8 F
  have rem : 7≤(S.erase a).card := by
    by_cases w : a∈S
    · have e := Finset.card_erase_add_one w
      omega
    · rw [Finset.erase_eq_of_notMem w]
      omega
  apply eq_zero_of_degree_lt_of_eval_finset_eq_zero (S.erase a)
  · exact degree_le_natDegree.trans_lt (by
      exact_mod_cast (T.qDeg.trans cap).trans_lt (show 6<(S.erase a).card by omega))
  · intro z hz
    have ps := Finset.mem_erase.mp hz
    obtain ⟨i,live,eq⟩ := mem_weightedSites.mp ps.2
    have t := congrFun T.tauTrace i
    rw [Pi.mul_apply,locality i (eq.trans_ne ps.1),weightedEval_apply,eq] at t
    exact (mul_eq_zero.mp t.symm).resolve_right live

private theorem head_poly_zero_of_core (F : LocalLinearBand A b 8 r U τ) {P : K[X]}
    (d : P.natDegree≤7) (inc : weightedEval (reflectedClock A) τ P∈U) :
    P=0 := by
  have z := eq_zero_of_self_row_zero (mem_annih.mp (weighted_head_annih F P) _ inc)
  apply eq_zero_of_degree_lt_of_eval_finset_eq_zero (weightedSites (reflectedClock A) τ)
  · exact degree_le_natDegree.trans_lt (by
      have :=head_sites8 F
      exact_mod_cast d.trans_lt (show 7<(weightedSites (reflectedClock A) τ).card by omega))
  · intro a ha
    obtain ⟨i,hi,eq⟩ := mem_weightedSites.mp ha
    have e := congrFun z i
    rw [weightedEval_apply,Pi.zero_apply,eq] at e
    exact (mul_eq_zero.mp e).resolve_right hi

omit [LinearOrder K] [IsStrictOrderedRing K] in
private theorem reverseX_degree : (1-X : K[X]).natDegree=1 := by
  rw [natDegree_sub_eq_right_of_natDegree_lt (p:=1) (q:=X) (by simp),natDegree_X]

omit [LinearOrder K] [IsStrictOrderedRing K] in
private theorem reverseX_ne : (1-X : K[X])≠0 := by
  intro z
  simpa only [z,natDegree_zero,zero_ne_one] using (reverseX_degree (K:=K))

private theorem shifted_trace_agreement {P Q P' Q' : K[X]}
    (F : LocalLinearBand A b 8 r U τ) (cap : j≤6)
    (T : LocalLinearTraces A b U τ f r j P Q) (T' : LocalLinearTraces A b U τ g r j P' Q')
    (adj : diag (nodes A) f-g∈hiddenKernel b τ U) :
    P'=(1-X)*P ∧ Q'=(1-X)*Q := by
  let y := reflectedClock A
  let H : K[X] := 1-X
  let C := diag (nodes A)
  have dh : H.natDegree=1 := reverseX_degree
  have pd : P.natDegree≤j := by
    rcases T.pDeg with z|d
    · simp [z]
    · omega
  have pd' : P'.natDegree≤j := by
    rcases T'.pDeg with z|d
    · simp [z]
    · omega
  have deg (Z W : K[X]) (dZ : Z.natDegree≤j) (dW : W.natDegree≤j) :
      (H*Z-W).natDegree≤7 := by
    apply (natDegree_sub_le _ _).trans
    apply max_le
    · exact natDegree_mul_le.trans (by omega)
    · omega
  have acts (Z : K[X]) : C (weightedEval y τ Z)=weightedEval y τ (H*Z) := by
    ext i
    simp only [C,H,y,diag_apply,weightedEval_apply,eval_mul,eval_sub,eval_one,eval_X,
      reflectedClock,Pi.sub_apply,Pi.one_apply]
    ring
  have τact : τ*(C f-g)=weightedEval y τ (H*Q-Q') := by
    rw [map_sub,←acts,←T.tauTrace,←T'.tauTrace]
    ext i
    simp only [C,diag_apply,Pi.sub_apply,Pi.mul_apply]
    ring
  have qeq : weightedEval y τ (H*Q-Q')∈U := by
    rw [←τact,(mem_hiddenKernel.mp adj).1]
    exact U.zero_mem
  let e := b*f-weightedEval y τ P
  let e' := b*g-weightedEval y τ P'
  have ce : C e∈U := by
    have fwd : C e=weightedEval y e H := by
      ext i
      simp only [C,H,y,diag_apply,weightedEval_apply,eval_sub,eval_one,eval_X,reflectedClock,
        Pi.sub_apply,Pi.one_apply]
      ring
    rw [fwd]
    exact reflected_clock_weighted_core F.invariant T.weightTrace H
  have output : weightedEval y τ (H*P-P')=b*(C f-g)-(C e-e') := by
    dsimp only [e,e']
    rw [map_sub,←acts,map_sub]
    ext i
    simp only [C,diag_apply,Pi.sub_apply,Pi.mul_apply]
    ring
  have pe : weightedEval y τ (H*P-P')∈U := by
    rw [output]
    exact U.sub_mem (mem_hiddenKernel.mp adj).2.1 (U.sub_mem ce T'.weightTrace)
  exact ⟨(sub_eq_zero.mp (head_poly_zero_of_core F (deg _ _ pd pd') pe)).symm,
    (sub_eq_zero.mp (head_poly_zero_of_core F (deg _ _ T.qDeg T'.qDeg) qeq)).symm⟩

/-- The same-grade representatives of consecutive clocks force the
true forward feature into the invisible algebra when j-l ≤ 4. -/
theorem hiddenKernel_of_same_grade_partners
    (ha : ∀ i k,i≤k→A i k=0) (ho : HasOrder p A b) (F : LocalLinearBand A b 8 r U τ)
    (full : primitiveBack A b 8=annih (treeSpace A 9)) (pay : 19≤p)
    {l : ℕ} (limit : j≤6) (budget : j≤4+l) (fs : ℕ → Fin s→K)
    (inside : ∀ a, fs a∈zeroSpace A j)
    (link : ∀ a<l, diag (nodes A) (fs a)-fs (a+1)∈hiddenKernel b τ U) :
    fs 0∈hiddenKernel b τ U := by
  have rb : r≤2 := by rcases F.coreRank with w|w <;> omega
  have ex (a : ℕ) : ∃ P Q, LocalLinearTraces A b U τ (fs a) r j P Q :=
    local_linear_two_traces ho F full (by omega) (by omega) (inside a)
  choose P Q tr using ex
  let H : K[X] := 1-X
  have h (a : ℕ) (aa : a≤l) : P a=H^a*P 0 ∧ Q a=H^a*Q 0 := by
    induction a with
    | zero => simp
    | succ k ih =>
      obtain ⟨ph,qh⟩ := ih (by omega)
      obtain ⟨e,g⟩ := shifted_trace_agreement F limit (tr k) (tr (k+1)) (link k (by omega))
      rw [e,g,ph,qh,pow_succ',mul_assoc,mul_assoc]
      exact ⟨rfl,rfl⟩
  obtain ⟨ph,qh⟩ := h l le_rfl
  have D (Z : K[X]) (nz : Z≠0) : (H^l*Z).natDegree=l+Z.natDegree := by
    rw [natDegree_mul (pow_ne_zero _ reverseX_ne) nz,natDegree_pow,reverseX_degree,mul_one]
  have dq : (Q 0).natDegree≤4 := by
    by_cases z : Q 0=0
    · simp [z]
    · have caps := (tr l).qDeg
      rw [qh,D _ z] at caps
      omega
  have dp : P 0=0 ∨ (P 0).natDegree+r+1≤4 := by
    by_cases z : P 0=0
    · exact Or.inl z
    · apply Or.inr
      rcases (tr l).pDeg with a|a
      · exact (mul_ne_zero (pow_ne_zero _ reverseX_ne) z (ph.symm.trans a)).elim
      · rw [ph,D _ z] at a
        omega
  exact mem_hiddenKernel.mpr (local_linear_invisible_of_small_traces ha ho F full pay (tr 0) dq dp)

end
end RKResearch.Certified.Graded.Reverse.LocalLinear
