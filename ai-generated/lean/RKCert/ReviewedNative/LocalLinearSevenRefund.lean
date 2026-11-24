module

public import RKCert.ReviewedNative.LocalLinearQuarticSeven
public import RKCert.ReviewedNative.LocalHiddenMomentBridge
public import RKCert.ReviewedNative.ReversePaidTraces

@[expose] public section

/-! # Actual same-grade refunds at the order-17 local reverse horizon

One-clock support uses the real τ sites. A sequence of consecutive
ordinary-clock representatives carries both paid polynomials by 1-X
modulo the early invariant core, with no assumed full-midpoint blindness. -/
namespace RKResearch.Certified.Graded.Reverse.LocalLinear
open RKResearch Module Polynomial RKCert.Endpoint RKCert.Endpoint.WeightedClock RKCert.OneEscape
open scoped Classical Matrix
noncomputable section

variable {K : Type*} [Field K] {s p h r j : ℕ}
variable {A : Matrix (Fin s) (Fin s) K} {b τ f g : Fin s→K}
variable {U : Submodule K (Fin s→K)}

set_option maxRecDepth 3500
set_option maxHeartbeats 850000

private theorem ordinary_clock_weighted_reflected (v : Fin s→K) (P : K[X]) :
    diag (nodes A) (weightedEval (reflectedClock A) v P)=
      weightedEval (reflectedClock A) v ((1-X)*P) := by
  ext i
  simp only [diag_apply,weightedEval_apply,eval_mul,eval_sub,eval_one,eval_X,
    reflectedClock,Pi.sub_apply,Pi.one_apply]
  ring

private theorem reflected_shift_nonzero : (1-X : K[X])≠0 := by
  intro e
  have d := Thin.one_sub_X_natDegree (K:=K)
  rw [e,natDegree_zero] at d
  exact Nat.zero_ne_one d

variable [LinearOrder K] [IsStrictOrderedRing K]

/-- A paid column seen by the reverse head at only one real clock is hidden.
The exact window is `j+r≤h`, not a fixed grade in the order-19 tableau. -/
theorem hiddenKernel_of_one_paid_head_clock (ho : HasOrder p A b)
    (F : LocalLinearBand A b h r U τ) (full : primitiveBack A b h=annih (treeSpace A (h+1)))
    (pay : 2*h+3≤p) (budget : j+r≤h) (hf : f∈zeroSpace A j) (a : K)
    (locality : ∀ i,reflectedClock A i≠a → τ i*f i=0) : f∈hiddenKernel b τ U := by
  obtain ⟨P,Q,T⟩ := local_linear_two_traces ho F full pay budget hf
  apply LocalLinearTraces.mem_hidden_of_q_zero F T
  let S := weightedSites (reflectedClock A) τ
  have count : h+1-r < S.card := F.site_count
  have rem : j<(S.erase a).card := by
    by_cases w : a∈S
    · have e := Finset.card_erase_add_one w
      omega
    · rw [Finset.erase_eq_of_notMem w]
      omega
  apply eq_zero_of_degree_lt_of_eval_finset_eq_zero (S.erase a)
  · exact degree_le_natDegree.trans_lt (by exact_mod_cast T.qDeg.trans_lt rem)
  · intro z hz
    have m := Finset.mem_erase.mp hz
    obtain ⟨i,live,eq⟩ := mem_weightedSites.mp m.2
    have t := congrFun T.tauTrace i
    rw [Pi.mul_apply,locality i (eq.trans_ne m.1),weightedEval_apply,eq] at t
    exact (mul_eq_zero.mp t.symm).resolve_right live

/-- Just one same-grade paid comparison shifts both polynomials exactly.
Faithfulness on the escaping blocks removes the early-U error; no estimate
on the number of physical rows in a block is used. -/
theorem same_grade_trace_shift {P Q P' Q' : K[X]}
    (F : LocalLinearBand A b h r U τ) (budget : j+r≤h)
    (T : LocalLinearTraces A b U τ f r j P Q) (T' : LocalLinearTraces A b U τ g r j P' Q')
    (adj : diag (nodes A) f-g∈hiddenKernel b τ U) :
    P'=(1-X)*P ∧ Q'=(1-X)*Q := by
  let y := reflectedClock A
  let H : K[X] := 1-X
  let C := diag (nodes A)
  have dH : H.natDegree=1 := Thin.one_sub_X_natDegree
  have stableQ (D E : K[X]) (dd : D.natDegree≤j) (de : E.natDegree≤j)
      (memU : weightedEval y τ (H*D-E)∈U) : E=H*D := by
    have dp : (H*D-E).natDegree≤j+1 := by
      apply (natDegree_sub_le _ _).trans
      apply max_le
      · exact natDegree_mul_le.trans (by omega)
      · omega
    have cut : (H*D-E).natDegree < (HeadFiber.escapeSites y τ U).card := by
      have n := F.escapes
      change h+1-r < (HeadFiber.escapeSites y τ U).card at n
      omega
    have eq := HeadFiber.faithful_on_escape_sites F.invariant
      (degree_le_natDegree.trans_lt (by exact_mod_cast cut)) memU
    exact (sub_eq_zero.mp eq).symm
  have pcap (D : K[X]) (d : D=0∨D.natDegree+r+1≤j) : D.natDegree≤j := by
    rcases d with e|q
    · simp [e]
    · omega
  have acts (v : Fin s→K) (D : K[X]) : C (weightedEval y v D)=weightedEval y v (H*D) :=
    ordinary_clock_weighted_reflected v D
  have τact : τ*(C f-g)=weightedEval y τ (H*Q-Q') := by
    rw [map_sub,←acts,←T.tauTrace,←T'.tauTrace]
    ext i
    simp only [C,diag_apply,Pi.sub_apply,Pi.mul_apply]
    ring
  have qmem : weightedEval y τ (H*Q-Q')∈U := by
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
  have pmem : weightedEval y τ (H*P-P')∈U := by
    rw [output]
    exact U.sub_mem (mem_hiddenKernel.mp adj).2.1 (U.sub_mem ce T'.weightTrace)
  exact ⟨stableQ P P' (pcap P T.pDeg) (pcap P' T'.pDeg) pmem,
    stableQ Q Q' T.qDeg T'.qDeg qmem⟩

theorem hiddenKernel_of_same_grade_partners_at_seven
    (ha : ∀ i k,i≤k→A i k=0) (ho : HasOrder p A b) (F : LocalLinearBand A b 7 r U τ)
    (full : primitiveBack A b 7=annih (treeSpace A 8)) (pay : 17≤p)
    {l : ℕ} (budget : j+r≤7) (refund : j≤4+l) (fs : ℕ → Fin s→K)
    (inside : ∀ a, fs a∈zeroSpace A j)
    (link : ∀ a<l, diag (nodes A) (fs a)-fs (a+1)∈hiddenKernel b τ U) :
    fs 0∈hiddenKernel b τ U := by
  have ex (a : ℕ) : ∃ P Q, LocalLinearTraces A b U τ (fs a) r j P Q :=
    local_linear_two_traces ho F full (by omega) budget (inside a)
  choose P Q tr using ex
  let H : K[X] := 1-X
  have h (a : ℕ) (aa : a≤l) : P a=H^a*P 0 ∧ Q a=H^a*Q 0 := by
    induction a with
    | zero => simp
    | succ k ih =>
      obtain ⟨ph,qh⟩ := ih (by omega)
      obtain ⟨e,g⟩ := same_grade_trace_shift F budget (tr k) (tr (k+1)) (link k (by omega))
      rw [e,g,ph,qh,pow_succ',mul_assoc,mul_assoc]
      exact ⟨rfl,rfl⟩
  obtain ⟨ph,qh⟩ := h l le_rfl
  have D (Z : K[X]) (nz : Z≠0) : (H^l*Z).natDegree=l+Z.natDegree := by
    rw [natDegree_mul (pow_ne_zero _ reflected_shift_nonzero) nz,natDegree_pow,
      Thin.one_sub_X_natDegree,mul_one]
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
      · exact (mul_ne_zero (pow_ne_zero _ reflected_shift_nonzero) z (ph.symm.trans a)).elim
      · rw [ph,D _ z] at a
        omega
  exact LocalLinearTraces.mem_hidden_of_q_zero F (tr 0)
    (local_linear_quartic_trace_zero ha ho F full pay (tr 0) dq dp)

/-- An element of a short ordinary-clock core already has actual same-grade
representatives. The paid refund applies to those representatives, not to
an arbitrary higher-grade extension. -/
theorem paid_core_le_hidden_at_seven
    (ha : ∀ i k,i≤k→A i k=0) (ho : HasOrder p A b) (F : LocalLinearBand A b 7 r U τ)
    (full : primitiveBack A b 7=annih (treeSpace A 8)) (pay : 17≤p)
    {l : ℕ} (limit : j+r≤7) (refund : j≤4+l) :
    core (diag (nodes A)) (zeroSpace A j ⊔ hiddenKernel b τ U) l≤hiddenKernel b τ U := by
  let J := hiddenKernel b τ U
  let C := diag (nodes A)
  intro z hz
  have ex (k : ℕ) : ∃ f∈zeroSpace A j, k≤l → (C^k) z-f∈J := by
    by_cases paid : k≤l
    · obtain ⟨f,hf,u,hu,s⟩ := Submodule.mem_sup.mp (mem_core.mp hz k paid)
      exact ⟨f,hf,fun _=>by rw [←s,add_comm,add_sub_cancel_right]; exact hu⟩
    · exact ⟨0,(zeroSpace A j).zero_mem,fun e=>(paid e).elim⟩
  choose fs fin fit using ex
  have h : fs 0∈J := by
    apply hiddenKernel_of_same_grade_partners_at_seven ha ho F full pay limit refund fs fin
    intro a paid
    have c : C ((C^a) z-fs a)∈J :=
      hiddenKernel_forward_clock_of_band F (Submodule.mem_map_of_mem (fit a (by omega)))
    have e : C (fs a)-fs (a+1)=((C^(a+1)) z-fs (a+1))-C ((C^a) z-fs a) := by
      rw [pow_succ',mul_apply_eq_comp,map_sub]
      abel
    rw [e]
    exact J.sub_mem (fit (a+1) (by omega)) c
  have h0 := fit 0 (Nat.zero_le l)
  rw [pow_zero,one_apply_eq_self] at h0
  simpa only [sub_add_cancel] using J.add_mem h0 h

end
end RKResearch.Certified.Graded.Reverse.LocalLinear
