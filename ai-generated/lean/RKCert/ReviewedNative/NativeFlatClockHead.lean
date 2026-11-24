module

public import RKCert.ReviewedNative.ClockHeadFibers
public import RKCert.ReviewedNative.ForwardNodalGain
public import RKCert.ReviewedNative.GradedGrowth

@[expose] public section

/-! # Unit-rank intervals in the genuine native forward defect flag

An intrinsic head is produced once, then propagated to every tight grade.
Only blocks escaping the invariant core are counted; no representative
normalization or assumption on distinct stage clocks is needed. -/
namespace RKResearch.Certified.Graded
open RKResearch Module RKCert.OneEscape
open scoped Classical

variable {K : Type*} [Field K] {s : ℕ} {A : Matrix (Fin s) (Fin s) K}

structure FlatClockHead (A : Matrix (Fin s) (Fin s) K) (j d r : ℕ)
    (U : Submodule K (Fin s → K)) (w : Fin s → K) : Prop where
  positive : 0 < r
  coreStable : U.map (diag (nodes A)) ≤ U
  coreInside : U ≤ zeroSpace A j
  coreMaximal : ∀ V : Submodule K (Fin s → K),
    V.map (diag (nodes A)) ≤ V → V ≤ zeroSpace A j → V ≤ U
  baseRank : finrank K (zeroSpace A j) = finrank K U + r
  ranks : ∀ k ≤ d, finrank K (zeroSpace A (j+k)) = finrank K (zeroSpace A j) + k
  flags : ∀ k ≤ d, zeroSpace A (j+k) = chain (diag (nodes A)) U w (r+k)
  unpaid : (diag (nodes A)^(r+d)) w ∉ zeroSpace A (j+d)
  extraSites : r+d < (HeadFiber.escapeSites (nodes A) w U).card

variable [CharZero K]

theorem zeroSpace_rank_interval_of_separation {q j d : ℕ}
    (ha : ∀ i k, i ≤ k → A i k=0)
    (sep : ∀ a, coeffEval A q a∈zeroSpace A q → a=0)
    (pos : 1≤j) (cap : j+d≤q) :
    finrank K (zeroSpace A j)+d ≤ finrank K (zeroSpace A (j+d)) := by
  induction d with
  | zero => simp
  | succ d ih =>
    have low := ih (by omega)
    have jump := Submodule.finrank_lt_finrank_of_lt
      (zeroSpace_strict_of_separation ha sep (j:=j+d) (by omega) (by omega))
    rw [show j+(d+1)=j+d+1 by omega]
    omega

set_option maxRecDepth 2500 in
/-- Every lower step in a nonempty flat interval above grade three is
clock-noninvariant by the outgoing Hermite bound; at its last grade the
incoming bound supplies the escape without borrowing another grade. -/
theorem flat_clock_head (ha : ∀ i k, i ≤ k → A i k=0) {j d : ℕ}
    (coeffSep : ∀ a, coeffEval A (j+d) a∈zeroSpace A (j+d) → a=0)
    (early : 3≤j) (positive : 0<d)
    (cap : finrank K (zeroSpace A (j+d)) ≤ finrank K (zeroSpace A j)+d) :
    ∃ r U w, FlatClockHead A j d r U w := by
  let F := zeroSpace A
  let T := diag (nodes A)
  have sep : PolySeparated A (j+d) := PolySeparated.of_coeff coeffSep
  have rank (k : ℕ) (hk : k≤d) : finrank K (F (j+k)) = finrank K (F j)+k := by
    have lo := zeroSpace_rank_interval_of_separation ha coeffSep (j:=j) (d:=k) (by omega) (by omega)
    have hi := zeroSpace_rank_interval_of_separation ha coeffSep (j:=j+k) (d:=d-k) (by omega) (by omega)
    rw [show (j+k)+(d-k)=j+d by omega] at hi
    change finrank K (F (j+k))+(d-k) ≤ finrank K (F (j+d)) at hi
    change finrank K (F j)+k ≤ finrank K (F (j+k)) at lo
    change finrank K (F (j+d)) ≤ finrank K (F j)+d at cap
    omega
  have esc (k : ℕ) (hk : k≤d) : ¬ (F (j+k)).map T ≤ F (j+k) := by
    intro inv
    by_cases last : k=d
    · subst k
      let z := j+d-1
      have zx : z+1=j+d := by dsimp [z]; omega
      have inv' : (F (z+1)).map T ≤ F (z+1) := zx.symm ▸ inv
      have g := clock_invariant_incoming ha (j:=z) (sep.mono (by omega)) inv'
      change finrank K (F z)+(z+1)/2 ≤ finrank K (F (z+1)) at g
      have dz : z=j+(d-1) := by dsimp [z];omega
      rw [zx,dz,rank d le_rfl,rank (d-1) (by omega)] at g
      omega
    · have g := clock_invariant_outgoing ha (sep.mono (show j+k≤j+d by omega)) le_rfl inv
      change finrank K (F (j+k))+(j+k+1)/2 ≤ finrank K (F (j+k+1)) at g
      rw [show j+k+1=j+(k+1) by omega,rank k hk,rank (k+1) (by omega)] at g
      omega
  have step (k : ℕ) (hk : k<d) : F (j+k+1) = F (j+k) ⊔ (F (j+k)).map T := by
    apply zeroSpace_clock_step_of_unit
    · change finrank K (F (j+k+1)) ≤ finrank K (F (j+k))+1
      rw [show j+k+1=j+(k+1) by omega,rank (k+1) (by omega),rank k hk.le]
      omega
    · exact esc k hk.le
  have e : F (j+1) = F j ⊔ (F j).map T := by simpa only [Nat.add_zero] using step 0 positive
  have one : finrank K (F j ⊔ (F j).map T : Submodule K (Fin s→K)) ≤ finrank K (F j)+1 := by
    rw [←e,rank 1 (by omega)]
  have out : ¬ (F j).map T ≤ F j := by simpa only [Nat.add_zero] using esc 0 (by omega)
  obtain ⟨r,U,w,r0,stable,inside,max,base,_,_,dim⟩ := single_head one out
  have flag (k : ℕ) (hk : k≤d) : F (j+k) = chain T U w (r+k) := by
    induction k with
    | zero => simpa only [Nat.add_zero] using base
    | succ k ih =>
      rw [show j+(k+1)=j+k+1 by omega,step k (by omega),ih (by omega),clock_chain_next stable (by omega)]
      rfl
  have outLast : ¬ (chain T U w (r+d)).map T ≤ chain T U w (r+d) := flag d le_rfl ▸ esc d le_rfl
  refine ⟨r,U,w,⟨r0,stable,inside,max,dim,rank,flag,?_,?_⟩⟩
  · change (T^(r+d)) w ∉ F (j+d)
    rw [flag d le_rfl]
    intro h
    apply outLast
    apply le_sup_right.trans
    rw [clock_chain_next stable (show 0<r+d by omega),chain]
    exact sup_le le_rfl ((Submodule.span_singleton_le_iff_mem _ _).mpr h)
  · exact HeadFiber.more_escape_sites stable (by omega) outLast

end RKResearch.Certified.Graded
