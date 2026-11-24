module

public import RKCert.ReviewedNative.ERK17ReverseSupport
public import RKCert.ReviewedNative.ClockHeadSupport

@[expose] public section

/-! # Intrinsic local linear seed, with an orthogonal reverse head

Only the exact primitive ranks and clock escapes are passed in.
The chosen head is in the first escaping grade and orthogonal to the
stable core for the literal coordinate dot product over an ordered field. -/
namespace RKResearch.Certified.Graded.Reverse
open RKResearch Polynomial Module RKCert.Endpoint RKCert.Endpoint.WeightedClock RKCert.OneEscape
open scoped Classical Matrix
noncomputable section
variable {K : Type*} [Field K] {s : ℕ}
variable {A : Matrix (Fin s) (Fin s) K} {b : Fin s→K}

private theorem clock_stable_of_complete_weighted {c d : Fin s→K} {L : Submodule K (Fin s→K)}
    (e : L=(weightedEval c d).range) : L.map (diag c)≤L := by
  rintro _ ⟨v,h,rfl⟩
  rw [e] at h ⊢
  exact weighted_range_clock c d h

private theorem strict_sup_clock_rank {c : Fin s→K} {U : Submodule K (Fin s→K)}
    (escape : ¬U.map (diag c)≤U) :
    finrank K U < finrank K (U⊔U.map (diag c) : Submodule K (Fin s→K)) := by
  apply Submodule.finrank_lt_finrank_of_lt
  apply lt_of_le_of_ne le_sup_left
  intro e
  exact escape (le_sup_right.trans e.ge)

structure LocalLinearBand (A : Matrix (Fin s) (Fin s) K) (b : Fin s→K)
    (h r : ℕ) (U : Submodule K (Fin s→K)) (τ : Fin s→K) : Prop where
  coreRank : r=1 ∨ r=2
  core : U=primitiveBack A b (r-1)
  invariant : U.map (diag (reflectedClock A))≤U
  headMem : τ∈primitiveBack A b r
  headOrthogonal : τ∈annih U
  band : ∀ j, r≤j → j≤h → primitiveBack A b j=
    chain (diag (reflectedClock A)) U τ (j+1-r)
  escapes : h+1-r < (HeadFiber.escapeSites (reflectedClock A) τ U).card

theorem LocalLinearBand.site_count {h r : ℕ} {U : Submodule K (Fin s→K)} {τ : Fin s→K}
    (F : LocalLinearBand A b h r U τ) :
    h+1-r < (weightedSites (reflectedClock A) τ).card := by
  have h := Finset.card_le_card (HeadFiber.escape_le_physical (c:=reflectedClock A) (w:=τ) (U:=U))
  exact F.escapes.trans_le h

theorem LocalLinearBand.local_mem_core {h r : ℕ} {U : Submodule K (Fin s→K)}
    {τ v : Fin s→K} (F : LocalLinearBand A b h r U τ) (le : r≤h)
    (hv : v∈primitiveBack A b h) {y : K}
    (loc : ∀ i,reflectedClock A i≠y → v i=0) : v∈U := by
  rw [F.band h le le_rfl] at hv
  exact HeadFiber.localized_mem F.invariant F.escapes hv loc

variable [LinearOrder K] [IsStrictOrderedRing K]

theorem eq_zero_of_self_row_zero {v : Fin s→K} (h : row v v=0) : v=0 := by
  ext i
  change v i=0
  have e : (∑ j,v j*v j)=0 := h
  have l : v i*v i≤∑ j,v j*v j := by
    exact Finset.single_le_sum (f:=fun j=>v j*v j) (fun j _=>mul_self_nonneg _) (Finset.mem_univ i)
  rw [e] at l
  exact (mul_eq_zero.mp (le_antisymm l (mul_self_nonneg _))).elim id id

theorem dot_orthogonal_inf_bot (U : Submodule K (Fin s→K)) : U⊓annih U=⊥ := by
  apply le_antisymm _ bot_le
  rintro v hv
  obtain ⟨u,a⟩ := Submodule.mem_inf.mp hv
  rw [eq_zero_of_self_row_zero (mem_annih.mp a v u)]
  exact (⊥ : Submodule K (Fin s→K)).zero_mem

theorem dot_orthogonal_sup_top (U : Submodule K (Fin s→K)) : U⊔annih U=⊤ := by
  apply Submodule.eq_of_le_of_finrank_le le_top
  have e := Submodule.finrank_sup_add_finrank_inf_eq U (annih U)
  rw [dot_orthogonal_inf_bot U,finrank_bot,add_zero] at e
  rw [e,finrank_top,finrank_fin_fun]
  simpa only [Fintype.card_fin] using (finrank_annih U).ge

set_option maxHeartbeats 900000 in
theorem local_linear_band_of_paid_ranks {h : ℕ} (h3 : 3≤h)
    (nz : firstSeed A b≠0)
    (tiny : (weightedSites (reflectedClock A) (firstSeed A b)).card≤2)
    (rank : ∀ n≤h,finrank K (primitiveBack A b n)=n+1)
    (escape : ∀ n,2≤n → n≤h →
      ¬(primitiveBack A b n).map (diag (reflectedClock A))≤primitiveBack A b n) :
    ∃ r U τ, LocalLinearBand A b h r U τ := by
  let d := firstSeed A b
  let c := reflectedClock A
  let L := primitiveBack A b
  let m := (weightedSites c d).card
  have dm : d∈L 0 := Submodule.mem_span_singleton_self d
  have mon : Monotone L := monotone_nat_of_le_succ (adjointFlag_le_succ _)
  have shift (j : ℕ) : (L j).map (diag c)≤L (j+1) := adjointFlag_clock _ j
  have first (k : ℕ) : weightedBand c d (k+1)≤L k := by
    simpa only [Nat.zero_add] using weighted_band_of_primitive_seed dm k
  have tight (j : ℕ) (hj : j≤h) : finrank K (L j)=j+1 := rank j hj
  have narrowRankOne : ¬ (L 1).map (diag c)≤L 1 → (L 0).map (diag c)≤L 0 := by
    intro le1
    have m1 : m≤1 := by
      by_contra! bad
      change m≤2 at tiny
      have e : m=2 := by omega
      have fit : weightedBand c d 2=L 1 := by
        apply Submodule.eq_of_le_of_finrank_le (first 1)
        rw [weightedBand_rank c d 2 e.ge,tight 1 (by omega)]
      exact le1 (clock_stable_of_complete_weighted (fit.symm.trans (weightedBand_eq_range c d 2 e.le)))
    have mpos : 1≤m := by
      have a : ∃ i,d i≠0 := by by_contra! h; exact nz (funext h)
      obtain ⟨i,hi⟩ := a
      exact Finset.card_pos.mpr ⟨c i,mem_weightedSites.mpr ⟨i,hi,rfl⟩⟩
    have base : weightedBand c d 1=L 0 := by
      apply Submodule.eq_of_le_of_finrank_le (first 0)
      rw [weightedBand_rank c d 1 mpos,tight 0 (by omega)]
    exact clock_stable_of_complete_weighted (base.symm.trans (weightedBand_eq_range c d 1 m1))
  have frame : ∃r, (r=1∨r=2) ∧ (L (r-1)).map (diag c)≤L (r-1) ∧
      ∀ j,r≤j → j≤h → ¬ (L j).map (diag c)≤L j := by
    by_cases inv : (L 1).map (diag c)≤L 1
    · exact ⟨2,Or.inr rfl,inv,fun j lo hi => escape j lo hi⟩
    · refine ⟨1,Or.inl rfl,narrowRankOne inv,fun j lo hi =>?_⟩
      by_cases e : j=1
      · exact e.symm ▸ inv
      · exact escape j (by omega) hi
  obtain ⟨r,choice,inv,esc⟩ := frame
  let U := L (r-1)
  have re : 1≤r ∧ r≤2 := by rcases choice with e|e <;> omega
  have inU : U≤L r := mon (by omega)
  have ds : finrank K U=r := by
    change finrank K (L (r-1))=r
    rw [tight _ (by omega)]
    omega
  have e : ¬L r≤U := by
    intro sub
    have cost := Submodule.finrank_mono sub
    rw [tight _ (by omega),ds] at cost
    omega
  obtain ⟨w,hw,out⟩ := Set.not_subset.mp e
  have wFull : w∈U⊔annih U := by rw [dot_orthogonal_sup_top]; trivial
  obtain ⟨u,hu,τ,orth,rep⟩ := Submodule.mem_sup.mp wFull
  have tmem : τ∈L r := by
    have h := (L r).sub_mem hw (inU hu)
    rwa [←rep,add_sub_cancel_left] at h
  have tauOut : τ∉U := by
    intro hm
    exact out (rep ▸ U.add_mem hu hm)
  have initial : L r=chain (diag c) U τ 1 := by
    symm
    simp only [chain,pow_zero,Module.End.one_eq_id,LinearMap.id_apply]
    apply Submodule.eq_of_le_of_finrank_le
    · exact sup_le inU ((Submodule.span_singleton_le_iff_mem ..).mpr tmem)
    · rw [Submodule.finrank_sup_span_singleton tauOut,ds,tight _ (by omega)]
  have step (j : ℕ) (lo : r≤j) (hi : j+1≤h) :
      L (j+1)=L j⊔(L j).map (diag c) := by
    symm; apply Submodule.eq_of_le_of_finrank_le (sup_le (mon (Nat.le_succ _)) (shift j))
    have cost := strict_sup_clock_rank (esc j lo (by omega))
    rw [tight _ (by omega)] at cost
    rw [tight _ hi]
    omega
  have expand (k : ℕ) (paid : r+k≤h) : L (r+k)=chain (diag c) U τ (k+1) := by
    induction k with
    | zero => simpa using initial
    | succ k ih =>
      rw [show r+(k+1)=r+k+1 by omega, step _ (by omega) (by omega),
        ih (by omega),clock_chain_next inv (by omega)]
  have exact (j : ℕ) (lo : r≤j) (hi : j≤h) :
      L j=chain (diag c) U τ (j+1-r) := by
    have eq := expand (j-r) (by omega)
    rwa [show r+(j-r)=j by omega,show j-r+1=j+1-r by omega] at eq
  refine ⟨r,U,τ,⟨choice,rfl,inv,tmem,orth,exact,?_⟩⟩
  apply HeadFiber.more_escape_sites inv (by omega)
  rw [←exact h (by omega) le_rfl]
  exact esc h (by omega) le_rfl

end
end RKResearch.Certified.Graded.Reverse
