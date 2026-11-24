module

public import RKCert.ReviewedNative.ERK17TinyHiddenRank
public import RKCert.ReviewedNative.LocalLinearMinimalCharge
public import RKCert.ReviewedNative.LocalLinearUnitFourFeed

@[expose] public section

/-! # Ordinary triple-label saturation of the actual width-26 rank-five band

Source-only. The signed minimum case is paid by the checked generic
local reverse charge, at its actual lower horizon. Exact coverage of the
original rows supplies the same corrected feed as the rank-four branch.
No scalar contradiction or final order-17 stage bound is asserted. -/
namespace RKResearch.Certified.ERK17

open RKResearch Module Polynomial Graded Graded.Reverse Graded.Reverse.LocalLinear
open RKCert.Endpoint RKCert.Endpoint.WeightedClock RKCert.OneEscape
open scoped Classical Matrix
noncomputable section

variable {K : Type*} [Field K] [LinearOrder K] [IsStrictOrderedRing K]
variable {A : Matrix (Fin 26) (Fin 26) K} {b τ : Fin 26 → K}
variable {r : ℕ} {U : Submodule K (Fin 26 → K)}

private theorem local_five_chain_rank_step (C : (Fin 26 → K) →ₗ[K] (Fin 26 → K))
    (J : Submodule K (Fin 26 → K)) (h : Fin 26 → K) (n : ℕ) :
    finrank K (chain C J h (n+1)) ≤ finrank K (chain C J h n)+1 := by
  change finrank K (chain C J h n ⊔ K ∙ (C^n) h : Submodule K (Fin 26 → K)) ≤ _
  have hsum := Submodule.finrank_add_le_finrank_add_finrank (chain C J h n) (K ∙ (C^n) h)
  have one : finrank K (K ∙ (C^n) h) ≤ 1 :=
    (finrank_span_le_card ({(C^n) h} : Set (Fin 26 → K))).trans (by simp)
  omega

/-- The true two-to-four-power continuation charges dimension at E6,
which pays L9 at exactly order 17. -/
theorem width26_rank_five_primitive_nine_cap (ho : HasOrder 17 A b)
    {h : Fin 26 → K} (G : FiveHiddenStaircase A 8 (hiddenKernel b τ U) h)
    (middle : finrank K (zeroSpace A 8) = 9) :
    finrank K (primitiveBack A b 9) ≤ 12 := by
  let J := hiddenKernel b τ U
  let C := diag (nodes A)
  have f6 : zeroSpace A 6 = chain C J h 2 := G.flags 6 (by decide) (by decide)
  have f8 : zeroSpace A 8 = chain C J h 4 := G.midpoint
  have d2 := local_five_chain_rank_step C J h 2
  have d3 := local_five_chain_rank_step C J h 3
  change finrank K (chain C J h 3) ≤ finrank K (chain C J h 2)+1 at d2
  change finrank K (chain C J h 4) ≤ finrank K (chain C J h 3)+1 at d3
  rw [←f6] at d2
  rw [←f8, middle] at d3
  have rich : 7 ≤ finrank K (zeroSpace A 6) := by omega
  have e6 := treeSpace_rank_eq_of_separation ho (q:=6) (by decide)
    (coeff_separated ho (by decide))
  have room := finrank_annih (treeSpace A 6)
  rw [Fintype.card_fin] at room
  have pay := Submodule.finrank_mono (primitiveBack_annih ho 6 9 (by decide))
  omega

/-- Geometric end of the rank-five branch, before the common port mapper.
The head count is an actual weighted-site count on the original reflected
clocks. The feed support equalities are coordinatewise on Fin 26. -/
structure Width26RankFivePhysical (A : Matrix (Fin 26) (Fin 26) K)
    (b τ h e W k θ : Fin 26 → K) (r : ℕ) (U : Submodule K (Fin 26 → K))
    (S Q : K[X]) : Prop where
  staircase : FiveHiddenStaircase A 8 (hiddenKernel b τ U) h
  ninth : zeroSpace A 9 = chain (diag (nodes A)) (hiddenKernel b τ U) h 5
  fit : LocalLinearTraces A b U τ h r 5 S Q
  qLive : Q ≠ 0
  compensation : ∃ u ∈ U, W = weightedEval (reflectedClock A) b Q -
    weightedEval (reflectedClock A) τ S - u
  coreRank : finrank K U = r
  headSites : r + (weightedSites (reflectedClock A) τ).card = 17
  contrastSites : (weightedSites (reflectedClock A) W).card = 4
  mask : e ∈ hiddenKernel b τ U
  originalRows : ∀ i, e i = 1 ∨
    (e i = 0 ∧ h i = Q.eval (reflectedClock A i) ∧ τ i ≠ 0) ∨
    (e i = 0 ∧ h i = 0 ∧ Q.eval (reflectedClock A i) ≠ 0 ∧ W i ≠ 0)
  feed : UnitCleanFourFeed A b τ h W k θ U (Q.comp (1-X))

set_option maxRecDepth 4000
set_option maxHeartbeats 1200000

theorem width26_tiny_rank_five_physical_producer
    (ha : ∀ i j, i ≤ j → A i j = 0) (ho : HasOrder 17 A b)
    (nz : firstSeed A b ≠ 0) (F : LocalLinearBand A b 7 r U τ)
    (full : primitiveBack A b 7 = annih (treeSpace A 8))
    (rank : finrank K (hiddenKernel b τ U) = 5) :
    ∃ (h : Fin 26 → K) (S Q : K[X]) (e W k θ : Fin 26 → K),
      Width26RankFivePhysical A b τ h e W k θ r U S Q := by
  let y := reflectedClock A
  let J := hiddenKernel b τ U
  let n := (weightedSites y τ).card
  change finrank K J = 5 at rank
  have rb : 1 ≤ r ∧ r ≤ 2 := by rcases F.coreRank with z | z <;> omega
  have frame := (ordered_width26_full_frame ha ho).1
  obtain ⟨dr, eqr⟩ := frame.reverse.flagExact (r-1) (by omega)
  have ur : finrank K U = r := by
    rw [F.core, ←eqr, dr, first_dim_one nz]
    omega
  have n0 : 9 ≤ r+n := by
    have f := F.site_count
    change 7+1-r < n at f
    omega
  obtain ⟨h, G, ninth⟩ := width26_tiny_rank_five_head ha ho nz F full rank
  obtain ⟨S, Q, fit⟩ := local_linear_two_traces ho F full (by decide)
    (by omega) G.headGrade
  have qLive : Q ≠ 0 := fun qz =>
    G.outside (LocalLinearTraces.mem_hidden_of_q_zero F fit qz)
  obtain ⟨e, eK, binary, off⟩ := hiddenKernel_support_unit b τ U
  obtain ⟨W, Worth, Wrows, u, hu, comp⟩ := local_linear_compensated_contrast F fit eK binary
  let t := (weightedSites y W).card
  have t4 : 4 ≤ t := local_linear_contrast_site_floor ho F full (by decide) (by decide)
    qLive fit.qDeg fit.pDeg hu comp
  have Uin : U ≤ annih (treeSpace A 8) := by
    rw [F.core]
    exact primitiveBack_annih ho 8 (r-1) (by omega)
  have mass (v : Fin 26 → K) (hv : v ∈ U) : ∑ i, v i = 0 := by
    have test := mem_annih.mp (Uin hv) _ (one_mem_treeSpace A 8)
    simpa only [row_apply, dotProduct, Pi.one_apply, mul_one] using test
  have Jorth : J ≤ annih U := by
    intro x hx
    apply mem_annih.mpr
    intro v hv
    have x8 : x ∈ zeroSpace A 8 := zeroSpace_mono A (by decide : 6 ≤ 8) (G.inside hx)
    have test := mem_annih.mp (Uin hv) _ (zeroSpace_le_treeSpace A 8 x8)
    rw [row_apply, dotProduct_comm, ←row_apply] at test
    exact test
  have tauRows (i : Fin 26) (hi : τ i ≠ 0) : e i = 0 ∧ h i = Q.eval (y i) := by
    have e0 : τ i * e i = 0 := congrFun (mem_hiddenKernel.mp eK).1 i
    have tr := congrFun fit.tauTrace i
    simp only [Pi.mul_apply, weightedEval_apply] at tr
    change τ i * h i = Q.eval (y i) * τ i at tr
    have hz : τ i * (h i - Q.eval (y i)) = 0 := by linear_combination tr
    exact ⟨(mul_eq_zero.mp e0).resolve_left hi,
      sub_eq_zero.mp ((mul_eq_zero.mp hz).resolve_left hi)⟩
  have C : JointBandCensus y h e τ W Q U J := by
    refine ⟨binary, off, tauRows, Wrows, Jorth, F.headOrthogonal, Worth, F.invariant, ?_⟩
    exact triple_indicator_mem_annih F.invariant fit.preserves
      (mem_hiddenKernel.mp eK).2.2 mass
  have ord := C.ordinary_rank
  change finrank K U + finrank K J + n + t ≤ 26 at ord
  rw [ur, rank] at ord
  have long : 17 ≤ r+n := by
    by_contra! short
    have pay : (weightedSites (reflectedClock A) τ).card+r+1 ≤ 17 := by
      change n+r+1 ≤ 17
      omega
    have cancel := reflected_clockMass_zero_of_paid_band ho F.headMem pay
    have collapsed := C.cancelled_rank cancel
    change finrank K U + finrank K J + 2*n + t ≤ 26 at collapsed
    rw [ur, rank] at collapsed
    have minimum : r+n = 9 := by rcases F.coreRank with z | z <;> omega
    have gain := local_linear_minimal_sites_paid_gain ha ho F ur minimum (by decide) 4 (by decide)
    change 13 ≤ finrank K (primitiveBack A b 9) at gain
    have cap := width26_rank_five_primitive_nine_cap ho G frame.middleDefects
    omega
  have counts : r+n = 17 ∧ t = 4 := ⟨by omega, by omega⟩
  have fill : 26 ≤ finrank K U + finrank K J + (weightedSites y τ).card +
      (weightedSites y W).card := by
    change 26 ≤ finrank K U + finrank K J + n + t
    rw [ur, rank]
    have a := counts.1
    have b' := counts.2
    omega
  have cover := C.physical_live_cover fill
  have outside (i : Fin 26) (ei : e i = 0) (bad : h i ≠ Q.eval (y i)) : W i ≠ 0 := by
    rcases cover i with core | ⟨_, profile, _⟩ | ⟨_, _, _, live⟩
    · exact (zero_ne_one (ei.symm.trans core)).elim
    · exact (bad profile).elim
    · exact live
  have Wclean (i : Fin 26) (wi : W i ≠ 0) (v : Fin 26 → K) (hv : v ∈ zeroSpace A 9) :
      v i = 0 := by
    have ⟨ei, h0, _⟩ := Wrows i wi
    rw [ninth] at hv
    obtain ⟨v0, hv0, R, _, repr⟩ := HeadFiber.exists_poly hv
    rw [repr]
    simp only [Pi.add_apply, off v0 hv0 i ei, weightedEval_apply, h0, mul_zero, zero_add]
  obtain ⟨k, θ, feed⟩ := unit_clean_four_feed_of_live_cover
    (hiddenKernel_forward_clock_of_band F) G.headGrade fit.preserves eK binary
    (fun i live => (tauRows i live).2) Wrows outside counts.2 qLive fit.qDeg Wclean
  exact ⟨h, S, Q, e, W, k, θ, ⟨G, ninth, fit, qLive, ⟨u, hu, comp⟩, ur,
    counts.1, counts.2, eK, cover, feed⟩⟩

end
end RKResearch.Certified.ERK17
