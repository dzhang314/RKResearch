module

public import RKCert.ReviewedNative.ERK17LocalFourRefinedCount
public import RKCert.ReviewedNative.ERK17LocalFourContrast
public import RKCert.ReviewedNative.LocalLinearUnitFourFeed

@[expose] public section

/-! # Actual rank-four support saturation at width 26

The refined labels earn an all-row cover, removing any hypothetical
zero-amplitude leftover. No scalar endpoint is consumed here. -/
namespace RKResearch.Certified.ERK17

open RKResearch Module Polynomial Graded Graded.Reverse Graded.Reverse.LocalLinear
open RKCert.Endpoint RKCert.Endpoint.WeightedClock PhysicalCensus
open scoped Classical Matrix BigOperators
noncomputable section

variable {K : Type*} [Field K] [LinearOrder K] [IsStrictOrderedRing K]
variable {A : Matrix (Fin 26) (Fin 26) K} {b τ : Fin 26 → K}
variable {r : ℕ} {U : Submodule K (Fin 26 → K)}

structure Width26RankFourPhysical (A : Matrix (Fin 26) (Fin 26) K)
    (b τ h ξ e W k θ : Fin 26 → K) (U : Submodule K (Fin 26 → K))
    (S Q : K[X]) : Prop where
  trace : LocalLinearTraces A b U τ h 2 5 S Q
  compensation : ∃ u ∈ U, W = weightedEval (reflectedClock A) b Q -
    weightedEval (reflectedClock A) τ S-u
  coreInside : hiddenKernel b τ U ≤ zeroSpace A 5
  rankHead : (activeLabels (jointClock (reflectedClock A) ξ) τ).card = 16
  rankContrast : (weightedSites (reflectedClock A) W).card = 4
  originalRows : ∀ i, e i = 1 ∨
    (e i = 0 ∧ h i = Q.eval (reflectedClock A i) ∧ τ i ≠ 0) ∨
    (e i = 0 ∧ h i = 0 ∧ ξ i = 0 ∧ Q.eval (reflectedClock A i) ≠ 0 ∧ W i ≠ 0)
  feed : UnitCleanFourFeed A b τ h W k θ U (Q.comp (1-X))

set_option maxRecDepth 4500
set_option maxHeartbeats 1800000

theorem width26_tiny_rank_four_physical_producer
    (ha : ∀ i j, i ≤ j → A i j = 0) (ho : HasOrder 17 A b)
    (nz : firstSeed A b ≠ 0) (F : LocalLinearBand A b 7 r U τ)
    (full : primitiveBack A b 7 = annih (treeSpace A 8))
    (rank : finrank K (hiddenKernel b τ U) = 4) :
    ∃ (h ξ : Fin 26 → K) (S Q : K[X]) (e W k θ : Fin 26 → K),
      Width26RankFourPhysical A b τ h ξ e W k θ U S Q := by
  obtain ⟨r2, inside, rich⟩ := width26_tiny_rank_four_refinement ha ho nz F full rank
  subst r
  obtain ⟨h,ξ,D⟩ := width26_tiny_rank_four_axes ha ho nz F full rank
  obtain ⟨S,Q,e,W,G⟩ := width26_local_four_census_inputs ha ho nz F full D
  let y := reflectedClock A
  let J := hiddenKernel b τ U
  have Wrows (i : Fin 26) (wi : W i ≠ 0) :
      e i=0 ∧ h i=0 ∧ Q.eval (y i)≠0 :=
    ⟨(G.contrastRows i wi).1,(G.contrastRows i wi).2.1,(G.contrastRows i wi).2.2.2⟩
  have marked : U.map (diag e) ≤ U := (mem_hiddenKernel.mp G.unit).2.2
  have C : JointBandCensus y h e τ W Q U J := by
    refine ⟨G.binary,G.kernelOff,G.tauRows,Wrows,G.kernelOrthogonal,F.headOrthogonal,
      G.contrastOrthogonal,F.invariant,?_⟩
    exact triple_indicator_mem_annih F.invariant G.trace.preserves marked G.coreMass
  have R : RefinedJointBandCensus y h ξ e τ W Q U J :=
    ⟨C,G.trace.preserves,D.axisPreserves,marked,fun i wi => (G.contrastRows i wi).2.2.1,G.coreMass⟩
  have sixteen := width26_local_four_refined_head_count ha ho nz F full D G.trace C
    G.coreRank rank rich.ge G.contrastCount
  have cap := R.rank
  rw [G.coreRank,show finrank K J=4 from rank] at cap
  have head : (activeLabels (jointClock y ξ) τ).card=16 := by
    have four := G.contrastCount
    change 4 ≤ (weightedSites y W).card at four
    change 16 ≤ (activeLabels (jointClock y ξ) τ).card at sixteen
    omega
  have four : (weightedSites y W).card=4 := by
    have low := G.contrastCount
    change 4 ≤ (weightedSites y W).card at low
    omega
  have cover := R.physical_live_cover (by rw [G.coreRank,show finrank K J=4 from rank,head,four])
  have outside (i : Fin 26) (ei : e i=0) (bad : h i≠Q.eval (y i)) : W i≠0 := by
    rcases cover i with e1 | on | contrast
    · exact (zero_ne_one (ei.symm.trans e1)).elim
    · exact (bad on.2.1).elim
    · exact contrast.2.2.2.2
  obtain ⟨k,θ,feed⟩ := unit_clean_four_feed_of_live_cover
    (hiddenKernel_forward_clock_of_band F) D.fifth G.trace.preserves G.unit G.binary
    (fun i live => (G.tauRows i live).2) Wrows outside four G.live G.trace.qDeg G.cleanRows
  exact ⟨h,ξ,S,Q,e,W,k,θ,⟨G.trace,G.compensated,inside,head,four,cover,feed⟩⟩

end
end RKResearch.Certified.ERK17
