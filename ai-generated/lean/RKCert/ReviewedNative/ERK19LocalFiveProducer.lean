module

public import RKCert.ReviewedNative.LocalLinearJointBands
public import RKCert.ReviewedNative.ERK19LocalFiveThinCharge
public import RKCert.ReviewedNative.ERK19LocalFiveSaturation

@[expose] public section

/-! Draft only: exact saturation producer for the localized **nonzero**
order-19 branch. The two disjoint-rank charges derive, rather than assume,
the original physical support cover. -/
namespace RKResearch.Certified.ERK19
open RKResearch Module Polynomial Graded Graded.Reverse Graded.Reverse.LocalLinear
open RKCert.Endpoint RKCert.Endpoint.WeightedClock
open scoped Classical
noncomputable section

variable {K : Type*} [Field K] [LinearOrder K] [IsStrictOrderedRing K]
variable {A : Matrix (Fin 29) (Fin 29) K} {b : Fin 29→K}
variable {r : ℕ} {U : Submodule K (Fin 29→K)} {τ h : Fin 29→K} {P Q : K[X]}

set_option maxHeartbeats 1050000 in
theorem width29_local_five_cover_premises
    (ha : ∀ i j,i≤j→A i j=0) (ho : HasOrder 19 A b) (nz : firstSeed A b≠0)
    (F : LocalLinearBand A b 8 r U τ) (full : primitiveBack A b 8=annih (treeSpace A 9))
    (rank : finrank K (hiddenKernel b τ U)=5) (G : LocalFiveGeometry A b r U τ h P Q) :
    ∃ e W, LocalFiveCoverPremises A b U τ h e W Q := by
  let y := reflectedClock A
  let J := hiddenKernel b τ U
  let n := (weightedSites y τ).card
  have rb : 1≤r ∧ r≤2 := by rcases F.coreRank with e|e <;> omega
  have H := (ordered_width29_frame ha ho).1
  obtain ⟨d,eq⟩ := H.reverse.flagExact (r-1) (by omega)
  have ur : finrank K U=r := by rw [F.core,←eq,d,first_dim_one nz]; omega
  have low : 10≤r+n := by
    have sites := F.site_count
    change 8+1-r<n at sites
    omega
  obtain ⟨e,eK,bin,off⟩ := hiddenKernel_support_unit b τ U
  obtain ⟨W,Worth,Wrows,v,vU,fit⟩ := local_linear_compensated_contrast F G.fit eK bin
  let t := (weightedSites y W).card
  have t5 : 5≤t := local_linear_contrast_site_floor ho F full (by decide) (by decide)
    G.nonzeroHead G.fit.qDeg G.fit.pDeg vU fit
  have reverseMono : Monotone (primitiveBack A b) :=
    monotone_nat_of_le_succ (adjointFlag_le_succ _)
  have Uin : U≤annih (treeSpace A 9) := (F.core.le.trans
    (reverseMono (show r-1≤8 by omega))).trans full.le
  have mass (v : Fin 29→K) (hv : v∈U) : ∑ i,v i=0 := by
    have a := mem_annih.mp (Uin hv) _ (one_mem_treeSpace A 9)
    simpa only [row_apply,dotProduct,Pi.one_apply,mul_one] using a
  have Jorth : J≤annih U := by
    intro x hx
    apply mem_annih.mpr
    intro u hu
    have k := mem_annih.mp (Uin hu) _
      (zeroSpace_le_treeSpace A 9 (hiddenKernel_le_midpoint ho F full hx))
    rw [row_apply,dotProduct_comm,←row_apply]
    exact k
  have tauRows (i : Fin 29) (hi : τ i≠0) : e i=0 ∧ h i=Q.eval (y i) := by
    have e0 : τ i*e i=0 := congrFun (mem_hiddenKernel.mp eK).1 i
    have raw := congrFun G.fit.tauTrace i
    simp only [Pi.mul_apply,weightedEval_apply] at raw
    change τ i*h i=Q.eval (y i)*τ i at raw
    have hz : τ i*(h i-Q.eval (y i))=0 := by linear_combination raw
    exact ⟨(mul_eq_zero.mp e0).resolve_left hi,
      sub_eq_zero.mp ((mul_eq_zero.mp hz).resolve_left hi)⟩
  have C : JointBandCensus y h e τ W Q U J := by
    refine ⟨bin,off,tauRows,Wrows,Jorth,F.headOrthogonal,Worth,F.invariant,?_⟩
    exact triple_indicator_mem_annih F.invariant G.fit.preserves (mem_hiddenKernel.mp eK).2.2 mass
  change finrank K J=5 at rank
  have ordinary := C.ordinary_rank
  change finrank K U+finrank K J+n+t≤29 at ordinary
  rw [ur,rank] at ordinary
  have large : 19≤r+n := by
    by_contra! small
    have cancel := reflected_clockMass_zero_of_paid_band ho F.headMem (by change n+r+1≤19; omega)
    have extra := C.cancelled_rank cancel
    change finrank K U+finrank K J+2*n+t≤29 at extra
    rw [ur,rank] at extra
    have minSites : r+n=10 := by rcases F.coreRank with er|er <;> omega
    exact width29_local_five_minimal_reverse_sites_impossible ha ho nz F G minSites
  have saturated : r+n=19 ∧ t=5 := by omega
  have fill : 29≤finrank K U+finrank K J+(weightedSites y τ).card+(weightedSites y W).card := by
    change 29≤finrank K U+finrank K J+n+t
    rw [ur,rank]
    have a := saturated.1
    have b := saturated.2
    omega
  have physical := C.physical_cover fill
  exact ⟨e,W,⟨eK,bin,off,physical,Wrows,t5⟩⟩

end
end RKResearch.Certified.ERK19
