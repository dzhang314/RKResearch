module

public import RKCert.ReviewedNative.FirstSeedWideCensus

@[expose] public section

/-! # Unmarked signed four ports and the exact first-seed F9 step

The primitive acts on the original stage source, with no allowance for
an unobserved terminal coordinate. The extra paid primitive window is
degree three rather than the marked quadratic branch's degree two. -/
namespace RKResearch.Certified.ERK17
open RKResearch Module Polynomial RKCert.Endpoint RKCert.Endpoint.WeightedClock
open RKResearch.Certified.Graded RKResearch.Certified.Graded.Reverse
open RKResearch.Certified.Graded.Reverse.FirstWide
open RKCert.OneEscape
open scoped Classical Matrix
noncomputable section

variable {K : Type*} [Field K]

structure UnitPhysicalFourPort {s : ℕ} (A : Matrix (Fin (s+1)) (Fin (s+1)) K)
    (W θ : Fin (s+1)→K) (P : K[X]) : Prop where
  nonzero : P≠0
  degree : P.natDegree≤5
  sites : (weightedSites (nodes A) θ).card=4
  measured : ∀ i, W i≠0 → θ i=P.eval (nodes A i) ∧ θ i≠0
  inactive : ∀ i, W i=0 → θ i=0
  initial : θ 0=0 → P.eval 0=0
  quadrature : ∀ R : K[X], R.natDegree≤11 →
    (∑ i,weightedEval (nodes A) W R i)=(RKResearch.Certified.Graded.primitive (R*P)).eval 1
  primitive : ∀ R : K[X], R.natDegree≤3 → ∀ i, θ i≠0 →
    mat A (weightedEval (nodes A) θ R) i=(RKResearch.Certified.Graded.primitive (R*P)).eval (nodes A i)

theorem UnitPhysicalFourPort.primitive_zero_of_prefix {s : ℕ}
    {A : Matrix (Fin (s+1)) (Fin (s+1)) K} {W θ : Fin (s+1)→K} {P : K[X]}
    (B : UnitPhysicalFourPort A W θ P) (ha : ∀ i j, i≤j → A i j=0)
    {i : Fin (s+1)} (active : θ i≠0) (R : K[X]) (deg : R.natDegree≤3)
    (stop : ∀ j, j < i → θ j≠0 → R.eval (nodes A j)=0) :
    (RKResearch.Certified.Graded.primitive (R*P)).eval (nodes A i)=0 := by
  rw [←B.primitive R deg i active]
  apply causal_mat ha i
  intro j hj
  rw [weightedEval_apply]
  by_cases hs : θ j=0
  · rw [hs,mul_zero]
  · rw [stop j hj hs,zero_mul]

theorem unit_origin_clock_zero {s : ℕ} {A : Matrix (Fin (s+1)) (Fin (s+1)) K}
    (ha : ∀ i j, i≤j → A i j=0) : nodes A 0=0 := by
  change (∑ j,A 0 j*(1:K))=0
  exact Finset.sum_eq_zero fun j _ => by rw [ha 0 j (Fin.zero_le _),zero_mul]

variable [LinearOrder K] [IsStrictOrderedRing K]
variable {A : Matrix (Fin 26) (Fin 26) K} {b : Fin 26→K}

set_option maxRecDepth 3500 in
set_option maxHeartbeats 650000 in
theorem WideLinear.forward_nine_head (B : WideLinear A b)
    (ha : ∀ i j, i≤j → A i j=0) (ho : HasOrder 17 A b)
    (S : OddBalancedFrame A b 8 2) (nz : firstSeed A b≠0) :
    ∃ h : Fin 26→K,
      h∈zeroSpace A 5 ∧ h∉FirstWide.carrier A b ∧
      FirstWide.carrier A b≤zeroSpace A 6 ∧
      zeroSpace A 9=chain (diag (nodes A)) (FirstWide.carrier A b) h 5 := by
  let H := FirstWide.carrier A b
  let C := diag (nodes A)
  have cap : finrank K (zeroSpace A 9)≤10 := by
    have e := S.nextRoom
    change finrank K (zeroSpace A 9)+finrank K (back A b 0)≤11 at e
    rw [first_dim_one nz] at e
    omega
  have rk : finrank K H=5 := B.carrier_rank_five ha ho S
  have h8 : H≤zeroSpace A 8 := B.firstCover.carrier_pure ho (by decide)
  have inv : H.map C≤H := FirstWide.carrier_clock
  obtain ⟨h,F⟩ := five_hidden_staircase ha (by decide) S.separated S.middleDefects
    (cap.trans (by decide)) rk h8 inv
  have r8 : finrank K (zeroSpace A 8)=9 := S.middleDefects
  have ps := PolySeparated.of_coeff S.separated
  have notInv : ¬(zeroSpace A 8).map C≤zeroSpace A 8 := by
    intro stable
    have e := clock_invariant_outgoing ha ps (U:=zeroSpace A 8) le_rfl stable
    change finrank K (zeroSpace A 8)+4≤finrank K (zeroSpace A 9) at e
    omega
  have room : finrank K (zeroSpace A (8+1))≤finrank K (zeroSpace A 8)+1 := by
    change finrank K (zeroSpace A 9)≤finrank K (zeroSpace A 8)+1
    omega
  have e := zeroSpace_clock_step_of_unit (n:=8) room notInv
  have h8' : zeroSpace A 8=chain C H h 4 := F.midpoint
  change zeroSpace A 9=zeroSpace A 8⊔(zeroSpace A 8).map C at e
  rw [h8',clock_chain_next inv (by decide : 0<4)] at e
  exact ⟨h,F.headGrade,F.outside,F.inside,e⟩

end
end RKResearch.Certified.ERK17
