module

public import RKCert.ReviewedNative.ERK17LocalFourAdvance
public import RKCert.ReviewedNative.LocalLinearOneClockRefinement

@[expose] public section

/-! # Sixteen actual refined head labels at width 26 -/
namespace RKResearch.Certified.ERK17

open RKResearch Module Polynomial Graded Graded.Reverse Graded.Reverse.LocalLinear
open RKCert.Endpoint RKCert.Endpoint.WeightedClock PhysicalCensus
open scoped Classical Matrix BigOperators
noncomputable section

variable {K : Type*} [Field K] [LinearOrder K] [IsStrictOrderedRing K]
variable {A : Matrix (Fin 26) (Fin 26) K} {b τ h ξ e W : Fin 26 → K}
variable {U : Submodule K (Fin 26 → K)} {P Q : K[X]}

set_option maxRecDepth 4500
set_option maxHeartbeats 1800000

private theorem paid_reflected_moment {v : Fin 26 → K} {j : ℕ}
    (paid : v ∈ annih (treeSpace A j)) (R : K[X]) (rd : R.natDegree ≤ j) :
    (∑ i, v i*R.eval (reflectedClock A i)) = 0 := by
  let H := R.comp (1-X)
  have hd : H.natDegree ≤ j := natDegree_comp_le.trans (by
    rw [Thin.one_sub_X_natDegree,mul_one]
    exact rd)
  have z := mem_annih.mp paid _ (evalNodes_mem_treeSpace A H hd)
  simpa only [row_apply,dotProduct,evalNodes_apply,H,eval_comp,eval_sub,eval_one,
    eval_X,reflectedClock,Pi.sub_apply,Pi.one_apply] using z

private def massZero (K : Type*) [Field K] : Submodule K (Fin 26 → K) :=
  annih (Submodule.span K ({1} : Set (Fin 26 → K)))

private theorem mem_massZero {v : Fin 26 → K} :
    v ∈ massZero K ↔ (∑ i,v i) = 0 := by
  constructor
  · intro z
    have hm : (1 : Fin 26 → K) ∈ Submodule.span K ({1} : Set (Fin 26 → K)) :=
      Submodule.subset_span (Set.mem_singleton _)
    have test := mem_annih.mp z _ hm
    simpa only [row_apply,dotProduct,Pi.one_apply,mul_one] using test
  · intro zero
    apply mem_annih.mpr
    intro x hx
    obtain ⟨a,rfl⟩ := Submodule.mem_span_singleton.mp hx
    simp only [row_apply,dotProduct,Pi.smul_apply,Pi.one_apply,smul_eq_mul,mul_one]
    rw [←Finset.sum_mul,zero,zero_mul]

private theorem weighted_mem_massZero (y v : Fin 26 → K) (R : K[X]) :
    weightedEval y v R ∈ massZero K ↔ (∑ i, v i*R.eval (y i)) = 0 := by
  rw [mem_massZero]
  simp only [weightedEval_apply,mul_comm]

private theorem masses_zero_from_count {y v : Fin 26 → K} {d : ℕ}
    (tests : ∀ R : K[X], R.natDegree ≤ d → (∑ i,v i*R.eval (y i)) = 0)
    (small : (weightedSites y v).card ≤ d+1) :
    ∀ a, clockMass y v a = 0 := by
  apply clock_masses_zero_of_significant_sites tests
  apply le_trans (b := (weightedSites y v).card) _ small
  apply Finset.card_le_card
  intro a ha
  letI : DecidableEq K := Classical.decEq K
  exact (Finset.mem_filter.mp ha).1

theorem width26_local_four_refined_head_count
    (ha : ∀ i j,i ≤ j → A i j = 0) (ho : HasOrder 17 A b) (nz : firstSeed A b ≠ 0)
    (F : LocalLinearBand A b 7 2 U τ) (full : primitiveBack A b 7 = annih (treeSpace A 8))
    (D : LocalFourAxes A b τ h ξ U) (trace : LocalLinearTraces A b U τ h 2 5 P Q)
    (C : JointBandCensus (reflectedClock A) h e τ W Q U (hiddenKernel b τ U))
    (ur : finrank K U = 2) (jr : finrank K (hiddenKernel b τ U) = 4)
    (rich : 7 ≤ finrank K (zeroSpace A 6))
    (w4 : 4 ≤ (weightedSites (reflectedClock A) W).card) :
    16 ≤ (activeLabels (jointClock (reflectedClock A) ξ) τ).card := by
  let y := reflectedClock A
  let n := (weightedSites y τ).card
  let t := (weightedSites y W).card
  let M := annih (treeSpace A 7)
  have n8 := width26_local_four_tau_at_least_eight ha ho nz F rich
  change 8 ≤ n at n8
  change 4 ≤ t at w4
  by_contra! tooFew
  change (activeLabels (jointClock y ξ) τ).card < 16 at tooFew
  have leJ := ordinary_le_joint_clock_labels y ξ τ
  have n15 : n ≤ 15 := by change n ≤ _ at leJ; omega
  have base (R : K[X]) (rd : R.natDegree ≤ 13) : (∑ i, τ i*R.eval (y i))=0 :=
    paid_reflected_moment (primitiveBack_annih ho 13 2 (by decide) F.headMem) R rd
  have lower (R : K[X]) (rd : R.natDegree ≤ 6) : weightedEval y τ R ∈ M :=
    local_four_low_head_paid_E7 ho F R rd
  have count8 (zeros : ∀ a, clockMass y τ a = 0) : n = 8 := by
    have count := C.cancelled_rank zeros
    change finrank K U+finrank K (hiddenKernel b τ U)+2*n+t≤26 at count
    omega
  have total {v : Fin 26 → K} (vp : v ∈ M) : (∑ i, v i)=0 := by
    simpa only [eval_one,mul_one] using paid_reflected_moment vp (1 : K[X]) (by simp)
  have noOrbit (v : Fin 26 → K) (v8 : 8 ≤ (weightedSites y v).card)
      (orth : v ∈ annih U) (paid : completeOrbit y v ≤ M) : False :=
    width26_rank_four_no_paid_complete_orbit ha ho nz F rich v
      (show 7 ≤ (weightedSites y v).card from (by decide : 7 ≤ 8).trans v8) orth paid
  have finitePaid (pay : ∀ R : K[X], R.natDegree ≤ 7 → weightedEval y τ R ∈ M)
      (nsmall : n = 8) : False := by
    apply noOrbit τ n8 F.headOrthogonal
    exact completeOrbit_le_of_paid_tests (d:=7) (by change n ≤ 7+1; omega) pay
  rcases width26_local_four_actual_advance ha ho F full D trace with paid | ⟨a,δ,v,L⟩ | ⟨a,v,L⟩
  · have top14 : (∑ i, τ i*((X : K[X])^14).eval (y i)) = 0 := by
      have z := paid_reflected_moment (paid (X^7) (by simp)) (X^7) (by simp)
      convert z using 1
      apply Finset.sum_congr rfl
      intro i _
      simp only [weightedEval_apply,eval_pow,eval_X]
      change τ i*y i^14 = (y i^7*τ i)*y i^7
      rw [show 14=7+7 by decide,pow_add]
      ring
    have lifted := weighted_tests_one_more_of_top (y:=y) (w:=τ) (M:=massZero K) (d:=13)
      (fun R rd => (weighted_mem_massZero y τ R).mpr (base R rd))
      (Q:=X^14) (by simp) ((weighted_mem_massZero y τ _).mpr top14)
    have zeros := masses_zero_from_count (d:=14)
      (fun R rd => (weighted_mem_massZero y τ R).mp (lifted R rd)) n15
    exact finitePaid paid (count8 zeros)
  · have limit : a ∈ weightedSites y τ := by
      have hv : ∃ i, v i ≠ 0 := by by_contra! bad; exact L.live (funext bad)
      obtain ⟨i,vi⟩ := hv
      have ia : y i=a := by by_contra no; exact vi (L.off i no)
      have ti : τ i≠0 := by intro z; exact vi (by rw [L.fit i ia,z,zero_mul])
      exact mem_weightedSites.mpr ⟨i,ti,ia⟩
    have noCancelled (zeros : ∀ x, clockMass y τ x = 0) : False := by
      have few := count8 zeros
      by_cases orbit : v ∈ completeOrbit y τ
      · obtain ⟨R,dR,tR⟩ := weighted_top_of_local_orbit_mode L.live L.off orbit L.paid
        have r7 : R.natDegree = 6+1 := by change R.natDegree=n-1 at dR; omega
        exact finitePaid (weighted_tests_one_more_of_top lower r7 tR) few
      · have on (i : Fin 26) (vi : v i≠0) :
          tripleLabel y h e i ∈ tauLabels Q (weightedSites y τ) := by
          have ia : y i=a := by by_contra no; exact vi (L.off i no)
          have ti : τ i≠0 := by intro z; exact vi (by rw [L.fit i ia,z,zero_mul])
          exact ⟨(C.tauRows i ti).1,(C.tauRows i ti).2,mem_weightedSites.mpr ⟨i,ti,rfl⟩⟩
        have bound := C.cancelled_rank_with_silent_extra zeros L.orthogonal on
          (clockMass_zero_of_local_total a L.off (total L.paid)) orbit
        change finrank K U+finrank K (hiddenKernel b τ U)+2*n+1+t≤26 at bound
        omega
    by_cases short : n ≤ 14
    · exact noCancelled (masses_zero_from_count (d:=13) base short)
    by_cases noMass : clockMass y τ a = 0
    · have small : ((weightedSites y τ).filter fun x => clockMass y τ x≠0).card ≤ 13+1 := by
        have sub : (weightedSites y τ).filter (fun x => clockMass y τ x≠0) ⊆
            (weightedSites y τ).erase a := by
          intro x hx
          obtain ⟨on,live⟩ := Finset.mem_filter.mp hx
          exact Finset.mem_erase.mpr ⟨fun eq => live (eq.symm ▸ noMass),on⟩
        have size := Finset.card_le_card sub
        rw [Finset.card_erase_of_mem limit] at size
        change _ ≤ n-1 at size
        omega
      apply noCancelled
      apply clock_masses_zero_of_significant_sites base
      convert small using 1
      congr
    obtain ⟨i,j,ti,tj,ia,ja,diff⟩ :=
      actual_axis_split_of_silent_local_mode δ L.live L.off L.fit (total L.paid) noMass
    have split := ordinary_lt_joint_clock_labels_of_split ti tj ia ja diff
    change n < (activeLabels (jointClock y ξ) τ).card at split
    omega
  · have equal := live_weights_of_advance L.step L.atKnot
    have advance7 := weighted_tests_one_more_of_linear_advance a L.paid L.step lower
    have tests14 := weighted_tests_one_more_of_linear_advance (d:=13) a
      (mem_massZero.mpr (total L.paid)) L.step
      (fun R rd => (weighted_mem_massZero y τ R).mpr (base R rd))
    have small : (weightedSites y v).card ≤ 14+1 := by rw [equal]; exact n15
    have quiet := masses_zero_from_count (d:=14)
      (fun R rd => (weighted_mem_massZero y v R).mp (tests14 R rd)) small
    have zeros (x : K) : clockMass y τ x=0 := by
      rw [clockMass_of_clock_multiple (fun k => k-a) x (fun i => (L.step i).symm),quiet x,mul_zero]
    have eight := count8 zeros
    apply noOrbit v (by rw [equal]; exact n8) L.orthogonal
    exact completeOrbit_le_of_paid_tests (d:=7) (by rw [equal]; change n≤7+1; omega) advance7

end
end RKResearch.Certified.ERK17
