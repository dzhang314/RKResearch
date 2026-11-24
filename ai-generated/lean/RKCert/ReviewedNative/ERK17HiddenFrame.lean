module

public import RKCert.ReviewedNative.NativeHiddenCarrier
public import RKCert.ReviewedNative.ReversePhysicalPorts
public import RKCert.ReviewedNative.ForwardInvariantCap
public import RKCert.ReviewedNative.ERK17QuadraticCover

@[expose] public section

/-! # The true width-26 grade-four hidden kernel and its upper rank -/
namespace RKResearch.Certified.ERK17
open RKResearch Module Polynomial
open RKResearch.Certified.Graded RKResearch.Certified.Graded.Reverse
open RKCert.Endpoint RKCert.Endpoint.WeightedClock
open scoped Classical

noncomputable section
variable {K : Type*} [Field K]
variable {A : Matrix (Fin 26) (Fin 26) K} {b : Fin 26→K}

abbrev hiddenCarrier (A : Matrix (Fin 26) (Fin 26) K) (b : Fin 26→K) :=
    Hidden.carrier (nodes A) b (quadraticSeed A b) 0 (Fin.last 25)

def visible (A : Matrix (Fin 26) (Fin 26) K) (b : Fin 26→K) (i : Fin 26) : Prop :=
    quadraticSeed A b i≠0 ∨ reflectedClock A i*b i≠0

structure HiddenFrame (A : Matrix (Fin 26) (Fin 26) K) (b : Fin 26→K) : Prop where
  fromFour : zeroSpace A 4≤hiddenCarrier A b
  toEight : hiddenCarrier A b≤zeroSpace A 8
  stable : (hiddenCarrier A b).map (diag (nodes A))≤hiddenCarrier A b
  rankCap : finrank K (hiddenCarrier A b)≤5
  invisible : ∀ v∈hiddenCarrier A b, ∀ i, visible A b i → v i=0
  detected : ∀ v∈zeroSpace A 8, (∀i,visible A b i→v i=0) → v∈hiddenCarrier A b

theorem Width26QuadraticCover.pointwise (C : Width26QuadraticCover A b) :
    ∀ v∈zeroAt (annih (treeSpace A 8)) (Fin.last 25),
      ∃ P : K[X], P.natDegree≤6 ∧ weightedEval (reflectedClock A) (quadraticSeed A b) P=v := by
  intro v hv
  obtain ⟨h,t⟩ := mem_zeroAt.mp hv
  exact C.poly_cover h t

set_option maxHeartbeats 650000 in
theorem width26_hidden_frame [LinearOrder K] [IsStrictOrderedRing K]
    (ha : ∀ i j, i≤j → A i j=0) (ho : HasOrder 17 A b)
    (F : OddBalancedFrame A b 8 2) (C : Width26QuadraticCover A b) :
    HiddenFrame A b := by
  let t := Fin.last 25
  have y0 : reflectedClock A t=0 := by change 1-nodes A t=0; rw [C.lastClock,sub_self]
  have col (k : Fin 26) : A k t=0 := ha k t (Fin.le_last k)
  have supp : Thin.SupportsComplement A b 8 t := Thin.supportsComplement_of_cover C.pointwise
  have H8 : hiddenCarrier A b≤zeroSpace A 8 :=
    Hidden.carrier_le_defects ha ho (by decide) C.lastClock C.lastLive.live C.lastSeed supp
  have inv : (hiddenCarrier A b).map (diag (nodes A))≤hiddenCarrier A b :=
    Hidden.carrier_invariant C.lastClock
  have blind (v : Fin 26→K) (hv : v∈hiddenCarrier A b) (i : Fin 26) (vi : visible A b i) :
      v i=0 := by
    rcases vi with d|y
    · exact Hidden.carrier_zero_on_active C.lastSeed hv d
    · exact (mul_eq_zero.mp (Hidden.carrier_mirror_weight_zero C.lastClock hv i)).resolve_left y
  have det (v : Fin 26→K) (hv : v∈zeroSpace A 8) (h : ∀ i, visible A b i→v i=0) :
      v∈hiddenCarrier A b := by
    apply Hidden.actual_defect_hidden ha ho (by decide) hv
    · intro i
      by_cases z : quadraticSeed A b i=0
      · rw [z,zero_mul]
      · rw [h i (Or.inl z),mul_zero]
    · intro i
      change (reflectedClock A i*b i)*v i=0
      by_cases z : reflectedClock A i*b i=0
      · rw [z,zero_mul]
      · rw [h i (Or.inr z),mul_zero]
  have cap : finrank K (zeroSpace A 9)≤11 := by
    have h := F.nextRoom
    change finrank K (zeroSpace A 9) + _ ≤ 11 at h
    omega
  refine ⟨?_,H8,inv,invariant_core_cap_of_rank ha (by decide) F.separated
    F.middleDefects cap _ H8 inv,blind,det⟩
  intro v hv
  obtain ⟨Q,P,qd,pd,qfit,pfit⟩ := Thin.thin_reverse_two_traces ho hv (by decide)
    (by decide) (by decide) t y0 C.lastSeed C.sites C.pointwise
  have z := Thin.ordered_thin_invisible_given_reps ha ho y0 col supp Q P qd
    (by omega) (by omega) (by omega) (by omega) qfit pfit
  exact Hidden.actual_defect_hidden ha ho (by decide) hv (fun i => (z i).1) (fun i => (z i).2)

theorem ordered_width26_hidden_frame [LinearOrder K] [IsStrictOrderedRing K]
    (ha : ∀ i j, i≤j → A i j=0) (ho : HasOrder 17 A b) (z : firstSeed A b=0) :
    HiddenFrame A b :=
  width26_hidden_frame ha ho (ordered_width26_full_frame ha ho).1
    (ordered_width26_quadratic_cover ha ho z)

end
end RKResearch.Certified.ERK17
