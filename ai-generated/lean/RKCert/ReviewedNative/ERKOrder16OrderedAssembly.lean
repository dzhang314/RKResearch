module

public import RKCert.ReviewedNative.StagePadding
public import RKCert.ReviewedNative.ERKOrder16NativeHeadDispatch
public import RKCert.ReviewedNative.ERKOrder16StrongCenteredEndpoint
public import RKCert.ReviewedNative.ERKOrder16WeakFourPorts
public import RKCert.ReviewedNative.ERKOrder16WeakFiveAdapter

@[expose] public section

/-! # Ordered ERK16 assembly from the two exact weak scalar exclusions

There is no strong scalar premise, no additional rank/chart premise,
and no externally supplied statement about a physical stage. -/
namespace RKResearch.Certified.ERK16

open RKResearch Polynomial

/-- The genuine weak-four packet, including the third actual port and
all paid global spectators. -/
abbrev WeakFourScalarExclusion (K : Type*) [Field K] : Prop :=
  ∀ {Q Z : K[X]} {a c : K}, WeakFourChronologicalPorts Q Z a c → False

/-- The genuine weak-five packet with the same five physical labels in
all six local moments and the full degree-five global window. -/
abbrev WeakFiveScalarExclusion (K : Type*) [Field K] [CharZero K] : Prop :=
  ∀ {q Z : K[X]} {c : Fin 5 → K},
    RKCert.ReviewedNative.WeakFive16.Moments q Z c → False

variable {K : Type*} [Field K] [LinearOrder K] [IsStrictOrderedRing K]

/-- On width 24 the reviewed conditions earn the actual branch and
all its physical hypotheses. Only the two scalar contradictions
remain as inputs. -/
theorem width24_impossible_of_weak_scalar_exclusions
    (weakFour : WeakFourScalarExclusion K) (weakFive : WeakFiveScalarExclusion K)
    (A : Matrix (Fin 24) (Fin 24) K) (b : Fin 24 → K)
    (ha : ∀ i j, i ≤ j → A i j = 0) (ho : HasOrder 16 A b) : False := by
  rcases (width24_native_head_dispatch ha ho).2 with ordinary | strong
  · obtain ⟨seven, _, _, _, _, L, chart⟩ := ordinary
    rcases chart with four | five
    · obtain ⟨_, _, _, _, _, _, ports⟩ :=
        native_width24_weak_four_extra_port ha ho L.qDegree L.pDegree
          L.qFit L.pFit four
      exact weakFour ports
    · obtain ⟨_, _, _, moments⟩ :=
        width24_weak_five_moments_of_ordinary_head ha ho seven L five.symm.le
      exact weakFive moments
  · exact width24_strong_seventh_rank_ne_eight ha ho strong.1

/-- Native padding reduces arbitrary width to the actual width-24
exclusion. The seed tested after padding is the padded tableau's own. -/
theorem ordered_erk16_stage_floor25_of_weak_scalar_exclusions
    (weakFour : WeakFourScalarExclusion K) (weakFive : WeakFiveScalarExclusion K)
    {s : ℕ} {A : Matrix (Fin s) (Fin s) K} {b : Fin s → K}
    (ha : ∀ i j, i ≤ j → A i j = 0) (ho : HasOrder 16 A b) : 25 ≤ s := by
  have gt : 24 < s :=
    RKResearch.Certified.StagePadding.strict_stages_gt_of_exact_exclusion
      (n := 24) (p := 16)
      (width24_impossible_of_weak_scalar_exclusions weakFour weakFive) ha ho
  exact Nat.succ_le_of_lt gt

end RKResearch.Certified.ERK16
