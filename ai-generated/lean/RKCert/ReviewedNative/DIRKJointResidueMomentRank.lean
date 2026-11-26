module

public import RKCert.ReviewedNative.DIRKPairedOriginGradeBridge
public import RKCert.ReviewedNative.PaidResidueMomentRank

import Mathlib.Algebra.BigOperators.Group.Finset.Basic

@[expose] public section

/-! # The actual two-channel incoming residue matrix on a DIRK row

Only the chosen origin and recipient rows need the indicated diagonal
and upper-zero data. Payment and fibre-tap recovery are separate:
the moment rank argument never infers either from an order label. -/
namespace RKResearch.Certified.Graded.PairedOrigin.Joint

open Polynomial RKResearch
open RKResearch.Certified.Graded.ResidueMomentRank
open scoped Classical Matrix

variable {K : Type*} [Field K] {s : ℕ}

/-- The two actual cleared derivative-stage residues, without a scalar mask. -/
noncomputable def chart (A : Matrix (Fin (s+1)) (Fin (s+1)) K) (γ : K) :
    Bool → (Fin (s+1) → K)
  | false => originResidual A γ
  | true => nextResidual A γ

def JointClean (A : Matrix (Fin (s+1)) (Fin (s+1)) K) (γ : K) (i : Fin (s+1)) : Prop :=
  originResidual A γ i = 0 ∧ nextResidual A γ i = 0

noncomputable def earlierJointClocks (A : Matrix (Fin (s+1)) (Fin (s+1)) K)
    (γ : K) (k : Fin (s+1)) : Finset K :=
  (earlierJointOffRows A γ k).image (nodes A)

noncomputable def earlierJointFibre (A : Matrix (Fin (s+1)) (Fin (s+1)) K)
    (γ : K) (k : Fin (s+1)) (x : K) : Finset (Fin (s+1)) :=
  (earlierJointOffRows A γ k).filter (fun i => nodes A i = x)

noncomputable def fibreTapMass (A : Matrix (Fin (s+1)) (Fin (s+1)) K)
    (γ : K) (k : Fin (s+1)) (x : K) : K :=
  ∑ i ∈ earlierJointFibre A γ k x, A k i

noncomputable def fibreResidue (A : Matrix (Fin (s+1)) (Fin (s+1)) K)
    (γ : K) (k : Fin (s+1)) (x : K) (b : Bool) : K :=
  ∑ i ∈ earlierJointFibre A γ k x, A k i * chart A γ b i

/-- Only actual taps, and no recovery on the common diagonal clock. -/
def FibreTapRecovery (A : Matrix (Fin (s+1)) (Fin (s+1)) K)
    (γ : K) (k : Fin (s+1)) : Prop :=
  ∀ x ∈ earlierJointClocks A γ k, x ≠ γ →
    fibreResidue A γ k x = 0 → fibreTapMass A γ k x = 0

/-- Literal incoming probes on the unchanged tableau, both through degree d. -/
def JointProbePaid (A : Matrix (Fin (s+1)) (Fin (s+1)) K)
    (γ : K) (k : Fin (s+1)) (d : ℕ) : Prop :=
  ∀ (b : Bool) (P : K[X]), P.natDegree ≤ d →
    mat A (diag (chart A γ b) (evalNodes A P)) k = 0

noncomputable def activeJointClocks (A : Matrix (Fin (s+1)) (Fin (s+1)) K)
    (γ : K) (k : Fin (s+1)) : Finset K :=
  activeFibres (earlierJointClocks A γ k) (fibreResidue A γ k)

noncomputable def incomingJointRank (A : Matrix (Fin (s+1)) (Fin (s+1)) K)
    (γ : K) (k : Fin (s+1)) : ℕ :=
  residueRank (activeJointClocks A γ k) (fibreResidue A γ k)

variable {A : Matrix (Fin (s+1)) (Fin (s+1)) K} {γ : K} {k : Fin (s+1)}

private theorem chart_zero {i : Fin (s+1)} (h : JointClean A γ i) (b : Bool) :
    chart A γ b i = 0 := by
  cases b
  · exact h.1
  · exact h.2

private theorem group_by_clock (F : K → K) (q : Fin (s+1) → K) :
    (∑ x ∈ earlierJointClocks A γ k, F x * (∑ i ∈ earlierJointFibre A γ k x, q i)) =
      ∑ i ∈ earlierJointOffRows A γ k, F (nodes A i) * q i := by
  classical
  calc
    _ = ∑ x ∈ earlierJointClocks A γ k,
          ∑ i ∈ (earlierJointOffRows A γ k).filter (fun i => nodes A i = x),
            F (nodes A i) * q i := by
      apply Finset.sum_congr rfl
      intro x _
      rw [earlierJointFibre, Finset.mul_sum]
      apply Finset.sum_congr rfl
      intro i hi
      rw [(Finset.mem_filter.mp hi).2]
    _ = _ := Finset.sum_fiberwise_of_maps_to (g := nodes A)
      (s := earlierJointOffRows A γ k) (t := earlierJointClocks A γ k)
      (fun i hi => Finset.mem_image_of_mem (nodes A) hi) _

private theorem jointOff_sum_eq_probe
    (upper : ∀ i, k < i → A k i = 0) (clean : JointClean A γ k)
    (b : Bool) (P : K[X]) :
    (∑ i ∈ earlierJointOffRows A γ k, P.eval (nodes A i) * (A k i * chart A γ b i)) =
      mat A (diag (chart A γ b) (evalNodes A P)) k := by
  classical
  calc
    _ = ∑ i ∈ earlierJointOffRows A γ k,
          A k i * (chart A γ b i * P.eval (nodes A i)) := by
      apply Finset.sum_congr rfl
      intro i _
      exact (mul_comm _ _).trans (mul_assoc _ _ _)
    _ = ∑ i : Fin (s+1), A k i * (chart A γ b i * P.eval (nodes A i)) := by
      apply Finset.sum_subset (Finset.subset_univ _)
      intro i _ hi
      by_cases past : i < k
      · have hc : JointClean A γ i := by
          by_contra dirty
          exact hi (Finset.mem_filter.mpr ⟨Finset.mem_Iio.mpr past, dirty⟩)
        rw [chart_zero hc b, zero_mul, mul_zero]
      · by_cases eq : i = k
        · subst i
          rw [chart_zero clean b, zero_mul, mul_zero]
        · rw [upper i (lt_of_le_of_ne (le_of_not_gt past) (Ne.symm eq)), zero_mul]
    _ = _ := by simp only [mat_apply, Matrix.mulVec, dotProduct, diag_apply, evalNodes_apply]

theorem paidMoments_of_actual_probes
    (upper : ∀ i, k < i → A k i = 0) (clean : JointClean A γ k)
    {d : ℕ} (paid : JointProbePaid A γ k d) :
    PaidMoments (earlierJointClocks A γ k) (fibreResidue A γ k) d := by
  intro b P hd
  calc
    _ = ∑ i ∈ earlierJointOffRows A γ k, P.eval (nodes A i) * (A k i * chart A γ b i) :=
      group_by_clock (A := A) (γ := γ) (k := k) P.eval (fun i => A k i * chart A γ b i)
    _ = _ := (jointOff_sum_eq_probe upper clean b P).trans (paid b P hd)

private theorem offReceipt_eq_grouped (P : K[X]) :
    (∑ i ∈ earlierJointOffRows A γ k, A k i * P.derivative.eval (nodes A i)) =
      ∑ x ∈ earlierJointClocks A γ k, P.derivative.eval x * fibreTapMass A γ k x := by
  calc
    _ = ∑ i ∈ earlierJointOffRows A γ k, P.derivative.eval (nodes A i) * A k i := by
      apply Finset.sum_congr rfl
      intro i _
      exact mul_comm _ _
    _ = _ := (group_by_clock (A := A) (γ := γ) (k := k) P.derivative.eval (A k)).symm

/-- The literal clean-row receipt forces an active nonorigin clock when
zero paired residue recovers the actual tap mass there. -/
theorem exists_nonorigin_residue_ne_of_recovery
    (hγ : γ ≠ 0) (upper : ∀ i, k < i → A k i = 0) (diagonal : A k k = γ)
    (clean : JointClean A γ k) (nonorigin : nodes A k ≠ γ)
    (first : ∀ i, i < k → JointClean A γ i → nodes A i = γ)
    (recover : FibreTapRecovery A γ k) :
    ∃ x ∈ earlierJointClocks A γ k, x ≠ γ ∧ fibreResidue A γ k x ≠ 0 := by
  classical
  by_contra none
  have vanish (P : K[X]) (der0 : P.derivative.eval γ = 0) :
      (∑ i ∈ earlierJointOffRows A γ k, A k i * P.derivative.eval (nodes A i)) = 0 := by
    rw [offReceipt_eq_grouped]
    apply Finset.sum_eq_zero
    intro x hx
    by_cases eq : x = γ
    · rw [eq, der0, zero_mul]
    · have rz : fibreResidue A γ k x = 0 := by
        by_contra nr
        exact none ⟨x, hx, eq, nr⟩
      rw [recover x hx eq rz, mul_zero]
  have zeros := primitive_double_zero γ
  rcases paired_offReceipt_ne_of_first_nonorigin hγ upper diagonal clean.1 clean.2 nonorigin
      (fun i hi hg hh => first i hi ⟨hg,hh⟩) with ne | ne
  · exact ne (vanish _ zeros.1.2)
  · exact ne (vanish _ zeros.2.2)

/-- Literal paid probes on both channels force d+1+actual-rank active
clocks. This does not assume rank two or assign a generic scalar mask. -/
theorem incoming_rank_and_active_card_of_paid
    (hγ : γ ≠ 0) (upper : ∀ i, k < i → A k i = 0) (diagonal : A k k = γ)
    (clean : JointClean A γ k) (nonorigin : nodes A k ≠ γ)
    (first : ∀ i, i < k → JointClean A γ i → nodes A i = γ)
    (recover : FibreTapRecovery A γ k) {d : ℕ} (paid : JointProbePaid A γ k d) :
    0 < incomingJointRank A γ k ∧
      d+1+incomingJointRank A γ k ≤ (activeJointClocks A γ k).card := by
  classical
  obtain ⟨x, hx, _, nz⟩ := exists_nonorigin_residue_ne_of_recovery hγ upper diagonal
    clean nonorigin first recover
  have active : x ∈ activeJointClocks A γ k := by
    unfold activeJointClocks activeFibres
    exact Finset.mem_filter.mpr ⟨hx,nz⟩
  have someChannel : ∃ b : Bool, fibreResidue A γ k x b ≠ 0 := by
    by_contra none
    apply nz
    funext b
    by_contra hb
    exact none ⟨b,hb⟩
  obtain ⟨b, hb⟩ := someChannel
  have pos : 0 < incomingJointRank A γ k := residueRank_pos_of_entry active hb
  exact ⟨pos, active_card_of_paid_rank_pos (paidMoments_of_actual_probes upper clean paid) pos⟩

/-- One use of the checked centered-grade API pays both actual channels.
The grade-three seed is included in grade four, with no normalization units. -/
theorem jointProbePaid_of_centered_annihilation
    (upper0 : ∀ i, (0 : Fin (s+1)) < i → A 0 i = 0) (diagonal0 : A 0 0 = γ)
    {d : ℕ} (units : ∀ t : FiniteRootedTree, (t.order:ℕ) ≤ 4+d+1 → IsUnit (((t.order:ℕ):K)))
    (kill : ∀ v ∈ centeredZeroSpace A (4+d+1), v k = 0) :
    JointProbePaid A γ k d := by
  intro b P hd
  have origin := paired_actual_origin_clean A upper0 diagonal0
  have seed : chart A γ b ∈ centeredZeroSpace A 4 := by
    apply mem_centeredZeroSpace.mpr
    cases b
    · exact ⟨zeroSpace_mono A (by decide : 3 ≤ 4) (originResidual_mem_grade A γ), origin.1⟩
    · exact ⟨nextResidual_mem_grade A γ, origin.2⟩
  exact kill _ (mat_mem_centered_of_unit upper0 units (defectPolynomial_mem_centered seed hd))

/-- Join the two independently earned inputs: centered payment and actual
fibre recovery. The receiver still has to be genuinely joint-clean. -/
theorem incoming_rank_and_active_card_of_centered_annihilation
    (hγ : γ ≠ 0) (upper0 : ∀ i, (0 : Fin (s+1)) < i → A 0 i = 0) (diagonal0 : A 0 0 = γ)
    (upper : ∀ i, k < i → A k i = 0) (diagonal : A k k = γ)
    (clean : JointClean A γ k) (nonorigin : nodes A k ≠ γ)
    (first : ∀ i, i < k → JointClean A γ i → nodes A i = γ)
    (recover : FibreTapRecovery A γ k) {d : ℕ}
    (units : ∀ t : FiniteRootedTree, (t.order:ℕ) ≤ 4+d+1 → IsUnit (((t.order:ℕ):K)))
    (kill : ∀ v ∈ centeredZeroSpace A (4+d+1), v k = 0) :
    0 < incomingJointRank A γ k ∧
      d+1+incomingJointRank A γ k ≤ (activeJointClocks A γ k).card :=
  incoming_rank_and_active_card_of_paid hγ upper diagonal clean nonorigin first recover
    (jointProbePaid_of_centered_annihilation upper0 diagonal0 units kill)

end RKResearch.Certified.Graded.PairedOrigin.Joint
