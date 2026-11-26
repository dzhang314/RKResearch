import RKCert.ReviewedNative.DIRKJointResidueMomentRank

/-! Standalone typed checks, conditional on actual joint payment and recovery. -/
open Polynomial RKResearch RKResearch.Certified.Graded
open RKResearch.Certified.Graded.PairedOrigin RKResearch.Certified.Graded.PairedOrigin.Joint
open RKResearch.Certified.Graded.ResidueMomentRank
open scoped Classical Matrix

section
variable {K : Type*} [Field K] {s : ℕ}
variable {A : Matrix (Fin (s+1)) (Fin (s+1)) K} {γ : K} {k : Fin (s+1)} {d : ℕ}

example (upper : ∀ i, k < i → A k i = 0)
    (cleanG : originResidual A γ k = 0) (cleanH : nextResidual A γ k = 0)
    (paid : ∀ (b : Bool) (P : K[X]), P.natDegree ≤ d →
      mat A (diag (chart A γ b) (evalNodes A P)) k = 0)
    (b : Bool) (P : K[X]) (hd : P.natDegree ≤ d) :
    (∑ x ∈ earlierJointClocks A γ k, P.eval x *
      (∑ i ∈ earlierJointFibre A γ k x, A k i * chart A γ b i)) = 0 :=
  paidMoments_of_actual_probes upper ⟨cleanG,cleanH⟩
    (show JointProbePaid A γ k d from paid) b P hd

example (hγ : γ ≠ 0) (upper : ∀ i, k < i → A k i = 0) (diagonal : A k k = γ)
    (cleanG : originResidual A γ k = 0) (cleanH : nextResidual A γ k = 0)
    (nonorigin : nodes A k ≠ γ)
    (first : ∀ i, i < k → originResidual A γ i = 0 → nextResidual A γ i = 0 → nodes A i = γ)
    (recover : ∀ x ∈ earlierJointClocks A γ k, x ≠ γ →
      (∀ b : Bool, (∑ i ∈ earlierJointFibre A γ k x, A k i * chart A γ b i) = 0) →
      (∑ i ∈ earlierJointFibre A γ k x, A k i) = 0) :
    ∃ x ∈ earlierJointClocks A γ k, x ≠ γ ∧ fibreResidue A γ k x ≠ 0 := by
  refine exists_nonorigin_residue_ne_of_recovery hγ upper diagonal ⟨cleanG,cleanH⟩ nonorigin ?_ ?_
  · intro i hi hc
    exact first i hi hc.1 hc.2
  · intro x hx nx hz
    exact recover x hx nx (fun b => congrFun hz b)

example (hγ : γ ≠ 0) (upper : ∀ i, k < i → A k i = 0) (diagonal : A k k = γ)
    (clean : JointClean A γ k) (nonorigin : nodes A k ≠ γ)
    (first : ∀ i, i < k → JointClean A γ i → nodes A i = γ)
    (recover : FibreTapRecovery A γ k)
    (paid : ∀ (b : Bool) (P : K[X]), P.natDegree ≤ d →
      mat A (diag (chart A γ b) (evalNodes A P)) k = 0) :
    let X := activeFibres (earlierJointClocks A γ k) (fibreResidue A γ k)
    let r := residueRank X (fibreResidue A γ k)
    0 < r ∧ d+1+r ≤ X.card :=
  incoming_rank_and_active_card_of_paid hγ upper diagonal clean nonorigin first recover
    (show JointProbePaid A γ k d from paid)

example (upper0 : ∀ i, (0 : Fin (s+1)) < i → A 0 i = 0) (diagonal0 : A 0 0 = γ)
    (units : ∀ t : FiniteRootedTree, (t.order:ℕ) ≤ 4+d+1 → IsUnit (((t.order:ℕ):K)))
    (kill : ∀ v ∈ zeroSpace A (4+d+1), v 0 = 0 → v k = 0) :
    ∀ (b : Bool) (P : K[X]), P.natDegree ≤ d →
      mat A (diag (chart A γ b) (evalNodes A P)) k = 0 := by
  refine jointProbePaid_of_centered_annihilation upper0 diagonal0 units ?_
  intro v hv
  have hv' := mem_centeredZeroSpace.mp hv
  exact kill v hv'.1 hv'.2

example (hγ : γ ≠ 0) (upper0 : ∀ i, (0 : Fin (s+1)) < i → A 0 i = 0) (diagonal0 : A 0 0 = γ)
    (upper : ∀ i, k < i → A k i = 0) (diagonal : A k k = γ)
    (cleanG : originResidual A γ k = 0) (cleanH : nextResidual A γ k = 0)
    (nonorigin : nodes A k ≠ γ)
    (first : ∀ i, i < k → originResidual A γ i = 0 → nextResidual A γ i = 0 → nodes A i = γ)
    (recover : ∀ x ∈ earlierJointClocks A γ k, x ≠ γ →
      (∀ b : Bool, (∑ i ∈ earlierJointFibre A γ k x, A k i * chart A γ b i) = 0) →
      (∑ i ∈ earlierJointFibre A γ k x, A k i) = 0)
    (units : ∀ t : FiniteRootedTree, (t.order:ℕ) ≤ 4+d+1 → IsUnit (((t.order:ℕ):K)))
    (kill : ∀ v ∈ zeroSpace A (4+d+1), v 0 = 0 → v k = 0) :
    let X := activeFibres (earlierJointClocks A γ k) (fibreResidue A γ k)
    let r := residueRank X (fibreResidue A γ k)
    0 < r ∧ d+1+r ≤ X.card := by
  refine incoming_rank_and_active_card_of_centered_annihilation hγ upper0 diagonal0 upper diagonal
    ⟨cleanG,cleanH⟩ nonorigin ?_ ?_ units ?_
  · intro i hi hc
    exact first i hi hc.1 hc.2
  · intro x hx nx hz
    exact recover x hx nx (fun b => congrFun hz b)
  · intro v hv
    have hv' := mem_centeredZeroSpace.mp hv
    exact kill v hv'.1 hv'.2

end

#print axioms RKResearch.Certified.Graded.PairedOrigin.Joint.paidMoments_of_actual_probes
#print axioms RKResearch.Certified.Graded.PairedOrigin.Joint.exists_nonorigin_residue_ne_of_recovery
#print axioms RKResearch.Certified.Graded.PairedOrigin.Joint.incoming_rank_and_active_card_of_paid
#print axioms RKResearch.Certified.Graded.PairedOrigin.Joint.jointProbePaid_of_centered_annihilation
#print axioms RKResearch.Certified.Graded.PairedOrigin.Joint.incoming_rank_and_active_card_of_centered_annihilation
