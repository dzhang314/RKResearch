module

public import RKCert.ReviewedNative.ReversePhysicalPorts

@[expose] public section

/-! # Paid reverse rows outside a finite set of later clocks

Chronology is on the original row indices, not on the order of the
numbers stored in their clocks. The nodal mask removes every occurrence
of the covered clocks, including repeated physical rows. -/
namespace RKResearch.Certified.Graded.Reverse.Thin

open RKResearch Polynomial RKCert.Endpoint RKCert.Endpoint.WeightedClock
open scoped Classical Matrix

noncomputable section
variable {K : Type*} [Field K] [CharZero K] {s p m : ℕ}
variable {A : Matrix (Fin s) (Fin s) K} {b f : Fin s → K}
variable {Q P : K[X]}

/-- At the last active physical row whose reflected clock is not in S,
the entire affordable primitive window with nodal mask S vanishes.
This supports one-, two-, and three-clock cutoffs without increasing
the actual order budget. -/
theorem true_port_at_last_new_clock (ha : ∀ i j, i≤j → A i j=0)
    (ho : HasOrder p A b) {t : Fin s}
    (y0 : reflectedClock A t=0) (col : ∀k,A k t=0)
    (cover : SupportsComplement A b m t)
    (qfit : ∀ i,quadraticSeed A b i*f i=Q.eval (reflectedClock A i)*quadraticSeed A b i)
    (pfit : ∀ i,reflectedClock A i*b i*f i=P.eval (reflectedClock A i)*quadraticSeed A b i)
    (S : Finset K)
    (outside : ∃ i,reverseContrast A b Q P i≠0 ∧ reflectedClock A i∉S) :
    ∃ i : Fin s, reverseContrast A b Q P i≠0 ∧ reflectedClock A i∉S ∧
      reflectedClock A i≠0 ∧ Q.eval (reflectedClock A i)≠0 ∧
      (∀ j, i<j → reverseContrast A b Q P j≠0 → reflectedClock A j∈S) ∧
      ∀ R : K[X], m+Q.natDegree+R.natDegree+S.card+3≤p →
        m+P.natDegree+R.natDegree+S.card+4≤p →
        (primitive ((R*nodalHull S)*(X*Q))).eval (reflectedClock A i)=0 := by
  classical
  let y := reflectedClock A
  let W := reverseContrast A b Q P
  let T := Finset.univ.filter (fun i : Fin s => W i≠0 ∧ y i∉S)
  have nonempty : T.Nonempty := by
    obtain ⟨i,iw,iz⟩ := outside
    exact ⟨i,Finset.mem_filter.mpr ⟨Finset.mem_univ i,iw,iz⟩⟩
  obtain ⟨i,hi,imax⟩ := Finset.exists_max_image T id nonempty
  have props := (Finset.mem_filter.mp hi).2
  obtain ⟨d0,yn,bn,qn,_⟩ := reverse_contrast_true_support qfit pfit i props.1
  have after (j : Fin s) (ij : i<j) (active : W j≠0) : y j∈S := by
    by_contra bad
    have hjT : j∈T := Finset.mem_filter.mpr ⟨Finset.mem_univ j,active,bad⟩
    exact (not_le_of_gt ij) (imax j hjT)
  refine ⟨i,props.1,props.2,yn,qn,after,?_⟩
  intro R qb pb
  let H := R*nodalHull S
  have hd : H.natDegree≤R.natDegree+S.card := by
    have h := natDegree_mul_le (p:=R) (q:=nodalHull S)
    rw [natDegree_nodalHull] at h
    exact h
  have later : mat A.transpose (weightedEval y W H) i=0 := by
    apply causal_transpose ha
    intro j hj
    have lij := Fin.rev_lt_rev.mp hj
    by_cases zj : W j=0
    · simp [zj]
    simp [H,nodalHull_eval_of_mem (after j lij zj)]
  have check := true_port_eval ho y0 col cover Q P H (by omega) (by omega) d0
  change mat A.transpose (weightedEval y W H) i=_ at check
  rw [later] at check
  exact (mul_eq_zero.mp check.symm).resolve_right bn

end
end RKResearch.Certified.Graded.Reverse.Thin
