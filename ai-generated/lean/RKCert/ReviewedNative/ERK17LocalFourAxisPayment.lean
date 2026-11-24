module

public import RKCert.ReviewedNative.ERK17LocalFourAxes

@[expose] public section

/-! # The actual paid rank-two axis mode

At the r=2, grade-six border, the axis preserves U and carries its own
weight refund, but need not have a polynomial head trace. If it did have
one of degree at most four, the ordered quartic gate would hide it, contrary
to the genuine second-axis property. -/
namespace RKResearch.Certified.ERK17
open RKResearch Module Polynomial Graded Graded.Reverse Graded.Reverse.LocalLinear
open RKCert.Endpoint
open scoped Classical Matrix
noncomputable section

variable {K : Type*} [Field K] [LinearOrder K] [IsStrictOrderedRing K]
variable {A : Matrix (Fin 26) (Fin 26) K} {b τ h ξ : Fin 26→K}
variable {U : Submodule K (Fin 26→K)}

set_option maxRecDepth 3500
set_option maxHeartbeats 750000

theorem local_four_axis_no_small_profile
    (ha : ∀ i j,i≤j → A i j=0) (ho : HasOrder 17 A b)
    (F : LocalLinearBand A b 7 2 U τ) (full : primitiveBack A b 7=annih (treeSpace A 8))
    (D : LocalFourAxes A b τ h ξ U) (R : K[X]) (rd : R.natDegree≤4)
    (form : τ*ξ=weightedEval (reflectedClock A) τ R) : False := by
  obtain ⟨u,hu,P,pd,eq⟩ := D.weightRefund
  have trace : b*ξ-weightedEval (reflectedClock A) τ P∈U := by
    rw [eq,add_sub_cancel_right]
    exact hu
  have fit : LocalLinearTraces A b U τ ξ 2 6 P R :=
    ⟨D.axisPreserves,by omega,Or.inr (by omega),form,trace⟩
  have rz := local_linear_quartic_trace_zero ha ho F full (by decide) fit rd (Or.inr (by omega))
  exact D.axisOut (LocalLinearTraces.mem_hidden_of_q_zero F fit rz)

theorem local_four_axis_paid_E7 (ho : HasOrder 17 A b)
    (F : LocalLinearBand A b 7 2 U τ) {v : Fin 26→K} (hv : v∈zeroSpace A 6) :
    τ*v∈annih (treeSpace A 7) := by
  have m := primitive_shifted_column_annih ho (n:=2) (j:=6) (g:=7) (k:=0)
    (by decide) F.headMem (zeroSpace_le_treeSpace A 6 hv)
  simpa only [pow_zero,Module.End.one_eq_id,LinearMap.id_apply] using m

theorem local_four_low_head_paid_E7 (ho : HasOrder 17 A b)
    (F : LocalLinearBand A b 7 2 U τ) (P : K[X]) (pd : P.natDegree≤6) :
    weightedEval (reflectedClock A) τ P∈annih (treeSpace A 7) := by
  have m := weighted_primitive_band F.headMem P pd
  exact primitiveBack_annih ho 7 (2+6) (by decide) m

/-- A real extra axis always yields a nonzero paid τ-product, orthogonal
to the early core. Its proof uses the r=2 border, not a fictitious F6 full
trace or a larger forward or reverse horizon. -/
theorem local_four_axis_paid_nonzero
    (ha : ∀ i j,i≤j → A i j=0) (ho : HasOrder 17 A b)
    (F : LocalLinearBand A b 7 2 U τ) (full : primitiveBack A b 7=annih (treeSpace A 8))
    (D : LocalFourAxes A b τ h ξ U) :
    τ*ξ≠0 ∧ τ*ξ∈annih (treeSpace A 7) ∧ τ*ξ∈annih U := by
  refine ⟨?_,local_four_axis_paid_E7 ho F D.sixth,?_⟩
  · intro z
    exact local_four_axis_no_small_profile ha ho F full D 0 (by simp) (by simpa only [map_zero] using z)
  · apply mem_annih.mpr
    intro u hu
    have e := mem_annih.mp F.headOrthogonal _ (D.axisPreserves (Submodule.mem_map_of_mem hu))
    simpa only [row_apply,dotProduct,Pi.mul_apply,diag_apply,mul_assoc] using e

theorem local_four_axis_one_clock_mode
    (ha : ∀ i j,i≤j → A i j=0) (ho : HasOrder 17 A b)
    (F : LocalLinearBand A b 7 2 U τ) (full : primitiveBack A b 7=annih (treeSpace A 8))
    (D : LocalFourAxes A b τ h ξ U) (a : K) (locality : ∀ i,reflectedClock A i≠a → ξ i=0) :
    ∃ ℓ : Fin 26→K, ℓ≠0 ∧ ℓ∈annih (treeSpace A 7) ∧ ℓ∈annih U ∧
      (∀ i,reflectedClock A i≠a → ℓ i=0) ∧
      ∀ i,reflectedClock A i=a → ℓ i=τ i*(ξ i-0) := by
  obtain ⟨live,paid,orth⟩ := local_four_axis_paid_nonzero ha ho F full D
  exact ⟨τ*ξ,live,paid,orth,
    fun i off=>by simp only [Pi.mul_apply,locality i off,mul_zero],
    fun _ _=>by simp only [Pi.mul_apply,sub_zero]⟩

end
end RKResearch.Certified.ERK17
