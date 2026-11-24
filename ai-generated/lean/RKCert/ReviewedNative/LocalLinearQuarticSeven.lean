module

public import RKCert.ReviewedNative.LocalLinearHiddenKernel
public import RKCert.ReviewedNative.PhysicalEndpointMomentPorts
public import RKCert.ReviewedNative.OrderedNodalGain

@[expose] public section

/-! # The actual h=7 paid quartic visibility window

With filter `X` there are three tests, and with filter `X(X-u)` there
are two. They are the exact ordered quartic gates. No order-19 4+3
visibility result is used here. -/
namespace RKResearch.Certified.Graded.Reverse.LocalLinear
open RKResearch Module Polynomial RKCert.Endpoint
open scoped Classical Matrix
noncomputable section

variable {K : Type*} [Field K] [LinearOrder K] [IsStrictOrderedRing K] {s p r j : ℕ}
variable {A : Matrix (Fin s) (Fin s) K} {b τ f : Fin s→K}
variable {U : Submodule K (Fin s→K)} {P Q : K[X]}

set_option maxRecDepth 3500
set_option maxHeartbeats 750000

theorem local_linear_quartic_trace_zero
    (ha : ∀ i j,i≤j → A i j=0) (ho : HasOrder p A b)
    (F : LocalLinearBand A b 7 r U τ)
    (full : primitiveBack A b 7=annih (treeSpace A 8)) (pay : 17≤p)
    (fit : LocalLinearTraces A b U τ f r j P Q)
    (qd : Q.natDegree≤4) (pd : P=0∨P.natDegree+r+1≤4) : Q=0 := by
  by_contra qn
  obtain ⟨u,un,one⟩ := physical_local_reverse_port ha ho F full (by omega) (by decide)
    fit qd pd qn X (by simp) X_ne_zero
  let H : K[X] := X*(X-C u)
  have hd : H.natDegree≤2 := by
    apply natDegree_mul_le.trans
    simp
  have hn : H≠0 := mul_ne_zero X_ne_zero (X_sub_C_ne_zero u)
  obtain ⟨v,vn,two⟩ := physical_local_reverse_port ha ho F full (by omega) (by decide)
    fit qd pd qn H hd hn
  rw [eval_X] at un
  have vt : v≠0 ∧ v≠u := by simpa [H,eval_mul,eval_sub,sub_ne_zero] using vn
  apply qn
  apply RKCert.EndpointPhysical.ordered_quartic_eq_zero_of_primitives qd un vt.1 vt.2
  refine ⟨?_,?_⟩
  · intro R hr
    rw [formalPrimitive_eq_native,show R*(X*Q)=(X*R)*Q by ring]
    apply one R
    rw [natDegree_X]
    omega
  · intro R hr
    rw [formalPrimitive_eq_native,show R*(X*(X-C u)*Q)=(H*R)*Q by dsimp only [H]; ring]
    exact two R (by omega)

/-- Vanishing first trace gives actual hidden membership by dot
orthogonality, independently of the horizon. -/
theorem LocalLinearTraces.mem_hidden_of_q_zero {h : ℕ}
    (F : LocalLinearBand A b h r U τ) (fit : LocalLinearTraces A b U τ f r j P Q)
    (qz : Q=0) : f∈hiddenKernel b τ U := by
  have tf : τ*f=0 := by rw [fit.tauTrace,qz,map_zero]
  let y := reflectedClock A
  let v := weightedEval y τ P
  have av : v∈annih U := by
    apply mem_annih.mpr
    intro w hw
    have z := mem_annih.mp F.headOrthogonal _ (reflected_clock_weighted_core F.invariant hw P)
    rw [row_apply,dotProduct] at z ⊢
    convert z using 1
    apply Finset.sum_congr rfl
    intro i _
    simp only [v,weightedEval_apply]
    ring
  have off : row v (b*f)=0 := by
    rw [row_apply,dotProduct]
    apply Finset.sum_eq_zero
    intro i _
    have e : τ i*f i=0 := congrFun tf i
    simp only [v,weightedEval_apply,Pi.mul_apply]
    rw [show P.eval (y i)*τ i*(b i*f i)=(P.eval (y i)*b i)*(τ i*f i) by ring,e,mul_zero]
  have w : b*f-v∈U := fit.weightTrace
  have k := mem_annih.mp av _ w
  rw [map_sub,off,zero_sub,neg_eq_zero] at k
  have vz := eq_zero_of_self_row_zero k
  exact mem_hiddenKernel.mpr ⟨tf,by simpa only [vz,sub_zero] using w,fit.preserves⟩

theorem grade_four_le_hiddenKernel_at_seven
    (ha : ∀ i j,i≤j → A i j=0) (ho : HasOrder p A b)
    (F : LocalLinearBand A b 7 r U τ)
    (full : primitiveBack A b 7=annih (treeSpace A 8)) (pay : 17≤p) :
    zeroSpace A 4≤hiddenKernel b τ U := by
  intro f hf
  have rb : r≤2 := by rcases F.coreRank with e|e <;> omega
  obtain ⟨P,Q,fit⟩ := local_linear_two_traces ho F full (by omega) (by omega) hf
  exact LocalLinearTraces.mem_hidden_of_q_zero F fit
    (local_linear_quartic_trace_zero ha ho F full pay fit fit.qDeg fit.pDeg)

end
end RKResearch.Certified.Graded.Reverse.LocalLinear
