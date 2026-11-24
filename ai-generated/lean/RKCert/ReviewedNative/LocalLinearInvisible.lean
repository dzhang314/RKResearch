module

public import RKCert.ReviewedNative.LocalLinearReversePorts
public import RKCert.ReviewedNative.NativeQuinticPorts

@[expose] public section

/-! # A true low-grade feature is invisible to the local reverse head -/
namespace RKResearch.Certified.Graded.Reverse.LocalLinear
open RKResearch Module Polynomial RKCert.Endpoint RKCert.OneEscape
open scoped Classical Matrix
noncomputable section
variable {K : Type*} [Field K] {s p : ℕ}
variable {A : Matrix (Fin s) (Fin s) K} {b : Fin s→K}
variable {r j : ℕ} {U : Submodule K (Fin s→K)} {τ f : Fin s→K} {P Q : K[X]}

theorem local_linear_small_trace_zero [CharZero K]
    (ha : ∀ i j,i≤j → A i j=0) (ho : HasOrder p A b)
    (F : LocalLinearBand A b 8 r U τ)
    (full : primitiveBack A b 8=annih (treeSpace A 9))
    (pay : 19≤p) (fit : LocalLinearTraces A b U τ f r j P Q)
    (dQ : Q.natDegree≤4) (dP : P=0 ∨ P.natDegree+r+1≤4) :
    Q=0 := by
  by_contra nonzero
  obtain ⟨u,un,one⟩ := physical_local_reverse_port ha ho F full (by omega) (by decide)
    fit dQ dP nonzero X (by simp) X_ne_zero
  let H : K[X] := X*(X-C u)
  have du : H.natDegree≤2 := by
    apply natDegree_mul_le.trans
    simp
  have hn : H≠0 := mul_ne_zero X_ne_zero (X_sub_C_ne_zero u)
  obtain ⟨v,vn,two⟩ := physical_local_reverse_port ha ho F full (by omega) (by decide)
    fit dQ dP nonzero H du hn
  rw [eval_X] at un
  have vnot : v≠0 ∧ v≠u := by
    simpa [H,eval_mul,eval_sub,sub_ne_zero] using vn
  apply nonzero
  apply RKCert.ReviewedNative.Quintic.quintic_four_three Q (by omega) un vnot.1 vnot.2
  · intro k
    have n : k.val<4 := k.isLt
    have shift : (X : K[X]).natDegree+(X^k.val : K[X]).natDegree+4≤8 := by
      simp only [natDegree_X,natDegree_X_pow]; omega
    simpa only [pow_succ',mul_assoc] using one (X^k.val) shift
  · intro k
    have n : k.val<3 := k.isLt
    have shift : H.natDegree+(X^k.val : K[X]).natDegree+4≤8 := by
      rw [natDegree_X_pow]; omega
    have e : H*X^k.val*Q=X^(k.val+1)*((X-C u)*Q) := by
      rw [pow_succ']; dsimp only [H]; ac_rfl
    rw [←e]
    exact two (X^k.val) shift

variable [LinearOrder K] [IsStrictOrderedRing K]

/-- Conversion from the two actual traces; signed output weights need no positivity. -/
theorem local_linear_invisible_of_small_traces
    (ha : ∀ i j,i≤j → A i j=0) (ho : HasOrder p A b)
    (F : LocalLinearBand A b 8 r U τ)
    (full : primitiveBack A b 8=annih (treeSpace A 9))
    (pay : 19≤p) (fit : LocalLinearTraces A b U τ f r j P Q)
    (dQ : Q.natDegree≤4) (dP : P=0 ∨ P.natDegree+r+1≤4) :
    τ*f=0 ∧ b*f∈U ∧ U.map (diag f)≤U := by
  have Qz := local_linear_small_trace_zero ha ho F full pay fit dQ dP
  have τf : τ*f=0 := by
    rw [fit.tauTrace,Qz,map_zero]
  let y := reflectedClock A
  let v := weightedEval y τ P
  have annv : v∈annih U := by
    apply mem_annih.mpr
    intro w hw
    have paid := mem_annih.mp F.headOrthogonal _ (reflected_clock_weighted_core F.invariant hw P)
    rw [row_apply,dotProduct] at paid ⊢
    convert paid using 1
    apply Finset.sum_congr rfl
    intro i _
    simp only [v,weightedEval_apply]
    ring
  have off : row v (b*f)=0 := by
    rw [row_apply,dotProduct]
    apply Finset.sum_eq_zero
    intro i _
    have e : τ i*f i=0 := congrFun τf i
    simp only [v,weightedEval_apply,Pi.mul_apply]
    rw [show P.eval (y i)*τ i*(b i*f i)=(P.eval (y i)*b i)*(τ i*f i) by ring,e,mul_zero]
  have fitB : b*f-v∈U := fit.weightTrace
  have test : row v (b*f-v)=0 := mem_annih.mp annv _ fitB
  rw [map_sub,off,zero_sub,neg_eq_zero] at test
  have zero := eq_zero_of_self_row_zero test
  exact ⟨τf,by simpa only [zero,sub_zero] using fitB,fit.preserves⟩

/-- Paid grades 0 through 4 give the actual invisible triple. -/
theorem local_linear_invisible_four
    (ha : ∀ i j,i≤j → A i j=0) (ho : HasOrder p A b)
    (F : LocalLinearBand A b 8 r U τ)
    (full : primitiveBack A b 8=annih (treeSpace A 9))
    (pay : 19≤p) {f : Fin s→K} (hf : f∈zeroSpace A 4) :
    τ*f=0 ∧ b*f∈U ∧ U.map (diag f)≤U := by
  have rb : r≤2 := by rcases F.coreRank with q|q <;> omega
  obtain ⟨P,Q,fit⟩ := local_linear_two_traces ho F full (by omega) (by omega) hf
  exact local_linear_invisible_of_small_traces ha ho F full pay fit fit.qDeg fit.pDeg

end
end RKResearch.Certified.Graded.Reverse.LocalLinear
