module

public import RKCert.ReviewedNative.ERK13NativeMarkedCubicPorts
public import RKCert.ReviewedNative.NativeCubicTwoPort
public import RKCert.ReviewedNative.GradedGrowth

import Lean.Elab.Tactic.Omega

@[expose] public section

/-! # The universal grade-two core cut and radius ceiling

The paid port for a quadratic defect falls in unmarked F6, the literal
head band. The same checked two-port scalar detector therefore suffices
without assuming anything about F7 or the entry time of the terminal. -/
namespace RKResearch.Certified.Graded.ERK13NativeFirst

open RKResearch Polynomial Reverse Module RKCert.OneEscape RKCert.Endpoint
open scoped Matrix Classical
noncomputable section

variable {K : Type*} [Field K] [CharZero K]
variable {A : Matrix (Fin 19) (Fin 19) K} {b : Fin 19 → K}
variable {U : Submodule K (Fin 19 → K)} {w : Fin 19 → K} {r a : ℕ} {G : K[X]}

-- Separate the actual F6 payment and its zero-mode physical trace from
-- the scalar two-port dispatch. All dependent arguments here refer to the
-- very same residual and core match chosen by the native pivot.
private theorem quadratic_physical_port
    (H : NativeMarkedEscapeChart A b a G r U w)
    (ha : ∀ i j, i≤j → A i j=0) (ho : HasOrder 13 A b)
    {v : Fin 19→K} {P : K[X]} (hv : v∈zeroSpace A 2)
    (vStable : U.map (diag v)≤U) (pn : P≠0) (pd : P.natDegree≤2)
    (pr : v*w-weightedEval (nodes A) w P∈U)
    (S : K[X]) (sn : S≠0) (sd : S.natDegree≤2) :
    ∃ i : Fin 19, S.eval (nodes A i)≠0 ∧
      ∀ k : ℕ, k+S.natDegree≤3 → (primitive (X^k*(S*P))).eval (nodes A i)=0 := by
  let z : Fin 19 → K := markedProfileResidual A v P S
  have hv3 : v∈zeroSpace A 3 := zeroSpace_mono A (by decide : 2≤3) hv
  have pick : ∃ i g, NativeMarkedPivot A b U w v z G S i g :=
    H.pivot_for_polynomial_mask ha ho hv3 vStable (pd.trans (by decide : 2≤3))
      pn pr S (sd.trans (by decide : 2≤3)) sn
  obtain ⟨i,g,pivot⟩ := pick
  refine ⟨i,pivot.maskNonzero,?_⟩
  intro k hk
  let T : K[X] := X^k
  have td : (T*S).natDegree≤3 := by
    have le := natDegree_mul_le (p:=T) (q:=S)
    have tdeg : T.natDegree=k := natDegree_X_pow k
    rw [tdeg] at le
    exact le.trans hk
  let Z : Fin 19 → K := evalNodes A (primitive ((T*S)*P)) - mat A (evalNodes A T*(z-g))
  have paid : Z∈zeroSpace A 6 :=
    H.primitive_prefix_paid ho (d:=2) (v:=v) (z:=z) (g:=g) (S:=S) (P:=P)
      (by decide) hv pivot.core (markedProfileResidual_apply (A:=A) (v:=v) (P:=P) S) pd T td
  have f6 : zeroSpace A 6=escapeHeadBand A U w (r+1) := H.head.head.flags 1 (by decide)
  have tag : Z-(0:K) • evalNodes A (0:K[X])∈markedEscapeHeadBand A b U w (r+1) := by
    rw [zero_smul,sub_zero]
    exact Submodule.mem_sup_left (f6 ▸ paid)
  have eq := pivot.primitive_mode_trace ha (evalNodes A T) (R:=(T*S)*P)
    (J:=0) (factor:=0) (n:=r+1) tag
  simpa only [T,mul_assoc,zero_mul] using eq

theorem NativeMarkedEscapeChart.grade_two_le_core
    (H : NativeMarkedEscapeChart A b a G r U w)
    (ha : ∀ i j, i≤j → A i j=0) (ho : HasOrder 13 A b) : zeroSpace A 2≤U := by
  intro v hv
  by_contra out
  obtain ⟨vStable,P,pn,pd,pr⟩ :=
    H.low_multiplier_profile ha ho (d:=2) (Or.inl rfl) H.head.headBounds.1 hv out
  have firstCap : (X:K[X]).natDegree≤2 := by rw [natDegree_X]; decide
  obtain ⟨i,si,fp⟩ := quadratic_physical_port H ha ho hv vStable pn pd pr X X_ne_zero firstCap
  let x := nodes A i
  have xn : x≠0 := by simpa only [x,eval_X] using si
  let S : K[X] := X*(X-C x)
  have sd : S.natDegree=2 := by
    dsimp only [S]
    rw [natDegree_mul X_ne_zero (X_sub_C_ne_zero x),natDegree_X,natDegree_X_sub_C]
  obtain ⟨l,sl,sp⟩ := quadratic_physical_port H ha ho hv vStable pn pd pr
    S (mul_ne_zero X_ne_zero (X_sub_C_ne_zero x)) sd.le
  have sep : nodes A l≠0 ∧ nodes A l≠x := by
    simpa only [S,eval_mul,eval_sub,eval_X,eval_C,mul_ne_zero_iff,sub_ne_zero] using sl
  apply pn
  apply NativeCubicTwoPort.eq_zero_of_primitive_ports (P:=P) (pd.trans (by decide : 2≤3)) xn sep.1 sep.2
  · intro k
    exact fp k.val (by rw [natDegree_X]; have := k.isLt; omega)
  · intro k
    exact sp k.val (by rw [sd]; have := k.isLt; omega)

/-- The seed at grade two is paid and nonzero, so the maximal head radius
cannot be five, even before the grade-three exclusion is known. -/
theorem NativeMarkedEscapeChart.radius_le_four
    (H : NativeMarkedEscapeChart A b a G r U w)
    (ha : ∀ i j, i≤j → A i j=0) (ho : HasOrder 13 A b) : r≤4 := by
  have positive : 1≤finrank K (zeroSpace A 2) := zeroSpace_finrank ha ho (n:=1) (by decide)
  have lower := positive.trans (Submodule.finrank_mono (H.grade_two_le_core ha ho))
  have br := H.head.head.baseRank
  rw [H.head.five] at br
  omega

end
end RKResearch.Certified.Graded.ERK13NativeFirst
