module

public import RKCert.ReviewedNative.ERK13NativeMarkedLowProfile
public import RKCert.ReviewedNative.ERK13NativeMarkedSharedMode

import Mathlib.Tactic.Ring
import Lean.Elab.Tactic.Omega

@[expose] public section

/-! # Two actual preterminal ports for every off-core cubic defect

The residual is manufactured, not hypothesized. A global core match would
put a nonzero polynomial through degree six in the original grade-six
defect flag. The two pivots are found separately in stage order using
different polynomial masks. They need not have disjoint prefixes or
ordered clock values. All five identities use the same measured mode. -/

namespace RKResearch.Certified.Graded.ERK13NativeFirst

open RKResearch Polynomial Reverse Module RKCert.OneEscape RKCert.Endpoint
open scoped Matrix Classical
noncomputable section

variable {K : Type*} [Field K] [CharZero K]
variable {A : Matrix (Fin 19) (Fin 19) K} {b : Fin 19 → K}
variable {U : Submodule K (Fin 19 → K)} {w v : Fin 19 → K} {r a : ℕ} {G P : K[X]}

/-- The literal stage residual for a normalized multiplier test. -/
def markedProfileResidual (A : Matrix (Fin 19) (Fin 19) K) (v : Fin 19 → K)
    (P S : K[X]) : Fin 19 → K :=
  evalNodes A (S*P) - evalNodes A S*v

theorem markedProfileResidual_apply (S : K[X]) (i : Fin 19) :
    markedProfileResidual A v P S i =
      S.eval (nodes A i)*(P.eval (nodes A i)-v i) := by
  simp only [markedProfileResidual,Pi.sub_apply,Pi.mul_apply,evalNodes_apply,eval_mul,mul_sub]

/-- Every nonzero mask through degree three yields a literal preterminal
pivot. Only the actual multiplier profile and its native grade are assumed. -/
theorem NativeMarkedEscapeChart.pivot_for_polynomial_mask
    (H : NativeMarkedEscapeChart A b a G r U w)
    (ha : ∀ i j, i≤j → A i j=0) (ho : HasOrder 13 A b)
    (hv : v∈zeroSpace A 3) (vStable : U.map (diag v)≤U)
    (pd : P.natDegree≤3) (pn : P≠0)
    (pr : v*w-weightedEval (nodes A) w P∈U)
    (S : K[X]) (sd : S.natDegree≤3) (sn : S≠0) :
    ∃ k g, NativeMarkedPivot A b U w v (markedProfileResidual A v P S) G S k g := by
  let z := markedProfileResidual A v P S
  have vMask : MaskInvariant v U :=
    clock_mask_invariant (fun x hx => vStable (Submodule.mem_map_of_mem hx))
  have sp : (S*P).natDegree≤6 := natDegree_mul_le_of_le sd pd
  have vPay : evalNodes A S*v∈zeroSpace A 6 := by
    rw [mul_comm]
    exact zeroSpace_mul_treeSpace ho (m:=3) (n:=3) (by decide) hv
      (evalNodes_mem_treeSpace A S sd)
  have zTree : z∈treeSpace A 6 :=
    (treeSpace A 6).sub_mem (evalNodes_mem_treeSpace A _ sp) (zeroSpace_le_treeSpace A 6 vPay)
  have zOut : z∉U := by
    intro hz
    have zF : z∈zeroSpace A 6 := zeroSpace_mono A (by decide : 5≤6) (H.head.head.coreInside hz)
    have result : evalNodes A (S*P)∈zeroSpace A 6 := by
      simpa only [z,markedProfileResidual,sub_add_cancel] using (zeroSpace A 6).add_mem zF vPay
    exact mul_ne_zero sn pn (eval_eq_zero_of_coeff_separated
      (coeff_separated ho (q:=6) (by decide)) (S*P) sp result)
  exact H.first_joint_pivot ha ho vMask pr (markedProfileResidual_apply S) zTree zOut

/-- The bridge agrees literally with the five scalar rows of the Lobatto
test. All clocks here are coordinates of original stages. -/
structure NativeMarkedCubicPortPair (A : Matrix (Fin 19) (Fin 19) K)
    (G P J : K[X]) (scale : K) (k l : Fin 19) : Prop where
  firstBefore : k < Fin.last 18
  secondBefore : l < Fin.last 18
  firstNonzero : nodes A k ≠ 0
  secondNonzero : nodes A l ≠ 0
  distinct : nodes A k ≠ nodes A l
  firstMesh : G.eval (nodes A k) = 0
  secondMesh : G.eval (nodes A l) = 0
  firstLinear : (primitive (X*P)).eval (nodes A k) = 0
  firstQuadratic : (primitive (X^2*P)).eval (nodes A k) = 0
  firstCubic : (primitive (X^3*P)).eval (nodes A k) = scale*J.eval (nodes A k)
  secondQuadratic : (primitive (X^2*P)).eval (nodes A l) -
    nodes A k*(primitive (X*P)).eval (nodes A l) = 0
  secondCubic : (primitive (X^3*P)).eval (nodes A l) -
    nodes A k*(primitive (X^2*P)).eval (nodes A l) = scale*J.eval (nodes A l)

set_option maxHeartbeats 650000 in
theorem NativeMarkedEscapeChart.two_preterminal_cubic_ports
    (H : NativeMarkedEscapeChart A b a G r U w)
    (ha : ∀ i j, i≤j → A i j=0) (ho : HasOrder 13 A b)
    (early : coordinate (K:=K) (Fin.last 18)∈treeSpace A 7)
    (hv : v∈zeroSpace A 3) (vStable : U.map (diag v)≤U)
    (pd : P.natDegree≤3) (pn : P≠0)
    (pr : v*w-weightedEval (nodes A) w P∈U) :
    ∃ J : K[X], (J=0 ∨ NativeEarlyF7Mode A U w r J) ∧
    ∃ (scale : K) (k l : Fin 19), NativeMarkedCubicPortPair A G P J scale k l := by
  obtain ⟨J,jmode,scale,trace⟩ := H.early_cubic_shared_ports ha ho early hv pd
  obtain ⟨k,g₁,piv₁⟩ := H.pivot_for_polynomial_mask ha ho hv vStable pd pn pr X
    (by simp) X_ne_zero
  let t := nodes A k
  let S : K[X] := X*(X-C t)
  have sd : S.natDegree≤2 := natDegree_mul_le_of_le
    (show (X:K[X]).natDegree≤1 by simp) (show (X-C t).natDegree≤1 by simp)
  have sn : S≠0 := mul_ne_zero X_ne_zero (X_sub_C_ne_zero t)
  obtain ⟨l,g₂,piv₂⟩ := H.pivot_for_polynomial_mask ha ho hv vStable pd pn pr S
    (sd.trans (by decide)) sn
  let u := nodes A l
  have tNonzero : t≠0 := by simpa only [eval_X] using piv₁.maskNonzero
  have separated : u*(u-t)≠0 := by
    simpa only [S,u,eval_mul,eval_sub,eval_X,eval_C] using piv₂.maskNonzero
  obtain ⟨uNonzero,ud⟩ := mul_ne_zero_iff.mp separated
  have diff : t≠u := (sub_ne_zero.mp ud).symm
  have firstTrace (T : K[X]) (d : (T*X).natDegree≤3) :
      (primitive ((T*X)*P)).eval t = (scale*(T*X).coeff 3)*J.eval t :=
    trace X T _ g₁ k piv₁ (markedProfileResidual_apply X) d
  have secondTrace (T : K[X]) (d : (T*S).natDegree≤3) :
      (primitive ((T*S)*P)).eval u = (scale*(T*S).coeff 3)*J.eval u :=
    trace S T _ g₂ l piv₂ (markedProfileResidual_apply S) d
  have self2 : (X:K[X])*X = X^2 := (pow_two X).symm
  have self3 : (X:K[X])^2*X = X^3 := (pow_succ X 2).symm
  have T1 := firstTrace 1 (by simp)
  have T2 := firstTrace X (by simp [self2])
  have T3 := firstTrace (X^2) (by simp [self3])
  have U2 := secondTrace 1 (by simpa only [one_mul] using (sd.trans (by decide : 2≤3)))
  have U3 := secondTrace X (natDegree_mul_le_of_le (show (X:K[X]).natDegree≤1 by simp) sd)
  have s2 : S*P=X^2*P-t • (X*P) := by
    dsimp only [S]
    rw [Polynomial.smul_eq_C_mul]
    ring
  have s3 : (X*S)*P=X^3*P-t • (X^2*P) := by
    dsimp only [S]
    rw [Polynomial.smul_eq_C_mul]
    ring
  have sc : S.coeff 3=0 := coeff_eq_zero_of_natDegree_lt (sd.trans_lt (by decide : 2<3))
  have xsc : (X*S).coeff 3=1 := by
    have e : X*S=X^3-t • (X^2:K[X]) := by
      dsimp only [S]
      rw [Polynomial.smul_eq_C_mul]
      ring
    rw [e,coeff_sub,Polynomial.coeff_smul]
    simp [coeff_X_pow]
  refine ⟨J,jmode,scale,k,l,⟨piv₁.preterminal,piv₂.preterminal,tNonzero,uNonzero,diff,
    piv₁.meshRoot,piv₂.meshRoot,?_,?_,?_,?_,?_⟩⟩
  · simpa [coeff_X] using T1
  · simpa [self2,coeff_X_pow] using T2
  · simpa [self3,coeff_X_pow] using T3
  · simpa only [one_mul,s2,map_sub,map_smul,eval_sub,eval_smul,smul_eq_mul,sc,mul_zero,
      zero_mul] using U2
  · simpa only [s3,map_sub,map_smul,eval_sub,eval_smul,smul_eq_mul,xsc,mul_one] using U3

/-- No state from a different defect, proxy pivot or selected scalar root
is needed. At radius two the off-core premise itself contradicts the
checked two-step peel; at larger radii the complete profile is produced. -/
theorem NativeMarkedEscapeChart.physical_cubic_data_of_off_core
    (H : NativeMarkedEscapeChart A b a G r U w)
    (ha : ∀ i j, i≤j → A i j=0) (ho : HasOrder 13 A b)
    (early : coordinate (K:=K) (Fin.last 18)∈treeSpace A 7)
    (hv : v∈zeroSpace A 3) (out : v∉U) :
    ∃ (P J : K[X]) (scale : K) (k l : Fin 19),
      P≠0 ∧ P.natDegree≤3 ∧ (J=0 ∨ NativeEarlyF7Mode A U w r J) ∧
      NativeMarkedCubicPortPair A G P J scale k l := by
  by_cases room : 3≤r
  · obtain ⟨stable,P,pn,pd,pr⟩ :=
      H.low_multiplier_profile ha ho (d:=3) (Or.inr rfl) room hv out
    obtain ⟨J,jmode,scale,k,l,pair⟩ := H.two_preterminal_cubic_ports ha ho early hv stable pd pn pr
    exact ⟨P,J,scale,k,l,pn,pd,jmode,pair⟩
  · have eqr : r=2 := by have := H.head.headBounds.1; omega
    subst r
    exact (out (radius_two_grade_three_core H.head hv)).elim

end
end RKResearch.Certified.Graded.ERK13NativeFirst
