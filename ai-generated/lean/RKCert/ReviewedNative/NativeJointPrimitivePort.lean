module

public import RKCert.ReviewedNative.JointPrefixDetector
public import RKCert.ReviewedNative.CausalStage
import Mathlib.Tactic.Abel
import Mathlib.Tactic.Ring
import Lean.Elab.Tactic.Omega

@[expose] public section

/-! # Transport native primitive defects through a joint physical prefix

The core need only be pointwise invariant under the clock and one
multiplier. No unitality, product closure, head normalization, or
evaluation matching on a nonphysical point is assumed.
-/
namespace RKResearch.Certified.Graded.HeadFiber

open Polynomial RKCert.OneEscape RKCert.Endpoint
open scoped Classical Matrix
noncomputable section
variable {K : Type*} [Field K] [CharZero K] {s m n : ℕ}
variable {A : Matrix (Fin s) (Fin s) K}
variable {U : Submodule K (Fin s→K)} {w v : Fin s→K}

/-- On the first actual joint block where S(c)(P(c)−v) cannot match the
invariant core, all simultaneously paid primitive masks vanish at that
same original row. The polynomial band and matrix advance are literal. -/
theorem joint_primitive_ports
    (ha : ∀ i j,i≤j → A i j=0)
    (core : U≤zeroSpace A m)
    (stable : U.map (diag (nodes A))≤U) (vstable : U.map (diag v)≤U)
    (cover : zeroSpace A (m+1)≤chain (diag (nodes A)) U w n)
    (P S : K[X]) (profile : v*w-weightedEval (nodes A) w P∈U)
    (outside : evalNodes A (S*P)-evalNodes A S*v∉U) :
    ∃ i : Fin s, S.eval (nodes A i)≠0 ∧
      ∀ R : K[X], (R*(S*P)).natDegree≤m →
        evalNodes A (R*S)*v∈zeroSpace A m →
        (primitive (R*(S*P))).eval (nodes A i)=0 := by
  let c := nodes A
  let z := evalNodes A (S*P)-evalNodes A S*v
  have cInv (x : Fin s→K) (hx : x∈U) : diag c x∈U :=
    stable (Submodule.mem_map_of_mem hx)
  have vInv (x : Fin s→K) (hx : x∈U) : diag v x∈U :=
    vstable (Submodule.mem_map_of_mem hx)
  have value (i : Fin s) : z i=S.eval (c i)*(P.eval (c i)-v i) := by
    simp [z,c,mul_sub]
  obtain ⟨i,g,hg,pre,iS,detect⟩ := joint_prefix_detector
    (clock_mask_invariant cInv) (clock_mask_invariant vInv) P S profile value outside
  refine ⟨i,iS,fun R d adv => ?_⟩
  let T : K[X] := R*(S*P)
  let e : Fin s→K := evalNodes A R*(z-g)
  let feed : Fin s→K := evalNodes A (R*S)*v+evalNodes A R*g
  let y : Fin s→K := evalNodes A (primitive T)-mat A e
  have gr : evalNodes A R*g∈U := clock_function_mem cInv R.eval hg
  have feedPay : feed∈zeroSpace A m := (zeroSpace A m).add_mem adv (core gr)
  have eEq : e=evalNodes A T-feed := by
    ext j
    simp only [e,feed,z,T,Pi.mul_apply,Pi.add_apply,Pi.sub_apply,evalNodes_apply,eval_mul]
    ring
  have yEq : y=mat A feed-(mat A (evalNodes A T)-evalNodes A (primitive T)) := by
    dsimp only [y]
    rw [eEq,map_sub]
    abel
  have yPay : y∈zeroSpace A (m+1) := by
    rw [yEq]
    exact (zeroSpace A (m+1)).sub_mem (mat_zeroSpace_charZero A m feedPay)
      (primitive_defect A T d)
  have causal (j : Fin s) (hj : j.val < i.val + 1) : mat A e j=0 := by
    apply causal_mat ha j e
    intro t ht
    have ti : t < i := by change t.val < j.val at ht; change t.val < i.val; omega
    simp only [e,Pi.mul_apply,Pi.sub_apply,pre t ti,sub_self,mul_zero]
  change (primitive T).eval (c i)=0
  apply detect (cover yPay) ((primitive T).eval (c i))
  intro j hj hclock _
  simp only [y,Pi.sub_apply,evalNodes_apply,causal j hj,sub_zero]
  exact congrArg (fun t=> (primitive T).eval t) hclock

end
end RKResearch.Certified.Graded.HeadFiber
