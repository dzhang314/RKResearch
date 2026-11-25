module

public import RKCert.ReviewedNative.NativeJointPrimitivePort
public import RKCert.ReviewedNative.NativeCubicTwoPort
import Mathlib.Tactic.Ring
import Lean.Elab.Tactic.Omega

@[expose] public section

/-! # Paid grade-three defects cannot carry an ordinary cubic head profile

The two primitive knots come from original matrix chronology. Their
mask degrees, not an assumed exact selector, earn each paid test.
-/
namespace RKResearch.Certified.Graded.ERK13NativeFirst

open RKResearch Polynomial RKCert.OneEscape RKCert.Endpoint
open scoped Classical Matrix
noncomputable section
variable {K : Type*} [Field K] [CharZero K] {s n : ℕ}
variable {A : Matrix (Fin s) (Fin s) K} {b : Fin s→K}
variable {U : Submodule K (Fin s→K)} {w v : Fin s→K} {P : K[X]}

/-- The cubic port only pays X-divisible masks, so a grade-four
multiplier whose first clock shift is also grade-four is admissible. -/
theorem ordinary_cubic_profile_impossible_of_xpaid
    (ha : ∀ i j,i≤j → A i j=0)
    (sep : PolySeparated A 6) (core : U≤zeroSpace A 6)
    (stable : U.map (diag (nodes A))≤U) (vstable : U.map (diag v)≤U)
    (cover : zeroSpace A 7≤chain (diag (nodes A)) U w n)
    (product : ∀ R : K[X], (X:K[X])∣R → R.natDegree≤3 → evalNodes A R*v∈zeroSpace A 6)
    (pn : P≠0) (pd : P.natDegree≤3)
    (profile : v*w-weightedEval (nodes A) w P∈U) : False := by
  have physical (S : K[X]) (sn : S≠0) (sx : (X:K[X])∣S) (sd : S.natDegree≤2) :
      ∃ i : Fin s, S.eval (nodes A i)≠0 ∧
        ∀ k : ℕ, k+S.natDegree≤3 →
          (primitive (X^k*(S*P))).eval (nodes A i)=0 := by
    have outside : evalNodes A (S*P)-evalNodes A S*v∉U := by
      intro pay
      have m := (zeroSpace A 6).add_mem (core pay) (product S sx (by omega))
      rw [sub_add_cancel] at m
      exact mul_ne_zero sn pn (sep (S*P) (by
        have h := natDegree_mul_le (p:=S) (q:=P)
        omega) m)
    obtain ⟨i,live,ports⟩ := HeadFiber.joint_primitive_ports ha core stable
      vstable cover P S profile outside
    refine ⟨i,live,fun k hk=>ports (X^k) ?_ (product _ ?_ ?_)⟩
    · have h₁ := natDegree_mul_le (p:=X^k) (q:=S*P)
      have h₂ := natDegree_mul_le (p:=S) (q:=P)
      rw [natDegree_X_pow] at h₁
      omega
    · obtain ⟨T,eq⟩ := sx
      exact ⟨X^k*T,by rw [eq]; ac_rfl⟩
    · have h := natDegree_mul_le (p:=X^k) (q:=S)
      rw [natDegree_X_pow] at h
      omega
  obtain ⟨i,ic,first⟩ := physical X X_ne_zero dvd_rfl (by simp)
  let a := nodes A i
  have ha0 : a≠0 := by simpa only [a,eval_X] using ic
  let S : K[X] := X*(X-C a)
  have sn : S≠0 := mul_ne_zero X_ne_zero (X_sub_C_ne_zero _)
  have sd : S.natDegree=2 := by
    dsimp only [S]
    rw [natDegree_mul X_ne_zero (X_sub_C_ne_zero _),natDegree_X,natDegree_X_sub_C]
  obtain ⟨j,jc,second⟩ := physical S sn ⟨X-C a,rfl⟩ sd.le
  have jc' : nodes A j≠0 ∧ nodes A j≠a := by
    simp only [S,eval_mul,eval_sub,eval_X,eval_C,mul_ne_zero_iff,sub_ne_zero] at jc
    exact jc
  apply pn
  apply NativeCubicTwoPort.eq_zero_of_primitive_ports pd ha0 jc'.1 jc'.2
  · intro k
    exact first k.val (by rw [natDegree_X]; have :=k.isLt; omega)
  · intro k
    exact second k.val (by rw [sd]; have :=k.isLt; omega)

/-- The original grade-three interface is the same cubic obstruction;
its paid products do not need to use the X-divisibility hypothesis. -/
theorem ordinary_cubic_profile_impossible
    (ha : ∀ i j,i≤j → A i j=0) (ho : HasOrder 13 A b)
    (sep : PolySeparated A 6) (core : U≤zeroSpace A 6)
    (stable : U.map (diag (nodes A))≤U) (vstable : U.map (diag v)≤U)
    (cover : zeroSpace A 7≤chain (diag (nodes A)) U w n)
    (hv : v∈zeroSpace A 3) (pn : P≠0) (pd : P.natDegree≤3)
    (profile : v*w-weightedEval (nodes A) w P∈U) : False := by
  apply ordinary_cubic_profile_impossible_of_xpaid ha sep core stable vstable cover _ pn pd profile
  intro R _ rd
  have h := zeroSpace_mul_treeSpace (m:=3) (n:=3) ho (by decide)
    hv (evalNodes_mem_treeSpace A R rd)
  simpa only [mul_comm] using h

end
end RKResearch.Certified.Graded.ERK13NativeFirst
