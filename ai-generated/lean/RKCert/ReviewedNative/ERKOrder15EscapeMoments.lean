module

public import RKCert.ReviewedNative.ERKOrder15Alias
public import RKCert.ReviewedNative.JacobiMomentPorts

@[expose] public section

/-! # Native probe payments for the two actual order-15 mesh inputs

This file uses the tree-free shared adjacent-moment signature. Its
import closure does not need any old RK definitions or Jacobi proof
that happens to import an archived geometric source. -/
namespace RKResearch.Certified.Graded

open RKResearch Reverse Polynomial
open scoped Matrix

variable {K : Type*} [Field K] {s : ℕ}
variable {A : Matrix (Fin (s+1)) (Fin (s+1)) K} {b : Fin (s+1)→K}

theorem order15_escape_origin (ha : ∀ i k,i ≤ k → A i k=0) (F : Order15PaidFrame A b)
    (P : K[X]) (hp : evalNodes A P∈order15FirstEscape A b) :
    P.coeff 0=0 := by
  have x : evalNodes A P 0=0 := origin_marked_defect ha (by have := F.size;omega) (F.escapePaid hp)
  have origin : nodes A 0=0 := by
    simp only [nodes,Matrix.mulVec,dotProduct]
    exact Finset.sum_eq_zero (fun j _=>by rw [ha 0 j (Fin.zero_le j),zero_mul])
  rwa [evalNodes_apply,origin,←coeff_zero_eq_eval_zero] at x

/-- Six adjacent unit moments on the actual first escape. They are the
shared order-15 input (r=5) for the signed Jacobi band, not a replay. -/
theorem order15_escape_adjacent_packet (ha : ∀ i k,i ≤ k → A i k=0)
    (ho : HasOrder A b 15) (F : Order15PaidFrame A b)
    (P : K[X]) (pd : P.natDegree≤8) (hp : evalNodes A P∈order15FirstEscape A b) :
    ∃ Q : K[X], P=X*Q ∧ Q.natDegree≤7 ∧ RKCert.ReviewedNative.JacobiMoments.MomentDifferences Q 5 := by
  obtain ⟨Q,hQ⟩:=Polynomial.X_dvd_iff.mpr (order15_escape_origin ha F P hp)
  have qd : Q.natDegree≤7 := by
    by_cases qz : Q=0
    · simp [qz]
    · rw [hQ,natDegree_X_mul qz] at pd
      omega
  refine ⟨Q,hQ,qd,?_⟩
  intro k
  have h := F.escapePaid hp
  have f : k.val+8+1≤15 := by have := k.isLt;omega
  have g : (k.val+1)+8+1≤15 := by have := k.isLt;omega
  have f₁ := paid_probe_marked_defect ha ho F.lastActive h k.val f
  have f₂ := paid_probe_marked_defect ha ho F.lastActive h (k.val+1) g
  rw [formalPrimitive_eq_native,formalPrimitive_eq_native,←hQ]
  rw [←probe_evalNodes ho P k.val (by omega),←probe_evalNodes ho P (k.val+1) (by omega)]
  exact f₁.trans f₂.symm

/-- When no terminal is charged, each of the seven paid moments itself
vanishes. In the marked branch only adjacent differences were used. -/
theorem order15_unmarked_escape_moments (ho : HasOrder A b 15) (F : Order15PaidFrame A b)
    (first : firstSeed A b≠0) (P : K[X]) (pd : P.natDegree≤8)
    (hp : evalNodes A P∈order15FirstEscape A b) (k : Fin 7) :
    (primitive (X^k.val*P)).eval 1=0 := by
  have p : evalNodes A P∈zeroSpace A 8 := by
    simpa only [markedDefectSpace,terminalMark,ite_eq_right first,sup_bot_eq] using F.escapePaid hp
  have k7 := k.isLt
  rw [←probe_evalNodes ho P k.val (by omega)]
  exact probe_zeroSpace ho (by omega) p

end RKResearch.Certified.Graded
