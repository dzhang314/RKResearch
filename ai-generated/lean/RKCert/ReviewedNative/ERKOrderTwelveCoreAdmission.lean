module

public import RKCert.ReviewedNative.ERKOrderTwelveForwardStaircase
public import RKCert.ReviewedNative.JointPrefixDetector
public import RKCert.ReviewedNative.ERKHeadContrast

public section

/-! # The native quadratic defect grade belongs to the order-12 core

Three formal tests on the same detected nonzero physical clock exclude
an outside quadratic multiplier. The low-degree case needs no ghost or
mesh polynomial, and no sign or order on the coefficient field. -/
namespace RKResearch.Certified.Graded.ERK12

open RKResearch Module Polynomial Reverse RKCert.Endpoint RKCert.OneEscape RKCert.ReviewedNative.TwoKnot
open scoped Matrix

variable {K : Type*} [Field K] [CharZero K] {s : ℕ}
variable {A : Matrix (Fin (s+1)) (Fin (s+1)) K} {b : Fin (s+1) → K}

omit [CharZero K] in
private theorem weighted_grade (ho : HasOrder A b 12)
    {v : Fin (s+1) → K} {m n : ℕ} (hv : v∈zeroSpace A m)
    (P : K[X]) (d : P.natDegree≤n) (pay : n+1≤12) :
    weightedEval (nodes A) v P∈zeroSpace A (m+n) := by
  have e : weightedEval (nodes A) v P=v*evalNodes A P := by ext i; simp [mul_comm]
  rw [e]
  exact zeroSpace_mul_treeSpace ho pay hv (evalNodes_mem_treeSpace A P d)

/-- The genuine second defect grade is inside the actual invariant core.
The proof uses the full three probes at a single physical first failure. -/
theorem grade_two_in_core (ha : ∀ i k, i ≤ k → A i k=0) (ho : HasOrder A b 12)
    (S : Saturation A b) (T : TerminalBand A b) {r : ℕ} {U : Submodule K (Fin (s+1) → K)} {w : Fin (s+1) → K}
    (H : ForwardStaircase A r U w) : zeroSpace A 2≤U := by
  classical
  intro v hv
  by_contra outside
  have stable := grade_two_multiplier_stable ho S T H hv
  obtain ⟨P,pnz,deg,fit⟩ := grade_two_multiplier_profile ho S T H hv outside
  let c := nodes A
  let z := evalNodes A (X*P)-weightedEval c v X
  have val (i : Fin (s+1)) : z i=X.eval (c i)*(P.eval (c i)-v i) := by
    simp [z,c,mul_sub]
  have sep : PolySeparated A 6 := PolySeparated.of_coeff
    (explicit_coeff_separated ha ho (q:=6) (by decide))
  have nz : z∉U := by
    intro hz
    have vz := weighted_grade ho hv (X:K[X]) (n:=1) (by simp) (by decide)
    change weightedEval c v X∈zeroSpace A (2+1) at vz
    have e := (zeroSpace A 6).add_mem (zeroSpace_mono A (by decide : 5≤6) (H.initial.coreInside hz))
      (zeroSpace_mono A (by decide : 2+1≤6) vz)
    have d : (X*P).natDegree≤6 :=
      natDegree_mul_le.trans (by rw [natDegree_X]; omega)
    exact (mul_ne_zero X_ne_zero pnz) (sep _ d (by simpa only [z,sub_add_cancel] using e))
  have cMask : MaskInvariant c U := clock_mask_invariant
    (fun u hu => H.initial.coreStable (Submodule.mem_map_of_mem hu))
  have vMask : MaskInvariant v U := clock_mask_invariant
    (fun u hu => stable (Submodule.mem_map_of_mem hu))
  obtain ⟨k,g,hg,before,live,detect⟩ :=
    HeadFiber.joint_prefix_detector cMask vMask P X fit val nz
  have active : c k≠0 := by simpa only [eval_X] using live
  have tests (q : Fin 3) : (primitive (X^(q.val+1)*P)).eval (c k)=0 := by
    let R : K[X] := X^q.val
    let Q : K[X] := X^(q.val+1)
    let B := Q*P
    have dr : R.natDegree≤2 := by simp only [R,natDegree_X_pow]; have := q.isLt; omega
    have dq : Q.natDegree≤3 := by simp only [Q,natDegree_X_pow]; have := q.isLt; omega
    have db : B.natDegree≤5 := natDegree_mul_le.trans (by omega)
    let feeder := weightedEval c g R+weightedEval c v Q
    have gu : weightedEval c g R∈U := by
      have eq : weightedEval c g R=fun i=>R.eval (c i)*g i := by ext i; simp
      rw [eq]
      exact mulByBlock_mem c cMask (fun x=>R.eval x) hg
    have feed : feeder∈zeroSpace A 5 := (zeroSpace A 5).add_mem
      (H.initial.coreInside gu) (weighted_grade ho hv Q dq (by decide))
    let y := evalNodes A (primitive B)-mat A (evalNodes A B)+mat A feeder
    have low : y∈zeroSpace A 6 := (zeroSpace A 6).add_mem
      (by simpa only [neg_sub] using (zeroSpace A 6).neg_mem (primitive_defect A B db))
      (mat_zeroSpace_charZero A 5 feed)
    have hy : y∈chain (diag c) U w (r+2) :=
      H.cut ▸ (show zeroSpace A 6≤escape7 A from le_sup_left) low
    apply detect hy ((primitive B).eval (c k))
    intro i hi same _
    have e : mat A (evalNodes A B) i=mat A feeder i := by
      have h := causal_mat ha i (evalNodes A B-feeder) (by
        intro l hl
        change l.val < i.val at hl
        have lk : l<k := by change l.val<k.val; omega
        rw [Pi.sub_apply,sub_eq_zero,evalNodes_apply]
        simp only [feeder,Pi.add_apply,weightedEval_apply,before l lk,val,eval_X,B,eval_mul,
          Q,R,eval_pow,pow_succ]
        ring)
      simpa only [map_sub,Pi.sub_apply,sub_eq_zero] using h
    change (primitive B).eval (c i)-mat A (evalNodes A B) i+mat A feeder i=_
    rw [e,sub_add_cancel,same]
  let a : Fin 3 → K := fun i => P.coeff i.val
  have rep : ofFn 3 a=P := by
    change ofFn 3 (toFn 3 P)=P
    exact ofFn_comp_toFn_eq_id_of_natDegree_lt (by omega)
  let u := c k
  let d : Fin 3 → K := fun i => a i*u^i.val
  have hilbert (q : Fin 3) :
      (∑ j : Fin 3, d j / ((q.val+j.val+2:ℕ):K))=0 := by
    have e := tests q
    rw [←rep,HeadContrast.primitive_monomial_moment] at e
    change moment a u (q.val+1)=0 at e
    have f : u^(q.val+2)*(∑ j : Fin 3, d j/((q.val+j.val+2:ℕ):K)) =
        moment a u (q.val+1) := by
      rw [moment,Finset.mul_sum]
      apply Finset.sum_congr rfl
      intro j _
      have en : j.val+(q.val+1)+1=j.val+(q.val+2) := by omega
      rw [en,pow_add u j.val (q.val+2),show j.val+(q.val+2)=q.val+j.val+2 by omega]
      dsimp only [d]
      ring
    exact (mul_eq_zero.mp (f.trans e)).resolve_left (pow_ne_zero _ active)
  have all := moments_detect ho (d:=2) (by decide) (by decide)
    (fun i j : Fin 3 => by have := i.isLt; have := j.isLt; omega) d hilbert
  have za : a=0 := by
    ext j
    exact (mul_eq_zero.mp (all j)).resolve_right (pow_ne_zero _ active)
  exact pnz (by rw [←rep,za,map_zero])

end RKResearch.Certified.Graded.ERK12
