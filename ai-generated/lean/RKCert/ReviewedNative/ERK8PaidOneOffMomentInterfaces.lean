module
public import RKCert.ReviewedNative.ERK8PaidArithmetic

public import RKCert.ReviewedNative.ERK8PaidOneOffScalars
public import RKCert.ReviewedNative.ERK8PaidOneOffPhysicalPrefix
public import RKCert.ReviewedNative.ERKTaggedHorizonSupport
public import RKCert.ReviewedNative.ERK8PaidOneOffClosing

@[expose] public section

/-! Native paid p8 moment projections over the actual Fin 10
tableau. Arithmetic budget is explicit at each call. -/
namespace RKResearch.Certified.Graded.OneOff.PaidProof.Eight

open RKResearch Polynomial Module Reverse
open scoped BigOperators Matrix Classical

variable {K : Type*} [Field K] [EightUnits K]
variable {A : Matrix (Fin 10) (Fin 10) K} {b : Fin 10 → K}

theorem zero_origin_of_F5 (ha : ∀ i j, i≤j → A i j=0)
    {P : K[X]} (hp : evalNodes A P∈zeroSpace A 5) : P.eval 0=0 := by
  have nc : nodes A (0:Fin 10)=0 := by
    simp only [nodes,Matrix.mulVec,dotProduct,Pi.one_apply,mul_one]
    exact Finset.sum_eq_zero (fun j _ => ha _ _ (Fin.zero_le j))
  have e : evalNodes A P (0:Fin 10)=0 := origin_zeroSpace ha 5 hp
  simpa only [evalNodes_apply,nc] using e

theorem zero_F5_poly_le_three (ha : ∀ i j, i≤j → A i j=0) (ho : HasOrder 8 A b)
    {P : K[X]} (deg : P.natDegree≤3) (hp : evalNodes A P∈zeroSpace A 5) : P=0 := by
  obtain ⟨Q,e⟩ := X_dvd_iff.mpr
    ((coeff_zero_eq_eval_zero P).trans (zero_origin_of_F5 ha hp))
  by_cases q0 : Q=0
  · simp [e,q0]
  have qDeg : Q.natDegree≤2 := by
    have d := natDegree_mul X_ne_zero q0
    rw [←e,natDegree_X] at d
    omega
  have test (k : Fin 3) :
      (∑ j : Fin 3, Q.coeff j.val/((k.val+j.val+2:ℕ):K))=0 :=
    ERKTaggedHorizon.anchor_probe_coeff ho Q (n:=2) (k:=k.val) qDeg (by have hk := k.isLt; omega)
      (by rw [←e]; exact probe_zeroSpace ho (by have hk := k.isLt; omega) hp)
  have all (j : Fin 3) : Q.coeff j.val=0 :=
    moments_detect ho (n:=3) (d:=2) (by decide) (by decide)
      (fun i j => by have hi := i.isLt; have hj := j.isLt; omega)
      (fun i : Fin 3 => Q.coeff i.val) test j
  have zero : Q=0 := by
    ext n
    rw [coeff_zero]
    by_cases g : n<3
    · exact all ⟨n,g⟩
    · exact coeff_eq_zero_of_natDegree_lt (by omega)
  simp [e,zero]

/-- Used ONLY for the profile kernel, not for a generic grade-five defect.
The actual endpoint observation is a proved hypothesis of this helper. -/
theorem zero_F5_low_top_kernel (ha : ∀ i j, i≤j → A i j=0) (ho : HasOrder 8 A b)
    {P : K[X]} (deg : P.natDegree≤4) (hp : evalNodes A P∈zeroSpace A 5)
    (atOne : P.eval 1=0) : P=0 := by
  obtain ⟨B,e⟩ := X_dvd_iff.mpr
    ((coeff_zero_eq_eval_zero P).trans (zero_origin_of_F5 ha hp))
  have B1 : B.eval 1=0 := by simpa only [e,eval_mul,eval_X,one_mul] using atOne
  obtain ⟨Q,q⟩ := dvd_iff_isRoot.mpr (show B.IsRoot 1 from B1)
  by_cases q0 : Q=0
  · simp [e,q,q0]
  have eq : P=(X^2-X)*Q := by
    rw [e,q,C_1]
    eight_ring K
  have du : ((X:K[X])*(X-C 1)).natDegree=2 := by
    rw [natDegree_mul X_ne_zero (X_sub_C_ne_zero _),natDegree_X,natDegree_X_sub_C]
  have pq : P=(X*(X-C 1))*Q := by
    rw [e,q,mul_assoc]
  have qd : Q.natDegree≤2 := by
    have v := natDegree_mul (mul_ne_zero X_ne_zero (X_sub_C_ne_zero (1:K))) q0
    rw [←pq,du] at v
    omega
  have dec := ERK8PaidField.beta_cubic_from_probes_paid ho Q (qd.trans (by decide)) (fun k=>by
    rw [←eq]
    exact probe_zeroSpace ho (by have ht := k.isLt; omega) hp)
  have top : Q.coeff 3=0 := coeff_eq_zero_of_natDegree_lt (qd.trans_lt (by decide))
  rw [top,map_zero,zero_mul] at dec
  simp [eq,dec]

theorem shiftProbe (A : Matrix (Fin 10) (Fin 10) K) (b v : Fin 10 → K) (k : ℕ) :
    probe A b k (diag (nodes A) v)=probe A b (k+1) v := by
  simp only [probe,row_apply,dotProduct,diag_apply,pow_succ]
  apply Finset.sum_congr rfl
  intro j _
  eight_ring K

/-- The E4 terminal polynomial decoder after subtracting its earned F4
defects. Only k=0,1,2,3 are paid on F4. -/
theorem terminalPolynomial (ho : HasOrder 8 A b) {P : K[X]} (deg : P.natDegree≤4)
    (p0 : P.eval 0=0) (p1 : P.eval 1=1) (w : K)
    (paid : ∀ k : Fin 4, probe A b k.val (evalNodes A P)=w) :
    P=X*(C (14:K)*lobattoCubic) := by
  exact EightPaid.terminal_polynomial_paid ho deg p0 p1 w paid

end RKResearch.Certified.Graded.OneOff.PaidProof.Eight
