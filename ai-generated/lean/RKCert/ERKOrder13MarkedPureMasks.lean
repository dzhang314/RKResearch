module
public import RKCert.ERKMarkedCausalContrast
public import RKCert.ERKOrder13FixedMomentGates
public import RKCert.ERKOrder13MarkedGhostScalar

@[expose] public section

/-! # Physical pure-mask obstructions and the simple marked Jacobi pencil -/
namespace RKCert.Paired.FiniteMidpoint
open RKCert.Paired RKCert.Paired.Clock RKCert.OneEscape RKCert.Endpoint
  RKCert.OrderTwelve Module Polynomial
open scoped Classical
variable {K:Type*} [Field K] [CharZero K] {s r:ℕ}
variable {A:Fin (s+1)→Fin (s+1)→K} {b:Vec K (s+1)}
variable {U:Submodule K (Vec K (s+1))} {w:Vec K (s+1)} {G P:K[X]}
set_option maxHeartbeats 3800000

omit [CharZero K] in
theorem marked13_mask_budget5 (H:MarkedHead A 6 1 r U w) (B:K[X]) (hd:B.natDegree<r) :
    weightedEval (nodes A) w B∈defectPlus A 1 5 := by
  rw [H.paid 5 le_rfl (by decide)]
  exact weighted_chain B hd

omit [CharZero K] in
theorem marked13_mask_budget6 (H:MarkedHead A 6 1 r U w) (B:K[X]) (hd:B.natDegree≤r) :
    weightedEval (nodes A) w B∈defectPlus A 1 6 := by
  rw [H.paid 6 (by decide) le_rfl]
  exact weighted_chain B (by omega)

theorem marked13_clean_alias_impossible (ha:StrictLower A)
    (S:Saturated A b 6 1) (M:Margin A b 6 1 1) (C:Chart13 A 1 5 r U w G)
    (alg:MulClosed U) (dis:∀i,Live U i→w i=0)
    (pn:P≠0) (pd:P.natDegree≤3) (pf:P∣G)
    (rep:∀i,w i≠0→w i=P.eval (nodes A i)) : False := by
  classical
  obtain ⟨e,he,ev⟩:=core_indicator alg
  have two:=C.marked.rTwo
  have h5:=marked13_mask_budget5 C.marked (X:K[X]) (by rw [natDegree_X];omega)
  have jd : ((X:K[X])*P).natDegree≤5 := by rw [natDegree_X_mul pn];omega
  obtain ⟨i,hi⟩:=firstContrast_exists S M C he (X:K[X]) pn X_ne_zero
    (jd.trans (by decide)) (Fplus_mono A 1 (by decide) h5)
  obtain ⟨off,wi,gin,nz⟩:=firstContrast_off C rep dis ev hi
  have u0:nodes A i≠0 := by
    intro z
    apply nz
    rw [eval_mul,eval_X,z,zero_mul]
  have h6:=markedResponse_paid ha C he (by decide) (X:K[X]) jd h5
  have flat:=marked13_off_six C h6 off wi
  rw [markedResponse_at_first ha hi] at flat
  obtain ⟨t,gt⟩:=marked13_alias_mesh C
  rw [dx5_mark_factor,smul_smul] at gt
  have qn : t*42≠0 := by
    intro z
    have d:=C.meshDegree
    rw [gt,z,zero_smul,natDegree_zero] at d
    omega
  have f : P∣(X*(dFivePoly:K[X])) := by
    rw [gt,smul_eq_C_mul] at pf
    exact ((isUnit_C.mpr (isUnit_iff_ne_zero.mpr qn)).dvd_mul_left).mp pf
  rw [gt,eval_smul,smul_eq_mul] at gin
  exact marked13_alias_primitive_ne_zero P _ pn f pd u0
    ((mul_eq_zero.mp gin).resolve_left qn) flat

noncomputable def markPencil (θ:K) : K[X] := dSixPoly+C θ*dFivePoly

theorem marked13_unaliased_mesh (C:Chart13 A 1 6 r U w G) :
    ∃ t θ:K,t≠0∧G=t•(X*markPencil θ) := by
  cases C.mesh with
  | marked x y e =>
    have yn:y≠0 := by
      intro yz
      have d:=C.meshDegree
      rw [e,yz,zero_smul,add_zero] at d
      have h:=natDegree_smul_le x (dx5:K[X])
      rw [dx5_degree] at h
      omega
    have nn:(56:K)*y≠0 := mul_ne_zero (by norm_num) yn
    refine ⟨56*y,42*x/(56*y),nn,?_⟩
    apply @Polynomial.funext K _ _ (Infinite.of_injective (fun n:ℕ=>(n:K)) Nat.cast_injective)
    intro z
    rw [e,dx5_mark_factor,dx6_as_dSix,←Nat.cast_smul_eq_nsmul K (56:ℕ) (X*dSixPoly:K[X])]
    simp only [eval_add,eval_mul,eval_smul,smul_eq_mul,eval_C,eval_X,markPencil]
    have fit :(56*y)*(42*x/(56*y))=42*x := by field_simp
    calc
      _ = (56*y)*(z*(dSixPoly:K[X]).eval z)+
          ((56*y)*(42*x/(56*y)))*(z*(dFivePoly:K[X]).eval z) := by rw [fit]; push_cast; ring
      _ = _ := by ring

theorem markPencil_degree (θ:K) : (markPencil θ).natDegree=6 := by
  have d := marked_noalias_degree_leading (K:=K) (a:=1) (b:=θ) one_ne_zero
  simpa only [map_one,one_mul,markPencil] using d.1

section Ordered
variable [LinearOrder K] [IsStrictOrderedRing K]

omit [LinearOrder K] [IsStrictOrderedRing K] in
private theorem pencil_wronskian (z:K) :
    (dFivePoly:K[X]).eval z*(dSixPoly:K[X]).derivative.eval z-
      (dSixPoly:K[X]).eval z*(dFivePoly:K[X]).derivative.eval z =
       1/28 + (5/28)*(2*z-1)^2 + (1/2)*(5*z^2-5*z+1)^2+
       (15/14)*(markD3:K[X]).eval z^2+(55/28)*(markD4:K[X]).eval z^2+
       (13/4)*(dFivePoly:K[X]).eval z^2 := by
  norm_num [dFivePoly,dSixPoly,markD3,markD4,Polynomial.derivative_add,Polynomial.derivative_sub,
    Polynomial.derivative_mul,Polynomial.derivative_X_pow,Polynomial.C_ofNat]
  ring

/-- Both conclusions concern actual roots only, even in non-real-closed
ordered fields. They need no root ordering or existence of a splitting. -/
theorem markPencil_simple_at (θ z:K) (hz:(markPencil θ).eval z=0) :
    (dFivePoly:K[X]).eval z≠0 ∧ (markPencil θ).derivative.eval z≠0 := by
  have W := pencil_wronskian z
  have pos : 0<(dFivePoly:K[X]).eval z*(dSixPoly:K[X]).derivative.eval z-
      (dSixPoly:K[X]).eval z*(dFivePoly:K[X]).derivative.eval z := by
    rw [W]
    positivity
  simp only [markPencil,eval_add,eval_mul,eval_C] at hz
  have dz:(dSixPoly:K[X]).eval z= -θ*(dFivePoly:K[X]).eval z := by linear_combination hz
  have eq : (dFivePoly:K[X]).eval z*(markPencil θ).derivative.eval z =
      (dFivePoly:K[X]).eval z*(dSixPoly:K[X]).derivative.eval z-
        (dSixPoly:K[X]).eval z*(dFivePoly:K[X]).derivative.eval z := by
    rw [markPencil,derivative_add,derivative_C_mul,eval_add,eval_mul,eval_C,dz]
    ring
  exact (mul_ne_zero_iff.mp (ne_of_gt (eq.symm ▸ pos)))

end Ordered
end RKCert.Paired.FiniteMidpoint
