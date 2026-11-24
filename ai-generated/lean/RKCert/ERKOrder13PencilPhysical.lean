module
public import RKCert.ERKOrder13MarkedPureMasks

@[expose] public section

/-! # Degree completion with two genuinely causal omitted clocks
The complementary factor is cut out using the *already detected* clocks.
No roots beyond those clocks have to exist over the field. Multiplying
both original masks by the remaining complementary factor preserves
their chronology and gives one simultaneous quartic scalar gate.
-/
namespace RKCert.Paired.FiniteMidpoint
open RKCert.Paired RKCert.Paired.Clock RKCert.OneEscape RKCert.Endpoint
  RKCert.OrderTwelve Module Polynomial
variable {K:Type*} [Field K] [LinearOrder K] [IsStrictOrderedRing K] {s r:ℕ}
variable {A:Fin (s+1)→Fin (s+1)→K} {b:Vec K (s+1)}
variable {U:Submodule K (Vec K (s+1))} {w:Vec K (s+1)} {G P:K[X]}
set_option maxHeartbeats 4200000

omit [LinearOrder K] [IsStrictOrderedRing K] in
/-- Strip the unavoidable clock-zero factor before identifying an omitted
root. A true double zero of x·markPencil causes no special case. -/
theorem marked13_base_factor (F P:K[X]) (pn:P≠0) (pf:P∣X*F) :
    ∃ B R:K[X], B≠0 ∧ R≠0 ∧ B.natDegree≤1 ∧ B*P=X*R ∧ R∣F := by
  by_cases z:P.eval 0=0
  · obtain ⟨R,fit⟩ : (X:K[X])∣P := by simpa using (dvd_iff_isRoot (a:=(0:K))).mpr z
    have rn:R≠0 := fun r0=>pn (by rw [fit,r0,mul_zero])
    obtain ⟨Q,qfit⟩:=pf
    have f : F=R*Q := by
      apply mul_left_cancel₀ X_ne_zero
      simpa only [fit,mul_assoc] using qfit
    exact ⟨1,R,one_ne_zero,rn,by simp,by simpa only [one_mul] using fit,⟨Q,f⟩⟩
  · obtain ⟨Q,fit⟩:=pf
    have eq:=congrArg (Polynomial.eval (0:K)) fit
    rw [eval_mul,eval_X,zero_mul,eval_mul] at eq
    have q0:Q.eval 0=0 := (mul_eq_zero.mp eq.symm).resolve_left z
    obtain ⟨R,rf⟩ : (X:K[X])∣Q := by simpa using (dvd_iff_isRoot (a:=(0:K))).mpr q0
    have f:F=P*R := by
      apply mul_left_cancel₀ X_ne_zero
      calc
        _ = P*(X*R) := by rwa [←rf]
        _ = _ := by ring
    exact ⟨X,P,X_ne_zero,pn,by simp,rfl,⟨R,f⟩⟩

omit [LinearOrder K] [IsStrictOrderedRing K] in
private theorem cofactor_at_simple {F Q:K[X]} {z:K}
    (hf:F=(X-C z)*Q) (hn:F.derivative.eval z≠0) : Q.eval z≠0 := by
  simpa only [hf,derivative_mul,derivative_sub,derivative_X,derivative_C,sub_zero,eval_add,
    eval_mul,eval_one,eval_sub,eval_X,eval_C,sub_self,zero_mul,one_mul,add_zero] using hn

theorem marked13_complete_factor (θ u v:K) (R:K[X]) (rf:R∣markPencil θ)
    (ru:R.eval u≠0) (rv:R.eval v≠0) (vu:v≠u)
    (hu:(markPencil θ).eval u=0) (hv:(markPencil θ).eval v=0) :
    ∃ L F:K[X], L.eval u≠0 ∧ L.eval v≠0 ∧
       F=L*R ∧ F.natDegree=4 ∧ markPencil θ=(X-Polynomial.C u)*(X-Polynomial.C v)*F := by
  obtain ⟨Q,hQ⟩:=rf
  have qu:Q.eval u=0 := by rw [hQ,eval_mul] at hu;exact (mul_eq_zero.mp hu).resolve_left ru
  have qv:Q.eval v=0 := by
    have e:=congrArg (Polynomial.eval v) hQ
    rw [hv,eval_mul] at e
    exact (mul_eq_zero.mp e.symm).resolve_left rv
  obtain ⟨S,hS⟩:=dvd_iff_isRoot.mpr qu
  have sv:S.eval v=0 := by
    rw [hS,eval_mul,eval_sub,eval_X,eval_C] at qv
    exact (mul_eq_zero.mp qv).resolve_left (sub_ne_zero.mpr vu)
  obtain ⟨L,hL⟩:=dvd_iff_isRoot.mpr sv
  let F:=L*R
  have he:markPencil θ=(X-Polynomial.C u)*(X-Polynomial.C v)*F := by rw [hQ,hS,hL];dsimp [F];ring
  have nv:markPencil θ≠0 := by
    intro ee
    have d:=markPencil_degree θ
    rw [ee,natDegree_zero] at d
    omega
  have nf:F≠0 := fun z=>nv (by rw [he,z,mul_zero])
  have fd:=markPencil_degree θ
  rw [he,natDegree_mul (mul_ne_zero (X_sub_C_ne_zero _) (X_sub_C_ne_zero _)) nf,
    natDegree_mul (X_sub_C_ne_zero _) (X_sub_C_ne_zero _),natDegree_X_sub_C,natDegree_X_sub_C] at fd
  have xu : markPencil θ=(X-C u)*((X-C v)*F) := by rw [he,mul_assoc]
  have xv : markPencil θ=(X-C v)*((X-C u)*F) := by rw [he];ring
  have du:=cofactor_at_simple xu (markPencil_simple_at θ u hu).2
  have dv:=cofactor_at_simple xv (markPencil_simple_at θ v hv).2
  rw [eval_mul,show F=L*R by rfl,eval_mul] at du dv
  exact ⟨L,F,((mul_ne_zero_iff.mp du).2 |> mul_ne_zero_iff.mp).1,
    ((mul_ne_zero_iff.mp dv).2 |> mul_ne_zero_iff.mp).1,rfl,by omega,he⟩

/-- Scalar conclusion of any clean invariant-core pure marked chart at
the saturated unaliased degree. A single τ serves both high tests. -/
theorem marked13_filled_pair (ha:StrictLower A) (ho:HasTreeOrderAtLeast A b 13)
    (S:Saturated A b 6 1) (M:Margin A b 6 1 1) (C:Chart13 A 1 6 r U w G)
    (alg:MulClosed U) (dis:∀i,Live U i→w i=0)
    (pn:P≠0) (pd:P.natDegree+r=6) (pf:P∣G)
    (rep:∀i,w i≠0→w i=P.eval (nodes A i)) :
    ∃ θ u v τ:K,∃ F:K[X],
      u≠0 ∧ v≠0 ∧ v≠u ∧ (dFivePoly:K[X]).eval u≠0 ∧
      markPencil θ=(X-Polynomial.C u)*(X-Polynomial.C v)*F ∧
      (primitive (X*F)).eval u=0 ∧
      (primitive (X*(X*F))).eval u=τ*u*(dFivePoly:K[X]).eval u ∧
      (primitive ((X-Polynomial.C u)*(X*F))).eval v=τ*v*(dFivePoly:K[X]).eval v := by
  classical
  obtain ⟨e,he,ev⟩:=core_indicator alg
  obtain ⟨t,θ,tn,mesh⟩:=marked13_unaliased_mesh C
  have pdiv:P∣X*markPencil θ := by
    rw [mesh,smul_eq_C_mul] at pf
    exact ((isUnit_C.mpr (isUnit_iff_ne_zero.mpr tn)).dvd_mul_left).mp pf
  obtain ⟨B,R,bn,rn,bd,base,rdiv⟩:=marked13_base_factor (markPencil θ) P pn pdiv
  have rtwo:=C.marked.rTwo
  obtain ⟨i,hi⟩:=firstContrast_exists S M C he B pn bn (natDegree_mul_le.trans (by omega))
    (marked13_mask_budget6 C.marked B (by omega))
  let u:=nodes A i
  obtain ⟨oi,wi,gi,bi⟩:=firstContrast_off C rep dis ev hi
  have ui : u*R.eval u≠0 := by rw [base,eval_mul,eval_X] at bi;exact bi
  let E : K[X] := (X-Polynomial.C u)*B
  have En:E≠0 := mul_ne_zero (X_sub_C_ne_zero _) bn
  have Ed:E.natDegree≤2 := by
    dsimp [E]
    rw [natDegree_mul (X_sub_C_ne_zero _) bn,natDegree_X_sub_C]
    omega
  obtain ⟨j,hj⟩:=firstContrast_exists S M C he E pn En (natDegree_mul_le.trans (by omega))
    (marked13_mask_budget6 C.marked E (by omega))
  let v:=nodes A j
  obtain ⟨oj,wj,gj,bj⟩:=firstContrast_off C rep dis ev hj
  have vj : (v-u)*(v*R.eval v)≠0 := by
    change (E*P).eval v≠0 at bj
    rw [show E*P=(X-Polynomial.C u)*(B*P) by dsimp [E];ring,base,
      eval_mul,eval_mul,eval_X,eval_sub,eval_X,eval_C] at bj
    exact bj
  have un:= (mul_ne_zero_iff.mp ui).1
  have vn:= (mul_ne_zero_iff.mp (mul_ne_zero_iff.mp vj).2).1
  have vu:v≠u := sub_ne_zero.mp (mul_ne_zero_iff.mp vj).1
  have pencilRoot {z:K} (zn:z≠0) (h:G.eval z=0) : (markPencil θ).eval z=0 := by
    rw [mesh,eval_smul,smul_eq_mul,eval_mul,eval_X] at h
    exact (mul_eq_zero.mp ((mul_eq_zero.mp h).resolve_left tn)).resolve_left zn
  have hu:=pencilRoot un gi
  have hv:=pencilRoot vn gj
  obtain ⟨L,F,lu,lv,fF,Fd,fit⟩:=marked13_complete_factor θ u v R rdiv
    (mul_ne_zero_iff.mp ui).2 (mul_ne_zero_iff.mp (mul_ne_zero_iff.mp vj).2).2 vu hu hv
  let B0 := L*B
  let B1 : K[X] := X*B0
  let B2 : K[X] := (X-Polynomial.C u)*B0
  have b0n:B0≠0 := mul_ne_zero (fun z=>lu (by rw [z,eval_zero])) bn
  have b0p:B0*P=X*F := by
    calc B0*P=L*(B*P) := by dsimp [B0];ring
      _ = _ := by rw [base,fF];ring
  have b1p:B1*P=X*(X*F) := by dsimp [B1];rw [mul_assoc,b0p]
  have b2p:B2*P=(X-Polynomial.C u)*(X*F) := by dsimp [B2];rw [mul_assoc,b0p]
  have Fn:F≠0 := by intro z;rw [z,natDegree_zero] at Fd;omega
  have sumD := congrArg natDegree b0p
  rw [natDegree_mul b0n pn,natDegree_X_mul Fn,Fd] at sumD
  have b0pay:=marked13_mask_budget5 C.marked B0 (by omega)
  have b1d:B1.natDegree≤r := by dsimp [B1];rw [natDegree_X_mul b0n];omega
  have b1pay:=marked13_mask_budget6 C.marked B1 b1d
  have hfirst:FirstContrast A w e P B0 i := hi.mul L lu
  have hsecond:FirstContrast A w e P B1 i := hfirst.mul X (by simpa only [eval_X] using un)
  have hnext:FirstContrast A w e P B2 j := by
    have q := hj.mul L lv
    convert q using 1
    dsimp [E,B2,B0]
    ring
  have y0 := markedResponse_paid (P:=P) ha C he (by decide) B0 (by rw [natDegree_mul b0n pn];omega) b0pay
  have y1 := markedResponse_paid (P:=P) ha C he (by decide : 5≤6) B1 (natDegree_mul_le.trans (by omega)) b1pay
  have t0 (k:Fin (s+1)) (ok:¬Live U k) (wk:w k=0) : maskedResponse A w e P B0 k=0 :=
    marked13_off_six C y0 ok wk
  obtain ⟨τ,t1⟩:=marked13_off_seven_line ha ho S M C y1
  have ys : maskedResponse A w e P B2 j=maskedResponse A w e P B1 j := by
    have h:B2=B1-u•B0 := by dsimp [B2,B1];rw [sub_mul,smul_eq_C_mul]
    rw [h,map_sub,map_smul,Pi.sub_apply,Pi.smul_apply,t0 j oj wj,smul_zero,sub_zero]
  have m0:=t0 i oi wi
  have m1:=t1 i oi wi
  have m2:=ys.trans (t1 j oj wj)
  rw [markedResponse_at_first ha hfirst,b0p] at m0
  rw [markedResponse_at_first ha hsecond,b1p] at m1
  rw [markedResponse_at_first ha hnext,b2p] at m2
  exact ⟨θ,u,v,τ,F,un,vn,vu,(markPencil_simple_at θ u hu).1,fit,m0,m1,m2⟩

end RKCert.Paired.FiniteMidpoint
