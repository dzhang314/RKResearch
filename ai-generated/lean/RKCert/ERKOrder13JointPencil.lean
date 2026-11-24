module
public import RKCert.ERKOrder13MarkedJoint

@[expose] public section
/-! # Omitted-root arithmetic for actual joint-block contrast profiles -/
namespace RKCert.Paired.FiniteMidpoint
open RKCert.Paired RKCert.Paired.Clock RKCert.OneEscape RKCert.Paired.OrderTwelve
  RKCert.Endpoint RKCert.OrderTwelve Module Polynomial
variable {K:Type*} [Field K] [LinearOrder K] [IsStrictOrderedRing K] {s a r:ℕ}
variable {A:Fin (s+1)→Fin (s+1)→K} {b:Vec K (s+1)}
variable {U:Submodule K (Vec K (s+1))} {w v:Vec K (s+1)} {G P:K[X]}
set_option maxHeartbeats 3900000

theorem marked13_joint_alias_impossible (ha:StrictLower A)
    (S:Saturated A b 6 1) (M:Margin A b 6 1 1) (C:Chart13 A 1 5 r U w G)
    (hm:U.map (diag v)≤U) (mult:v*w-weightedEval (nodes A) w P∈U)
    (v5:v∈defectPlus A 1 5) (w5:weightedEval (nodes A) v X∈defectPlus A 1 5)
    (pn:P≠0) (pd:P.natDegree≤3) (pf:P∣G) : False := by
  have jd : ((X:K[X])*P).natDegree≤5 := by rw [natDegree_X_mul pn];omega
  obtain ⟨i,h⟩:=first_marked_joint_exists S M C hm pn (X:K[X]) X_ne_zero
    (jd.trans (by decide)) (Fplus_mono A 1 (by decide) w5)
  obtain ⟨gi,bi⟩:=h.off C hm mult v5
  have u0:nodes A i≠0 := by
    intro z
    apply bi
    rw [eval_mul,eval_X,z,zero_mul]
  have yr:=marked_joint_residual_paid (P:=P) ha (X:K[X]) jd w5
  have b6 := C.marked.paid 6 (by decide) le_rfl
  have cap : defectPlus A 1 6≤chain (diag (nodes A)) U w (r+1) := le_of_eq b6
  have zeroEval : evalNodes A (0:K[X])=(0:Vec K (s+1)) := by ext i;simp
  have z0 := h.integral (H:=0) ha C hm mult cap (by rw [zeroEval,sub_zero];exact cap yr)
  rw [eval_zero] at z0
  obtain ⟨t,gt⟩:=marked13_alias_mesh C
  rw [dx5_mark_factor,smul_smul] at gt
  have qn : t*42≠0 := by
    intro z
    have d:=C.meshDegree
    rw [gt,z,zero_smul,natDegree_zero] at d
    omega
  have df : P∣X*(dFivePoly:K[X]) := by
    rw [gt,smul_eq_C_mul] at pf
    exact ((isUnit_C.mpr (isUnit_iff_ne_zero.mpr qn)).dvd_mul_left).mp pf
  rw [gt,eval_smul,smul_eq_mul] at gi
  exact marked13_alias_primitive_ne_zero P _ pn df pd u0 ((mul_eq_zero.mp gi).resolve_left qn) z0

theorem marked13_joint_unaliased_impossible (ha:StrictLower A) (ho:HasTreeOrderAtLeast A b 13)
    (S:Saturated A b 6 1) (M:Margin A b 6 1 1) (C:Chart13 A 1 6 r U w G)
    (hm:U.map (diag v)≤U) (mult:v*w-weightedEval (nodes A) w P∈U)
    (v5:v∈defectPlus A 1 5)
    (pn:P≠0) (pd:P.natDegree≤4) (pf:P∣G)
    (paid5:∀ (B:K[X]),B.natDegree+P.natDegree≤5→weightedEval (nodes A) v B∈defectPlus A 1 5)
    (paid6:∀ (B:K[X]),B.natDegree+P.natDegree≤6→weightedEval (nodes A) v B∈defectPlus A 1 6) : False := by
  obtain ⟨t,θ,tn,mesh⟩:=marked13_unaliased_mesh C
  have pdiv:P∣X*markPencil θ := by
    rw [mesh,smul_eq_C_mul] at pf
    exact ((isUnit_C.mpr (isUnit_iff_ne_zero.mpr tn)).dvd_mul_left).mp pf
  obtain ⟨B,R,bn,rn,bd,base,rdiv⟩:=marked13_base_factor (markPencil θ) P pn pdiv
  obtain ⟨i,hi⟩:=first_marked_joint_exists S M C hm pn B bn (natDegree_mul_le.trans (by omega))
    (paid6 B (by omega))
  let u:=nodes A i
  obtain ⟨gi,bi⟩:=hi.off C hm mult v5
  have ui : u*R.eval u≠0 := by rw [base,eval_mul,eval_X] at bi;exact bi
  let E : K[X] := (X-Polynomial.C u)*B
  have En:E≠0 := mul_ne_zero (X_sub_C_ne_zero _) bn
  have Ed:E.natDegree≤2 := by
    dsimp [E]
    rw [natDegree_mul (X_sub_C_ne_zero _) bn,natDegree_X_sub_C]
    omega
  obtain ⟨j,hj⟩:=first_marked_joint_exists S M C hm pn E En (natDegree_mul_le.trans (by omega))
    (paid6 E (by omega))
  let x:=nodes A j
  obtain ⟨gj,bj⟩:=hj.off C hm mult v5
  have xj : (x-u)*(x*R.eval x)≠0 := by
    change (E*P).eval x≠0 at bj
    rw [show E*P=(X-Polynomial.C u)*(B*P) by dsimp [E];ring,base,
      eval_mul,eval_mul,eval_X,eval_sub,eval_X,eval_C] at bj
    exact bj
  have un:= (mul_ne_zero_iff.mp ui).1
  have xn:= (mul_ne_zero_iff.mp (mul_ne_zero_iff.mp xj).2).1
  have xu:x≠u := sub_ne_zero.mp (mul_ne_zero_iff.mp xj).1
  have pencilRoot {z:K} (zn:z≠0) (h:G.eval z=0) : (markPencil θ).eval z=0 := by
    rw [mesh,eval_smul,smul_eq_mul,eval_mul,eval_X] at h
    exact (mul_eq_zero.mp ((mul_eq_zero.mp h).resolve_left tn)).resolve_left zn
  have hu:=pencilRoot un gi
  have hx:=pencilRoot xn gj
  obtain ⟨L,F,lu,lx,fF,Fd,fit⟩:=marked13_complete_factor θ u x R rdiv
    (mul_ne_zero_iff.mp ui).2 (mul_ne_zero_iff.mp (mul_ne_zero_iff.mp xj).2).2 xu hu hx
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
  have b0pay:=paid5 B0 (by omega)
  have b1d:B1.natDegree+P.natDegree≤6 := by dsimp [B1];rw [natDegree_X_mul b0n];omega
  have b1pay:=paid6 B1 b1d
  have hfirst:FirstMarkedJoint A v U P B0 i := hi.mul C.marked.stable L lu
  have hsecond:FirstMarkedJoint A v U P B1 i := hfirst.mul C.marked.stable X (by simpa only [eval_X] using un)
  have hnext:FirstMarkedJoint A v U P B2 j := by
    have q := hj.mul C.marked.stable L lx
    convert q using 1
    dsimp [E,B2,B0]
    ring
  have y0 := marked_joint_residual_paid (P:=P) ha B0 (by rw [natDegree_mul b0n pn];omega) b0pay
  have y1 := marked_joint_residual_paid (P:=P) ha B1 (natDegree_mul_le.trans b1d) b1pay
  let T:K[X]:=X*dFivePoly
  obtain ⟨τ,y1'⟩:=marked13_seven_line ha ho S M C y1
  change contrastResidual A v P B1-evalNodes A (τ•T)∈Band13 A 6 r U w 7 at y1'
  have cap : defectPlus A 1 6≤Band13 A 6 r U w 7 := by
    exact (show defectPlus A 1 6≤firstEscape A 1 6 from sup_le_sup le_sup_left le_rfl).trans (firstEscape_band13 C 7)
  have zeroEval : evalNodes A (0:K[X])=(0:Vec K (s+1)) := by ext k;simp
  have y2 : contrastResidual A v P B2-evalNodes A (τ•T)∈Band13 A 6 r U w 7 := by
    have e:B2=B1-u•B0 := by dsimp [B2,B1];rw [sub_mul,smul_eq_C_mul]
    rw [e,map_sub,map_smul,sub_right_comm]
    exact (Band13 A 6 r U w 7).sub_mem y1' ((Band13 A 6 r U w 7).smul_mem _ (cap y0))
  have m0:=hfirst.integral (H:=0) ha C hm mult cap (by rw [zeroEval,sub_zero];exact cap y0)
  have m1:=hsecond.integral ha C hm mult cap y1'
  have m2:=hnext.integral ha C hm mult cap y2
  rw [b0p,eval_zero] at m0
  rw [b1p,eval_smul,smul_eq_mul,show T=X*dFivePoly from rfl,eval_mul,eval_X] at m1
  rw [b2p,eval_smul,smul_eq_mul,show T=X*dFivePoly from rfl,eval_mul,eval_X] at m2
  obtain ⟨an,om,f₀,f₁⟩:=Pencil13.physical_pair_to_integer θ u x τ F un xn
    (markPencil_simple_at θ u hu).1 fit m0 (by simpa only [mul_assoc] using m1) (by simpa only [mul_assoc] using m2)
  exact Pencil13.no_common_tape u x un an om f₀ f₁

end RKCert.Paired.FiniteMidpoint
