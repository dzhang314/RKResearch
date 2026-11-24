module

public import RKCert.ReviewedNative.OneOffSeventhProfiles
public import RKCert.ReviewedNative.OneOffSeventhResiduals

@[expose] public section

/-! # The actual affine factor of the terminal Ag coefficient -/
namespace RKResearch.Certified.Graded.OneOff.Seven
open RKResearch Polynomial Module
open RKCert.Paired.OneOff (endpointF endpointG endpoint_nonzero readGrid endpointFData endpointG_formula)
open scoped Classical Matrix

variable {K : Type*} [Field K] [CharZero K] {A : Matrix (Fin 12) (Fin 12) K} {b : Fin 12 → K}

noncomputable def endLPoly (d z : K) : K[X] :=
  let S := 2*(1-2*d)*paramU d
  C (((4*endpointF d d)/d)/((d-z)*S))*(X-C z)-
    C (((4*d*endpointF d z)/(z*(z-2*d)))/((z-d)*S))*(X-C d)

noncomputable def terminalQ (d z : K) : K[X] := (X-C (2*d))*endLPoly d z

theorem endL_poly_eval (d z x : K) : (endLPoly d z).eval x=endL d z x := by
  simp only [endLPoly,endL,eval_sub,eval_mul,eval_C,eval_X]
  ring

theorem terminalQ_eval (d z x : K) :
    (terminalQ d z).eval x=(x-2*d)*endL d z x := by
  simp [terminalQ,endL_poly_eval]

omit [CharZero K] in
theorem endL_poly_degree (d z : K) : (endLPoly d z).natDegree≤1 := by
  exact natDegree_sub_le_of_le
    ((natDegree_C_mul_le _ _).trans (natDegree_X_sub_C_le _))
    ((natDegree_C_mul_le _ _).trans (natDegree_X_sub_C_le _))

omit [CharZero K] in
theorem terminalQ_degree (d z : K) : (terminalQ d z).natDegree≤2 :=
  natDegree_mul_le_of_le (natDegree_X_sub_C_le _) (endL_poly_degree _ _)

structure EndpointChart (A : Matrix (Fin 12) (Fin 12) K) (a d z : K) : Prop where
  Un : paramU d≠0
  eq_on : ∀ r : Fin 12, r≠Fin.last 11 → g A r=0 →
    endP d (nodes A r)+(terminalQ d z).eval (nodes A r)*scaledH A a r=0
  p1 : endP d 1=1

theorem order9_actual_endpoint_chart (ha : ∀ i j, i ≤ j → A i j = 0) (ho : HasOrder A b 9)
    {a d : K} {i j : Fin 12} (D : GlobalNormal A a d i j) (F : FirstFour A a d (by decide)) :
    EndpointChart A a d (nodes A (5:Fin 12)) := by
  let z := nodes A (5:Fin 12)
  let q := terminalQ d z
  have an := D.base.origin.a_ne
  have dn := D.base.dn
  have C4 := order9_clean_four ha ho D F
  obtain ⟨_,_,_,t1⟩ := order9_maximal_normal_profile ha ho D F
  have sixth := order9_sixth_feature ha ho D F
  have zn : z≠0 := sixth.2.1
  have zd : z≠d := sixth.2.2.1
  have zt : z≠2*d := sixth.2.2.2.1
  obtain ⟨w,wU,fn,qt,pForm,p1⟩ := order9_terminal_normal_profile ha ho D F
  let P := ofFn 6 w.1
  let Q := C a * ofFn 3 w.2.2
  have ff : endpointF d 1=2*paramU d := endpointF_at_one d
  have un : paramU d≠0 := by intro e; exact fn (by rw [ff,e,mul_zero])
  have Pform (x : K) : P.eval x=endP d x := by
    rw [endP,←show (1-2*d)*(2*paramU d)=2*(1-2*d)*paramU d by ring,←ff]
    exact pForm x
  have raw (r : Fin 12) (nr : r≠Fin.last 11) (gr : g A r=0) :
      endP d (nodes A r)+Q.eval (nodes A r)*scaledH A a r=0 := by
    have e := (normal_profile_value w r).symm.trans (congrFun wU r)
    have R0 : Reverse.coordinate (K:=K) (Fin.last 11) r=0 := by
      have nr' : r ≠ (11 : Fin 12) := fun he => nr (he.trans (by decide))
      simp [Reverse.coordinate,nr']
    rw [gr,mul_zero,zero_add,R0] at e
    change P.eval (nodes A r)+h A r*(ofFn 3 w.2.2).eval (nodes A r)=0 at e
    rw [Pform] at e
    simp only [Q,eval_mul,eval_C,scaledH_eval]
    field_simp [an]
    linear_combination e
  have Qd : Q.eval d=q.eval d := by
    have rr := raw (2:Fin 12) (by decide) C4.g2
    rw [C4.node2,C4.H2] at rr
    have ed := cubic_endpoint_residual d z d dn zn zd zt t1 un
    simp only [sub_self,mul_zero,zero_mul,zero_div] at ed
    have e : (Q.eval d-q.eval d)*hzero d d=0 := by
      simp only [q,terminalQ_eval] 
      linear_combination rr-ed
    exact sub_eq_zero.mp ((mul_eq_zero.mp e).resolve_right
      (hzero_ne d d dn dn (by intro x; exact dn (by linear_combination -x))))
  have Qz : Q.eval z=q.eval z := by
    have rr := raw (5:Fin 12) (by decide) C4.g5
    rw [C4.node5,C4.H5] at rr
    have ez := cubic_endpoint_residual d z z dn zn zd zt t1 un
    simp only [sub_self,mul_zero,zero_mul,zero_div] at ez
    have e : (Q.eval z-q.eval z)*hzero d z=0 := by
      simp only [q,terminalQ_eval]
      linear_combination rr-ez
    exact sub_eq_zero.mp ((mul_eq_zero.mp e).resolve_right (hzero_ne d z dn zn zt))
  have Qt : Q.eval (2*d)=q.eval (2*d) := by simp [Q,q,terminalQ_eval,qt]
  have dt : d≠2*d := by intro h; exact dn (by linear_combination -h)
  have S : ({d,2*d,z}:Finset K).card=3 := by simp [dt,Ne.symm zd,Ne.symm zt]
  have deg : Q.natDegree≤2 := (natDegree_C_mul_le _ _).trans
    (Nat.le_of_lt_succ (ofFn_natDegree_lt (by decide) _))
  have dd := natDegree_sub_le_of_le deg (terminalQ_degree d z)
  have Qeq : Q=q := sub_eq_zero.mp (Polynomial.eq_zero_of_natDegree_lt_card_of_eval_eq_zero'
    (Q-q) ({d,2*d,z}:Finset K) (fun x hx=>by
      simp only [Finset.mem_insert,Finset.mem_singleton] at hx
      rcases hx with rfl|rfl|rfl <;> simp only [eval_sub,Qd,Qt,Qz,sub_self])
    (by rw [S]; simpa using Nat.lt_succ_of_le dd))
  refine ⟨un,fun r nr gr=>?_,(Pform 1).symm.trans p1⟩
  simpa only [Qeq] using raw r nr gr

end RKResearch.Certified.Graded.OneOff.Seven
