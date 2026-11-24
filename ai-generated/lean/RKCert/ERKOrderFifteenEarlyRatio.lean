module
public import RKCert.ERKOrderFifteenLeakage

@[expose] public section

/-! # Three shifts suffice once the actual terminal column has entered.
The first shifted ghost has a different terminal mass ratio from the
highest surviving ghost. Compute this via the single unshifted mesh
moment, rather than fitting the entire ghost basis. -/
namespace RKCert.Paired.FiniteMidpoint
open RKCert.Paired RKCert.Endpoint Polynomial
variable {K : Type*} [Field K] [CharZero K]

theorem dx5_marked_five :
    balancedMoment 1 (dx5 : K[X]) 5=(1/1716:K) := by
  have h : (dx5:K[X]).natDegree≤10 := by rw [dx5_degree];decide
  unfold balancedMoment
  rw [ite_eq_right (by decide : (1:ℕ)≠0),scalarMoment_11 _ h,scalarMoment_11 _ h]
  norm_num [moment,Fin.sum_univ_succ,dx5_coeff]

theorem dx5_marked_low (k : Fin 5) :
    balancedMoment 1 (dx5 : K[X]) k=0 := by
  have h : (dx5:K[X]).natDegree≤10 := by rw [dx5_degree];decide
  unfold balancedMoment
  rw [ite_eq_right (by decide : (1:ℕ)≠0),scalarMoment_11 _ h,scalarMoment_11 _ h]
  fin_cases k <;> norm_num [moment,Fin.sum_univ_succ,dx5_coeff]

theorem low_marked_line (P : K[X]) (pd:P.natDegree≤6) (p0:P.coeff 0=0)
    (tests:∀k≤4,balancedMoment 1 P k=0) : ∃t:K,P=t•dx5 := by
  let t : K := 1716*balancedMoment 1 P 5
  let Q := P-t•(dx5:K[X])
  have qd : Q.natDegree≤6 :=
    (natDegree_sub_le _ _).trans (max_le pd ((natDegree_smul_le ..).trans_eq dx5_degree))
  have q0 : Q.coeff 0=0 := by
    simp [Q,coeff_sub,AddMonoidAlgebra.coeff_smul_apply,p0,dx5_coeff 0 (by decide)]
  have test (j:Fin 6) : scalarMoment Q j.val-scalarMoment Q (j.val+1)=0 := by
    have h : balancedMoment 1 Q j.val=0 := by
      rw [show Q=P-t•dx5 from rfl,balancedMoment_sub,balancedMoment_smul]
      by_cases hi:j.val=5
      · rw [hi,dx5_marked_five]
        unfold t
        ring
      · have c:j.val<5 := by have :=j.isLt;omega
        rw [tests _ (by omega),dx5_marked_low ⟨j.val,c⟩,mul_zero,sub_zero]
    simpa [balancedMoment] using h
  obtain ⟨α,β,e⟩:=meshOddPrefix7_decode Q (by omega) q0 test
  by_cases z:Q=0
  · exact ⟨t,sub_eq_zero.mp z⟩
  · have eq := (odd_seven_alias_form (.marked α β e) (by omega) z).2.1
    omega

noncomputable def terminalMoment (b : K) (P : K[X]) := scalarMoment P 0-b*P.eval 1

theorem terminalMoment_smul (b t : K) (P : K[X]) :
    terminalMoment b (t•P)=t*terminalMoment b P := by
  rw [terminalMoment,scalarMoment_smul,eval_smul,smul_eq_mul,terminalMoment]
  ring

theorem terminalMoment_sub (b : K) (P Q : K[X]) :
    terminalMoment b (P-Q)=terminalMoment b P-terminalMoment b Q := by
  simp only [terminalMoment,scalarMoment_sub,eval_sub]
  ring

theorem terminalMoment_add (b : K) (P Q : K[X]) :
    terminalMoment b (P+Q)=terminalMoment b P+terminalMoment b Q := by
  simp only [terminalMoment,scalarMoment,mul_add,map_add,eval_add]
  ring

theorem terminalMoment_dx5 (b:K) : terminalMoment b (dx5:K[X])=1-42*b := by
  have h : (dx5:K[X]).natDegree≤10 := by rw [dx5_degree];decide
  rw [terminalMoment,scalarMoment_11 _ h,eval_one_11 _ h]
  norm_num [moment,Fin.sum_univ_succ,dx5_coeff]
  ring

theorem terminalMoment_dx6 (b:K) : terminalMoment b (dx6:K[X])=1-56*b := by
  have h : (dx6:K[X]).natDegree≤10 := by rw [dx6_degree];decide
  rw [terminalMoment,scalarMoment_11 _ h,eval_one_11 _ h]
  norm_num [moment,Fin.sum_univ_succ,dx6_coeff]
  ring

theorem terminalMoment_dx7 (b:K) : terminalMoment b (dx7:K[X])=1-72*b := by
  have h : (dx7:K[X]).natDegree≤10 := by rw [dx7_degree];decide
  rw [terminalMoment,scalarMoment_11 _ h,eval_one_11 _ h]
  norm_num [moment,Fin.sum_univ_succ,dx7_coeff]
  ring

theorem terminalMoment_mesh_of_shift {P Q G:K[X]} {b t:K} {a:ℕ}
    (pd:P.natDegree=a) (pn:P≠0) (qd:Q.natDegree≤a)
    (test:balancedMoment 1 P 0=0) (shift:X*P-Q=t•G)
    (pm:terminalMoment b P=0) (qm:terminalMoment b Q=0) :
    terminalMoment b G=0 := by
  have tne:t≠0 := by
    intro e
    rw [e,zero_smul,sub_eq_zero] at shift
    rw [←shift,natDegree_X_mul pn,pd] at qd
    omega
  have diff : scalarMoment P 0=scalarMoment P 1 :=
    sub_eq_zero.mp (by simpa [balancedMoment] using test)
  have mp : terminalMoment b (X*P)=0 := by
    unfold terminalMoment at *
    rw [scalarMoment_clock,eval_mul,eval_X,one_mul,←diff]
    exact pm
  have eq := congrArg (terminalMoment b) shift
  rw [terminalMoment_sub,terminalMoment_smul,mp,qm,sub_zero] at eq
  exact (mul_eq_zero.mp eq.symm).resolve_left tne

theorem early_marked_scalar_rigid {P Q G:K[X]} {b t:K} {a:ℕ}
    (small:a=6∨a=7) (shape:OddSevenMesh G 1) (gd:G.natDegree=a+1)
    (pd:P.natDegree≤a) (qd:Q.natDegree≤a) (p0:P.coeff 0=0)
    (test:∀k≤a-2,balancedMoment 1 P k=0)
    (pm:terminalMoment b P=0) (qm:terminalMoment b Q=0) (shift:X*P-Q=t•G) : P=0 := by
  by_contra pn
  have gn:G≠0 := by intro e;rw [e,natDegree_zero] at gd;omega
  rcases small with a6|a7
  · subst a
    obtain ⟨v,e⟩:=low_marked_line P pd p0 (fun k hk=>test k (by omega))
    have deg := (mesh_line_degree e pn).trans dx5_degree
    have mz := terminalMoment_mesh_of_shift deg pn qd (test 0 (by decide)) shift pm qm
    obtain ⟨_,_,c,cn,f⟩:=odd_seven_alias_form shape gd.le gn
    have vn:v≠0 := by intro h;exact pn (by rw [e,h,zero_smul])
    rw [e,terminalMoment_smul,terminalMoment_dx5] at pm
    rw [f,terminalMoment_smul,terminalMoment_dx6] at mz
    have e1 := (mul_eq_zero.mp pm).resolve_left vn
    have e2 := (mul_eq_zero.mp mz).resolve_left cn
    apply (one_ne_zero : (1:K)≠0)
    linear_combination 4*e1-3*e2
  · subst a
    have low(j:Fin 6) : scalarMoment P j.val-scalarMoment P (j.val+1)=0 := by
      simpa [balancedMoment] using test j.val (by have :=j.isLt;omega)
    obtain ⟨v,u,e⟩:=meshOddPrefix7_decode P (by omega) p0 low
    obtain ⟨_,deg,c,cn,f⟩:=odd_seven_alias_form (.marked v u e) pd pn
    have mz := terminalMoment_mesh_of_shift deg pn qd (test 0 (by decide)) shift pm qm
    rw [f,terminalMoment_smul,terminalMoment_dx6] at pm
    have e1 := (mul_eq_zero.mp pm).resolve_left cn
    cases shape with
    | marked v u mesh =>
      have un:u≠0 := by
        intro z
        rw [z,zero_smul,add_zero] at mesh
        have h := (mesh_line_degree mesh gn).trans dx6_degree
        omega
      rw [mesh,terminalMoment_add,terminalMoment_smul,terminalMoment_smul,terminalMoment_dx6,
        terminalMoment_dx7,e1,mul_zero,zero_add] at mz
      have e2 := (mul_eq_zero.mp mz).resolve_left un
      apply (one_ne_zero : (1:K)≠0)
      linear_combination (9/2)*e1-(7/2)*e2

end RKCert.Paired.FiniteMidpoint
