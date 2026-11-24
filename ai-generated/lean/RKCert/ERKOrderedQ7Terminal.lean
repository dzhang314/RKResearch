module
public import RKCert.ERKOrderedQ7Knots
public import RKCert.ERKOrderedQ7Factor
public import RKCert.ERKFiniteEndpointData

@[expose] public section

/-! # Finish the actual order-14 equality case -/
namespace RKCert.Paired.FiniteMidpoint
open RKCert.Paired RKCert.Paired.Clock RKCert.OneEscape RKCert.Endpoint Polynomial Module
open scoped Classical
variable {K:Type*} [Field K] [CharZero K] {s r:ℕ}
variable {A:Fin (s+1)→Fin (s+1)→K} {b:Vec K (s+1)}
variable {U:Submodule K (Vec K (s+1))} {w:Vec K (s+1)} {G P:K[X]}
set_option maxHeartbeats 2100000

theorem even_seven_terminal_profile (ha:StrictLower A) (ho:HasTreeOrderAtLeast A b 14)
    (S:Saturated A b 7 0) :
    ∃ t:K,t≠0∧∃ f∈zeroSpace A 7,evalNodes A (t•dx6)+f=terminal s := by
  classical
  obtain ⟨one,h⟩:=even_terminal_column_short (q:=7) ha ho (by decide) S
  rw [treeSpace_sup ho (show 7+1≤14 by decide)] at h
  obtain ⟨z,⟨c,rfl⟩,f,hf,eq⟩:=Submodule.mem_sup.mp h
  let P:=ofFn 8 c
  have pD : P.natDegree≤7 := Nat.le_of_lt_succ (ofFn_natDegree_lt (by decide) _)
  have ev : evalNodes A P=polyEval A 7 c := evalNodes_ofFn A 7 c
  have hP : evalNodes A P∈defectPlus A 1 7 := by
    refine Submodule.mem_sup.mpr ⟨-f,(zeroSpace A 7).neg_mem hf,terminal s,?_,?_⟩
    · rw [tailPlane,ite_eq_right (by decide : (1:ℕ)≠0)]
      exact Submodule.subset_span (Set.mem_singleton _)
    · rw [←eq,ev]
      abel
  have h0:=marked_eval_origin ha (by have := S.size;omega) P hP
  have h1 : P.eval 1=1 := by
    have zf := even_last_zero_short ha ho (by decide) S _ hf
    have h := congrFun eq (Fin.last s)
    rwa [Pi.add_apply,zf,add_zero,←ev,evalNodes_apply,one,terminal_at_last] at h
  obtain ⟨t,ht⟩:=terminalEven7_decode P pD h0 (fun k=>
    marked_moment_difference ho P hP pD (fun _=>one) (by have :=k.isLt;omega))
  have tn:t≠0 := by
    intro hz
    rw [ht,hz,zero_smul,eval_zero] at h1
    exact zero_ne_one h1
  exact ⟨t,tn,f,hf,by rwa [←ht,ev]⟩

theorem cubic_from_seven_masks (ha:StrictLower A) (S:Saturated A b 7 0)
    (M:Margin A b 7 0 0) (C:EvenSevenChart A r U w G) (Pr:SevenProfile A r U w P)
    (R:K[X]) (rn:R≠0) (rd:R.natDegree≤3) (δ:ℕ) (hd:δ+2≤r)
    (fit:(X:K[X])^δ*P=X*R) : False := by
  let Q1 : K[X] := X^δ
  have Q1d : Q1.natDegree=δ := natDegree_X_pow _
  obtain ⟨i,_,_,uFit,uTests⟩:=physical_seven_knot ha S M C Pr Q1 (pow_ne_zero _ X_ne_zero) (by omega)
  let u:=nodes A i
  have h1:Q1*P=X*R := fit
  rw [h1] at uFit uTests
  have un : u*R.eval u≠0 := by simpa only [eval_mul,eval_X] using uFit
  have u0 : u≠0 := fun hz=>un (by rw [hz,zero_mul])
  have Ru : R.eval u≠0 := fun hz=>un (by rw [hz,mul_zero])
  let Q2 : K[X] := Q1*(X-Polynomial.C u)
  have n2 : Q2≠0 := mul_ne_zero (pow_ne_zero _ X_ne_zero) (X_sub_C_ne_zero _)
  have d2 : Q2.natDegree=δ+1 := by
    change (Q1*(X-Polynomial.C u)).natDegree=δ+1
    rw [natDegree_mul (show Q1≠0 from pow_ne_zero _ X_ne_zero) (X_sub_C_ne_zero _),Q1d,natDegree_X_sub_C]
  obtain ⟨j,_,_,vFit,vTests⟩:=physical_seven_knot ha S M C Pr Q2 n2 (by omega)
  let v:=nodes A j
  have h2 : Q2*P=X*(X-Polynomial.C u)*R := by
    calc
      _ = (X-Polynomial.C u)*(Q1*P) := by dsimp [Q2];ring
      _ = _ := by rw [h1];ring
  rw [h2] at vFit vTests
  have nz : v*(v-u)*R.eval v≠0 := by simpa [v] using vFit
  have v0 : v≠0 := by intro e;apply nz;simp [e]
  have vu : v≠u := by intro e;apply nz;simp [e]
  have rv : R.eval v≠0 := by intro e;apply nz;simp [e]
  have J : KnotPair R (0:K[X]) 8 u v := by
    refine ⟨u0,v0,vu,Ru,rv,eval_zero,eval_zero,?_,?_⟩
    · intro k hk
      exact uTests (X^k) (by rw [Q1d,natDegree_X_pow];omega)
    · intro k hk
      exact vTests (X^k) (by rw [d2,natDegree_X_pow];omega)
  exact rn (cubic_no_profile (by decide) J rd)

theorem seven_terminal_factors (ha:StrictLower A) (ho:HasTreeOrderAtLeast A b 14)
    (S:Saturated A b 7 0) (C:EvenSevenChart A 2 U w G) (Pr:SevenProfile A 2 U w P) :
    P.natDegree=4 ∧
      (P.eval 0≠0→P∣dSixPoly) ∧
      (∀ i,¬Live U i→w i=0→nodes A i=1∨(nodes A i≠0→dSixValue (nodes A i)=0)) := by
  classical
  obtain ⟨t,tn,f,hf,ef⟩:=even_seven_terminal_profile ha ho S
  let H := t•(dx6:K[X])
  have e : evalNodes A H+f=terminal s := ef
  have hd : H.natDegree=7 := by dsimp [H];rw [natDegree_smul _ tn,dx6_degree]
  have hn: H≠0 := by intro hz;rw [hz,natDegree_zero] at hd;omega
  have hf' : f∈defectPlus A 0 7 := tail_zero_iff.mpr hf
  rw [C.marked.paid 7 (by decide) le_rfl] at hf'
  change f∈chain (diag (nodes A)) U w 4 at hf'
  obtain ⟨u,hu,Q,Qd,hfEq⟩:=exists_head_poly hf'
  have eq : H=P*(-Q) := by
    apply eq_of_degrees_lt_of_eval_finset_eq (headSites (nodes A) w)
    · have sH := even_seven_sites C
      exact degree_le_natDegree.trans_lt (by rw [hd];exact_mod_cast (show 7<(headSites (nodes A) w).card by omega))
    · have qd : Q.natDegree≤3 := by
        by_cases q0:Q=0
        · simp [q0]
        · exact Nat.le_of_lt_succ ((natDegree_lt_iff_degree_lt q0).mpr Qd)
      have ht : (P*(-Q)).natDegree≤7 := by
        have pp := Pr.degree
        have de := natDegree_mul_le (p:=P) (q:=-Q)
        rw [natDegree_neg] at de
        omega
      exact degree_le_natDegree.trans_lt (by
        have sH := even_seven_sites C
        exact_mod_cast (show (P*(-Q)).natDegree<(headSites (nodes A) w).card by omega))
    · intro z hz
      obtain ⟨i,hi,rfl⟩:=Finset.mem_image.mp hz
      have wi := (Finset.mem_filter.mp hi).2
      have ui : u i=0 := by by_contra zz;exact wi (Pr.disjoint i ⟨u,hu,zz⟩)
      have ni : i≠Fin.last s := by
        intro zz
        subst i
        apply wi
        have hw5 : w∈defectPlus A 0 5 := by simpa using marked_power C.marked (by decide) (k:=0) (by decide)
        exact grade_five_last_seven ha ho S hw5
      have ra:=congrFun e i
      rw [Pi.add_apply,terminal_at_ne ni,evalNodes_apply,hfEq i,ui,zero_add,Pr.repr i wi] at ra
      simp only [eval_mul,eval_neg]
      linear_combination ra
  have nq : -Q≠0 := by intro zz;exact hn (by rw [eq,zz,mul_zero])
  have qd : Q.natDegree≤3 := by
    by_cases q0:Q=0
    · simp [q0]
    · exact Nat.le_of_lt_succ ((natDegree_lt_iff_degree_lt q0).mpr Qd)
  have pd:P.natDegree=4 := by
    have aa:=Pr.degree
    have h := congrArg Polynomial.natDegree eq
    rw [hd,natDegree_mul Pr.nonzero nq,natDegree_neg] at h
    omega
  have Hfactor : H=(t*56)•(X*dSixPoly) := by
    dsimp [H]
    rw [dx6_as_dSix,←Nat.cast_smul_eq_nsmul K (56:ℕ) (X*dSixPoly:K[X]),smul_smul]
    norm_num

  have scale : t*(56:K)≠0 := mul_ne_zero tn (by norm_num)
  refine ⟨pd,?_ ,?_⟩
  · intro pp0
    have h0 : (-Q).eval 0=0 := by
      have raw := congrArg (fun T:K[X]=>T.eval 0) eq
      rw [Hfactor,eval_smul,eval_mul,eval_X,zero_mul,smul_zero,eval_mul] at raw
      exact (mul_eq_zero.mp raw.symm).resolve_left pp0
    have hdiv : (X:K[X])∣ -Q := by
      simpa using (dvd_iff_isRoot (a:=(0:K))).mpr h0
    obtain ⟨J,hJ⟩:=hdiv
    have h : ((t*56)•(dSixPoly:K[X]))=P*J := by
      apply mul_left_cancel₀ X_ne_zero
      rw [mul_smul_comm,←Hfactor,eq,hJ]
      ring
    refine ⟨(t*56)⁻¹•J,?_⟩
    have hh := congrArg (fun V:K[X]=>(t*56)⁻¹•V) h
    simpa only [smul_smul,inv_mul_cancel₀ scale,one_smul,mul_smul_comm] using hh
  · intro i hoU hw0
    by_cases ih:i=Fin.last s
    · subst i
      exact Or.inl (even_terminal_column_short (q:=7) ha ho (by decide) S).1
    · right
      intro ni
      have ui:u i=0 := by by_contra hz;exact hoU ⟨u,hu,hz⟩
      have he:=congrFun e i
      rw [Pi.add_apply,terminal_at_ne ih,evalNodes_apply,hfEq i,ui,hw0,mul_zero,zero_add,add_zero,
        Hfactor,eval_smul,smul_eq_mul,eval_mul,eval_X,dSixPoly_eval] at he
      exact (mul_eq_zero.mp ((mul_eq_zero.mp he).resolve_left scale)).resolve_left ni

end RKCert.Paired.FiniteMidpoint

