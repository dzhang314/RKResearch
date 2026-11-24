module
public import RKCert.ERKOrder13MarkedPureFactor
public import RKCert.ERKOrder13LateLift
public import RKCert.ERKOrder13OddFactor

@[expose] public section
/-! # The late marked pure obstruction reuses the full-odd factor gate -/
namespace RKCert.Paired.FiniteMidpoint
open RKCert.Paired RKCert.Paired.Clock RKCert.OneEscape RKCert.Endpoint Polynomial Module
variable {K:Type*} [Field K] [LinearOrder K] [IsStrictOrderedRing K] {s r a:ℕ}
variable {A:Fin (s+1)→Fin (s+1)→K} {b:Vec K (s+1)}
variable {U:Submodule K (Vec K (s+1))} {w:Vec K (s+1)} {G P:K[X]}
set_option maxHeartbeats 3000000

omit [LinearOrder K] [IsStrictOrderedRing K] in
theorem weighted_late_marked_budget (H:MarkedHead A 6 1 r U w) (R:K[X]) (hr:R.natDegree≤r) :
    weightedEval (nodes A) w R∈defectPlus A 1 6 := by
  rw [H.paid 6 (by decide) le_rfl]
  exact weighted_chain R (by omega)

theorem physical_late_marked_thirteen_knot (ha:StrictLower A) (ho:HasTreeOrderAtLeast A b 13)
    (S:Saturated A b 6 1) (M:Margin A b 6 1 1) (C:Chart13 A 1 6 r U w G) (Pr:SevenProfile A r U w P)
    (late:(terminal s:Vec K (s+1))∉treeSpace A 7)
    (Q:K[X]) (qn:Q≠0) (qd:Q.natDegree≤r) :
    ∃ k:Fin (s+1), ¬Live U k ∧ w k=0 ∧
      (Q*P).eval (nodes A k)≠0 ∧
      ∀ R:K[X], R.natDegree+Q.natDegree≤r→
        (Paired.primitive (R*(Q*P))).eval (nodes A k)=0 := by
  classical
  obtain ⟨e,he,eVal⟩:=core_indicator Pr.algebra
  have Pdeg := Pr.degree
  let c := nodes A
  let F := Q*P
  let W : Vec K (s+1) := weightedEval c w Q+weightedEval c e F
  let v := evalNodes A F-W
  have Fdeg : F.natDegree≤6 := natDegree_mul_le.trans (by omega)
  have hW : W∈defectPlus A 1 6 := by
    exact Submodule.add_mem _
      (weighted_late_marked_budget C.marked _ (by omega))
      (Fplus_mono A 1 (by omega) (C.marked.core (weighted_core C.marked F he)))
  have vn : v≠0 := by
    intro h
    have eF : evalNodes A F=W := sub_eq_zero.mp h
    have z := separated_plus S M F (by omega)
      (by rw [eF];exact Fplus_mono A 1 (by omega) hW)
    exact mul_ne_zero qn Pr.nonzero z
  let R := Finset.univ.filter (fun i=>v i≠0)
  have hR:R.Nonempty := by
    by_contra h
    apply vn
    ext i
    change v i=0
    by_contra hn
    exact h ⟨i,Finset.mem_filter.mpr ⟨Finset.mem_univ _,hn⟩⟩
  let k:=R.min' hR
  have hk : v k≠0 := (Finset.mem_filter.mp (R.min'_mem hR)).2
  have before (i:Fin (s+1)) (hi:i<k) : v i=0 := by
    by_contra hn
    exact (not_le_of_gt hi) (R.min'_le i (Finset.mem_filter.mpr ⟨Finset.mem_univ _,hn⟩))
  have hko : ¬Live U k := by
    intro h
    apply hk
    simp [v,W,eVal,h,Pr.disjoint k h,c]
  have hwk : w k=0 := by
    by_contra h
    apply hk
    simp [v,W,eVal,hko,Pr.repr k h,F,c]
  have Fk : F.eval (c k)≠0 := by
    intro h
    apply hk
    simpa [v,W,eVal,hko,hwk,c] using h
  have core_zero (u:Vec K (s+1)) (hu:u∈U) : u k=0 := by
    by_contra hn
    exact hko ⟨u,hu,hn⟩
  refine ⟨k,hko,hwk,Fk,?_⟩
  intro J hj
  let T:=J*F
  let WJ:=weightedEval c w (J*Q)+weightedEval c e T
  have qdeg : (J*Q).natDegree≤r := natDegree_mul_le.trans hj
  have jdeg : T.natDegree≤6 := by
    have h:=natDegree_mul_le (p:=J*Q) (q:=P)
    change (J*(Q*P)).natDegree≤6
    rw [←mul_assoc]
    omega
  have hWJ : WJ∈defectPlus A 1 6 := by
    exact Submodule.add_mem _
      (weighted_late_marked_budget C.marked _ (by omega))
      (Fplus_mono A 1 (by omega) (C.marked.core (weighted_core C.marked T he)))
  have eq : weightedEval c v J=evalNodes A T-WJ := by
    ext i
    simp only [weightedEval_apply,evalNodes_apply,Pi.sub_apply,Pi.add_apply,v,W,WJ,T,eval_mul]
    ring
  have hA : mat A (evalNodes A T-WJ) k=0 := by
    rw [←eq]
    have h := strictlyCausal_mat ha k (weightedEval c v J) 0 (fun i hi=>by simp [before i hi])
    simpa only [map_zero,Pi.zero_apply] using h
  let y:=evalNodes A (Paired.primitive T)-mat A (evalNodes A T-WJ)
  have dF : mat A (evalNodes A T)-evalNodes A (Paired.primitive T)∈defectPlus A 1 7 := by
    have h := primitive_defect A T jdeg
    exact (show zeroSpace A 7≤defectPlus A 1 7 from le_sup_left) (zeroSpace_mono A (by omega) h)
  have dW : mat A WJ∈defectPlus A 1 7 :=
    Fplus_mono A 1 (by omega) (Fplus_mat ha 1 6 ⟨_,hWJ,rfl⟩)
  have yh : y∈defectPlus A 1 7 := by
    dsimp [y]
    rw [map_sub,show evalNodes A (Paired.primitive T)-(mat A (evalNodes A T)-mat A WJ)=
      -(mat A (evalNodes A T)-evalNodes A (Paired.primitive T))+mat A WJ by abel]
    exact Submodule.add_mem _ (Submodule.neg_mem _ dF) dW
  rw [late13_exact_marked_F7 ha ho C late] at yh
  obtain ⟨u,hu,J0,_,h⟩:=exists_head_poly yh
  have eFinal := h k
  change (Paired.primitive T).eval (c k)-mat A (evalNodes A T-WJ) k=u k+J0.eval (c k)*w k at eFinal
  rwa [hA,core_zero u hu,hwk,mul_zero,add_zero,sub_zero] at eFinal

theorem cubic_from_late_marked_masks (ha:StrictLower A) (ho:HasTreeOrderAtLeast A b 13)
    (S:Saturated A b 6 1) (M:Margin A b 6 1 1) (C:Chart13 A 1 6 r U w G) (Pr:SevenProfile A r U w P)
    (late:(terminal s:Vec K (s+1))∉treeSpace A 7)
    (R:K[X]) (rn:R≠0) (rd:R.natDegree≤3) (δ:ℕ) (hd:δ+2≤r)
    (fit:(X:K[X])^δ*P=X*R) : False := by
  let Q1 : K[X] := X^δ
  have Q1d : Q1.natDegree=δ := natDegree_X_pow _
  obtain ⟨i,_,_,uFit,uTests⟩:=physical_late_marked_thirteen_knot ha ho S M C Pr late Q1 (pow_ne_zero _ X_ne_zero) (by omega)
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
  obtain ⟨j,_,_,vFit,vTests⟩:=physical_late_marked_thirteen_knot ha ho S M C Pr late Q2 n2 (by omega)
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

theorem marked13_late_clean_pure_impossible (ha:StrictLower A) (ho:HasTreeOrderAtLeast A b 13)
    (S:Saturated A b 6 1) (M:Margin A b 6 1 1) (C:Chart13 A 1 a 2 U w G)
    (alg:MulClosed U) (dis:∀i,Live U i→w i=0) (pure:w*w∈Band13 A a 2 U w 8)
    (late:(terminal s:Vec K (s+1))∉treeSpace A 7) : False := by
  classical
  obtain ⟨rfl,t,tn,gt⟩:=late13_mesh ha ho S C late
  obtain ⟨P,Q,pn,qn,gu,pd,_,repr⟩:=marked13_pure_literal_factor ha ho S M C dis pure
  have Pr:SevenProfile A 2 U w P:=⟨alg,dis,pn,by omega,repr⟩
  by_cases p0:P.eval 0=0
  · obtain ⟨R,e⟩ : (X:K[X])∣P := by simpa using (dvd_iff_isRoot (a:=(0:K))).mpr p0
    have rn:R≠0 := fun h=>pn (by rw [e,h,mul_zero])
    have rd:R.natDegree≤3 := by rw [e,natDegree_X_mul rn] at pd;omega
    exact cubic_from_late_marked_masks ha ho S M C Pr late R rn rd 0 (by decide) (by rwa [pow_zero,one_mul])
  · have hG:G=t•(X*oddSixPoly) := by rw [gt,odd6_as_oddSix]
    have h0 : Q.eval 0=0 := by
      have e:=congrArg (fun T:K[X]=>T.eval 0) gu
      rw [hG,eval_smul,eval_mul,eval_X,zero_mul,smul_zero,eval_mul] at e
      exact (mul_eq_zero.mp e.symm).resolve_left p0
    obtain ⟨J,hJ⟩ : (X:K[X])∣Q := by
      simpa using (dvd_iff_isRoot (a:=(0:K))).mpr h0
    have h : (t•(oddSixPoly:K[X]))=P*J := by
      apply mul_left_cancel₀ X_ne_zero
      rw [mul_smul_comm,←hG,gu,hJ]
      ring
    have pfactor : P∣(oddSixPoly:K[X]) := by
      use t⁻¹•J
      have hh:=congrArg (fun V:K[X]=>t⁻¹•V) h
      simpa only [smul_smul,inv_mul_cancel₀ tn,one_smul,mul_smul_comm] using hh
    obtain ⟨i,hi,hv,nz,tests⟩:=physical_late_marked_thirteen_knot ha ho S M C Pr late (X:K[X]) X_ne_zero (by simp)
    let z:=nodes A i
    have nu:z*P.eval z≠0 := by simpa only [eval_mul,eval_X] using nz
    have inn:z≠0 := fun hz=>nu (by rw [hz,zero_mul])
    have hn:P.eval z≠0 := fun hz=>nu (by rw [hz,mul_zero])
    have g : evalNodes A G∈chain (diag (nodes A)) U w (2+(6-4)) := by
      rw [←C.marked.edge]
      exact C.meshPaid
    obtain ⟨u,hu,L,_,gl⟩:=exists_head_poly g
    have ui:u i=0 := by by_contra hz;exact hi ⟨u,hu,hz⟩
    have e:=gl i
    change G.eval z=u i+L.eval z*w i at e
    rw [ui,hv,mul_zero,add_zero,hG,eval_smul,smul_eq_mul,eval_mul,eval_X,oddSixPoly_eval] at e
    apply fixed13_odd_divisor_nonzero P pd pfactor z
      (Or.inr ⟨(mul_eq_zero.mp ((mul_eq_zero.mp e).resolve_left tn)).resolve_left inn,hn⟩)
    have h := tests 1 (by simp)
    simpa only [one_mul] using h

end RKCert.Paired.FiniteMidpoint
