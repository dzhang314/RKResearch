module
public import RKCert.ERKOrder13FourCore
public import RKCert.ERKOrderedQ7Terminal

@[expose] public section

/-! # Only in the full-odd branch: paid low masks in the rank-four chart -/
namespace RKCert.Paired.FiniteMidpoint
open RKCert.Paired RKCert.Paired.Clock RKCert.OneEscape RKCert.Endpoint Polynomial Module
variable {K:Type*} [Field K] [LinearOrder K] [IsStrictOrderedRing K] {s r:ℕ}
variable {A:Fin (s+1)→Fin (s+1)→K} {b:Vec K (s+1)}
variable {U:Submodule K (Vec K (s+1))} {w:Vec K (s+1)} {G P:K[X]}
set_option maxHeartbeats 2800000

omit [LinearOrder K] [IsStrictOrderedRing K] in
theorem full13_four_power (S:Saturated A b 6 1) (C:Chart13 A 0 6 r U w G)
    (h4:finrank K (zeroSpace A 4)=4) {k:ℕ} (hk:k<r-1) :
    (diag (nodes A)^k) w∈zeroSpace A 4 := by
  rw [full13_four_exact S C.marked h4]
  exact ((chain_le_iff _).mp le_rfl).2 k hk

omit [LinearOrder K] [IsStrictOrderedRing K] in
theorem full13_four_square_band [CharZero K] (ha:StrictLower A) (ho:HasTreeOrderAtLeast A b 13)
    (S:Saturated A b 6 1) (M:Margin A b 6 1 0) (C:Chart13 A 0 6 r U w G)
    (h4:finrank K (zeroSpace A 4)=4) (hr:3≤r) :
    ∀ k≤2*r-4,(diag (nodes A)^k) (w*w)∈Band13 A 6 r U w 8 := by
  let c:=nodes A
  let D:=diag c
  have powPaid (k:ℕ) (hk:k≤2*r-4) : (D^k) (w*w)∈zeroSpace A 8 := by
    let f:=min k (r-2)
    let g:=k-f
    have e:f+g=k := by dsimp [g];have hf:=min_le_left k (r-2);omega
    have hf:f<r-1 := by dsimp [f];have := min_le_right k (r-2);omega
    have hg:g<r-1 := by dsimp [g,f];omega
    have p1 : (D^f) w∈zeroSpace A 4 := full13_four_power S C h4 hf
    have p2 : (D^g) w∈zeroSpace A 4 := full13_four_power S C h4 hg
    have ee : (D^k) (w*w) = ((D^f) w)*((D^g) w) := by
      ext i
      simp only [D,pow_diag_apply,Pi.mul_apply]
      rw [←e,pow_add]
      ring
    rw [ee]
    exact zeroSpace_mul (A:=A) (m:=4) (n:=4) p1 p2
  intro k hk
  let j:=min k (2*r-5)
  have e1 : D ((D^j) (w*w))=(D^(j+1)) (w*w) := by rw [pow_succ'];rfl
  have l : j≤2*r-5 := min_le_right ..
  have hz := order13_full_no_leak ha ho S M C (powPaid j (by omega))
    (by rw [e1];exact powPaid _ (by omega))
  have choose : k=j ∨ k=j+1 := by dsimp [j] at *;omega
  change (D^k) (w*w)∈Band13 A 6 r U w 8
  rcases choose with e|e
  · rw [e];exact hz.1
  · rw [e,←e1];exact hz.2

omit [LinearOrder K] [IsStrictOrderedRing K] in
theorem full13_four_profile [CharZero K] (ha:StrictLower A) (ho:HasTreeOrderAtLeast A b 13)
    (S:Saturated A b 6 1) (M:Margin A b 6 1 0) (C:Chart13 A 0 6 r U w G)
    (h4:finrank K (zeroSpace A 4)=4) (hr:3≤r) :
    ∃ v P,Chart13 A 0 6 r U v G ∧ SevenProfile A r U v P := by
  classical
  obtain ⟨v,C,mulc,dis⟩:=full13_clean_four_head ha ho S M C h4
  have cn : headLen 6 6 r 8<(headSites (nodes A) v).card := by
    have :=band13_sites C
    unfold headLen at *
    omega
  obtain ⟨P,pd,hP⟩:=multiplier_degree (a:=v) (d:=2*r-4) dis cn
    (full13_four_square_band ha ho S M C h4 hr)
  have pn:P≠0 := by
    intro hz
    obtain ⟨x,hx⟩:=Finset.card_pos.mp (show 0<(headSites (nodes A) v).card by omega)
    obtain ⟨i,hi,_⟩:=Finset.mem_image.mp hx
    have hi' := (Finset.mem_filter.mp hi).2
    exact hi' (by rw [hP _ hi',hz,eval_zero])
  have pdeg := pd.resolve_left pn
  unfold headLen at pdeg
  exact ⟨v,P,C,⟨mulc,dis,pn,by omega,hP⟩⟩

omit [LinearOrder K] [IsStrictOrderedRing K] in
theorem weighted_thirteen_budget (H:MarkedHead A 6 0 r U w) (R:K[X]) (hr:R.natDegree≤r) :
    weightedEval (nodes A) w R∈defectPlus A 0 6 := by
  rw [H.paid 6 (by decide) le_rfl]
  exact weighted_chain R (by omega)

theorem physical_thirteen_knot (ha:StrictLower A) (ho:HasTreeOrderAtLeast A b 13)
    (S:Saturated A b 6 1) (M:Margin A b 6 1 0) (C:Chart13 A 0 6 r U w G) (Pr:SevenProfile A r U w P)
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
  have hW : W∈defectPlus A 0 6 := by
    exact Submodule.add_mem _
      (weighted_thirteen_budget C.marked _ (by omega))
      (Fplus_mono A 0 (by omega) (C.marked.core (weighted_core C.marked F he)))
  have vn : v≠0 := by
    intro h
    have eF : evalNodes A F=W := sub_eq_zero.mp h
    have z := separated_plus S M F (by omega)
      (by rw [eF];exact Fplus_mono A 0 (by omega) hW)
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
  have hWJ : WJ∈defectPlus A 0 6 := by
    exact Submodule.add_mem _
      (weighted_thirteen_budget C.marked _ (by omega))
      (Fplus_mono A 0 (by omega) (C.marked.core (weighted_core C.marked T he)))
  have eq : weightedEval c v J=evalNodes A T-WJ := by
    ext i
    simp only [weightedEval_apply,evalNodes_apply,Pi.sub_apply,Pi.add_apply,v,W,WJ,T,eval_mul]
    ring
  have hA : mat A (evalNodes A T-WJ) k=0 := by
    rw [←eq]
    have h := strictlyCausal_mat ha k (weightedEval c v J) 0 (fun i hi=>by simp [before i hi])
    simpa only [map_zero,Pi.zero_apply] using h
  let y:=evalNodes A (Paired.primitive T)-mat A (evalNodes A T-WJ)
  have dF : mat A (evalNodes A T)-evalNodes A (Paired.primitive T)∈defectPlus A 0 7 := by
    have h := primitive_defect A T jdeg
    exact (show zeroSpace A 7≤defectPlus A 0 7 from le_sup_left) (zeroSpace_mono A (by omega) h)
  have dW : mat A WJ∈defectPlus A 0 7 :=
    Fplus_mono A 0 (by omega) (Fplus_mat ha 0 6 ⟨_,hWJ,rfl⟩)
  have yh : y∈defectPlus A 0 7 := by
    dsimp [y]
    rw [map_sub,show evalNodes A (Paired.primitive T)-(mat A (evalNodes A T)-mat A WJ)=
      -(mat A (evalNodes A T)-evalNodes A (Paired.primitive T))+mat A WJ by abel]
    exact Submodule.add_mem _ (Submodule.neg_mem _ dF) dW
  have jy := tail_zero_iff.mp yh
  rw [order13_full_exact_F7 ha ho C] at jy
  obtain ⟨u,hu,J0,_,h⟩:=exists_head_poly jy
  have eFinal := h k
  change (Paired.primitive T).eval (c k)-mat A (evalNodes A T-WJ) k=u k+J0.eval (c k)*w k at eFinal
  rwa [hA,core_zero u hu,hwk,mul_zero,add_zero,sub_zero] at eFinal

theorem cubic_from_thirteen_masks (ha:StrictLower A) (ho:HasTreeOrderAtLeast A b 13)
    (S:Saturated A b 6 1) (M:Margin A b 6 1 0) (C:Chart13 A 0 6 r U w G) (Pr:SevenProfile A r U w P)
    (R:K[X]) (rn:R≠0) (rd:R.natDegree≤3) (δ:ℕ) (hd:δ+2≤r)
    (fit:(X:K[X])^δ*P=X*R) : False := by
  let Q1 : K[X] := X^δ
  have Q1d : Q1.natDegree=δ := natDegree_X_pow _
  obtain ⟨i,_,_,uFit,uTests⟩:=physical_thirteen_knot ha ho S M C Pr Q1 (pow_ne_zero _ X_ne_zero) (by omega)
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
  obtain ⟨j,_,_,vFit,vTests⟩:=physical_thirteen_knot ha ho S M C Pr Q2 n2 (by omega)
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

theorem order13_full_rank_four_high_impossible (ha:StrictLower A) (ho:HasTreeOrderAtLeast A b 13)
    (S:Saturated A b 6 1) (M:Margin A b 6 1 0) (C:Chart13 A 0 6 r U w G)
    (h4:finrank K (zeroSpace A 4)=4) (hr:3≤r) : False := by
  classical
  obtain ⟨v,Q,C,T⟩:=full13_four_profile ha ho S M C h4 hr
  by_cases q0:Q.eval 0=0
  · have hdiv : (X:K[X])∣Q := by
      simpa using (dvd_iff_isRoot (a:=(0:K))).mpr q0
    obtain ⟨P,hP⟩:=hdiv
    have pn:P≠0 := by intro h;exact T.nonzero (by rw [hP,h,mul_zero])
    have cap:=T.degree
    have dp:=congrArg natDegree hP
    rw [natDegree_X_mul pn] at dp
    exact cubic_from_thirteen_masks ha ho S M C T P pn (by omega) 0 (by omega)
      (by simpa only [pow_zero,one_mul] using hP)
  · have cap:=T.degree
    exact cubic_from_thirteen_masks ha ho S M C T Q T.nonzero (by omega) 1 (by omega)
      (by simp only [pow_one])

end RKCert.Paired.FiniteMidpoint
