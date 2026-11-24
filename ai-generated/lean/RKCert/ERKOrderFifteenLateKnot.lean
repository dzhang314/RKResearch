module
public import RKCert.ERKOrderFifteenFourCore
public import RKCert.ERKFiniteEndpointData

@[expose] public section

/-! # Both physical Jacobi endpoints in the uninterrupted rank-two chart -/
namespace RKCert.Paired.FiniteMidpoint
open RKCert.Paired RKCert.Paired.Clock RKCert.OneEscape RKCert.Endpoint Polynomial Module
open scoped Classical
variable {K : Type*} [Field K] [CharZero K] {s d : ℕ}
variable {A : Fin (s+1)→Fin (s+1)→K} {b : Vec K (s+1)}
variable {U : Submodule K (Vec K (s+1))} {w : Vec K (s+1)} {G P : K[X]}

omit [CharZero K] in
theorem weighted_plain_four_budget (w4:w∈defectPlus A d 4)
    (R:K[X]) (hr:R.natDegree≤3) :
    weightedEval (nodes A) w R∈defectPlus A d 7 := by
  apply weighted_paid
  intro k hk
  apply Fplus_mono A d _ (Fplus_power w4 k)
  have h := le_natDegree_of_mem_supp k hk
  omega

theorem physical_knot_of_paid {r j m n:ℕ} (ha:StrictLower A) (S:Saturated A b 7 1)
    (M:Margin A b 7 1 d) (H:MarkedHead A 7 d r U w) (Pr:SevenProfile A r U w P)
    (j7:j≤7) (fit:P.natDegree+m≤j)
    (hcore:U≤defectPlus A d j)
    (wpay:∀ R:K[X],R.natDegree≤m→weightedEval (nodes A) w R∈defectPlus A d j)
    (next: defectPlus A d (j+1)≤chain (diag (nodes A)) U w n)
    (Q:K[X]) (qn:Q≠0) (qd:Q.natDegree≤m) :
    ∃ k:Fin (s+1), ¬Live U k ∧ w k=0 ∧
      (Q*P).eval (nodes A k)≠0 ∧
      ∀ R:K[X], R.natDegree+Q.natDegree≤m→
        (Paired.primitive (R*(Q*P))).eval (nodes A k)=0 := by
  classical
  obtain ⟨e,he,eVal⟩:=core_indicator Pr.algebra
  let c := nodes A
  let F := Q*P
  let W : Vec K (s+1) := weightedEval c w Q+weightedEval c e F
  let v := evalNodes A F-W
  have Fdeg : F.natDegree≤j := natDegree_mul_le.trans (by omega)
  have hW : W∈defectPlus A d j := by
    exact Submodule.add_mem _
      (wpay _ (by omega))
      (hcore (weighted_core H F he))
  have vn : v≠0 := by
    intro h
    have eF : evalNodes A F=W := sub_eq_zero.mp h
    have z := separated_plus S M F (by omega)
      (by rw [eF];exact Fplus_mono A d (by omega) hW)
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
  have qdeg : (J*Q).natDegree≤m := natDegree_mul_le.trans hj
  have jdeg : T.natDegree≤j := by
    have h:=natDegree_mul_le (p:=J*Q) (q:=P)
    change (J*(Q*P)).natDegree≤j
    rw [←mul_assoc]
    omega
  have hWJ : WJ∈defectPlus A d j := by
    exact Submodule.add_mem _
      (wpay _ (by omega))
      (hcore (weighted_core H T he))
  have eq : weightedEval c v J=evalNodes A T-WJ := by
    ext i
    simp only [weightedEval_apply,evalNodes_apply,Pi.sub_apply,Pi.add_apply,v,W,WJ,T,eval_mul]
    ring
  have hA : mat A (evalNodes A T-WJ) k=0 := by
    rw [←eq]
    have h := strictlyCausal_mat ha k (weightedEval c v J) 0 (fun i hi=>by simp [before i hi])
    simpa only [map_zero,Pi.zero_apply] using h
  let y:=evalNodes A (Paired.primitive T)-mat A (evalNodes A T-WJ)
  have dF : mat A (evalNodes A T)-evalNodes A (Paired.primitive T)∈defectPlus A d (j+1) := by
    have h := primitive_defect A T jdeg
    exact (show zeroSpace A (j+1)≤defectPlus A d (j+1) from le_sup_left) (zeroSpace_mono A (by omega) h)
  have dW : mat A WJ∈defectPlus A d (j+1) :=
    Fplus_mono A d (by omega) (Fplus_mat ha d j ⟨_,hWJ,rfl⟩)
  have yh : y∈defectPlus A d (j+1) := by
    dsimp [y]
    rw [map_sub,show evalNodes A (Paired.primitive T)-(mat A (evalNodes A T)-mat A WJ)=
      -(mat A (evalNodes A T)-evalNodes A (Paired.primitive T))+mat A WJ by abel]
    exact Submodule.add_mem _ (Submodule.neg_mem _ dF) dW
  obtain ⟨u,hu,J0,_,h⟩:=exists_head_poly (next yh)
  have eFinal := h k
  change (Paired.primitive T).eval (c k)-mat A (evalNodes A T-WJ) k=u k+J0.eval (c k)*w k at eFinal
  rwa [hA,core_zero u hu,hwk,mul_zero,add_zero,sub_zero] at eFinal

theorem physical_odd_eight_knot (ha:StrictLower A) (S:Saturated A b 7 1)
    (M:Margin A b 7 1 d) (C:OddSevenChart A d 7 2 U w G) (Pr:SevenProfile A 2 U w P)
    (w4:w∈defectPlus A d 4) (e8:defectPlus A d 8=firstEscape A d 7)
    (Q:K[X]) (qn:Q≠0) (qd:Q.natDegree≤3) :
    ∃ k:Fin (s+1), ¬Live U k ∧ w k=0 ∧
      (Q*P).eval (nodes A k)≠0 ∧
      ∀ R:K[X], R.natDegree+Q.natDegree≤3→
        (Paired.primitive (R*(Q*P))).eval (nodes A k)=0 := by
  apply physical_knot_of_paid (j:=7) (m:=3) (n:=5) ha S M C.marked Pr (by decide)
    (by have := Pr.degree;omega) (C.marked.core.trans (Fplus_mono A d (by decide)))
    (weighted_plain_four_budget w4) _ Q qn qd
  rw [e8,C.marked.edge]

omit [CharZero K] in
theorem five_tests_from_paid_knot
    (test:∀ Q:K[X],Q≠0→Q.natDegree≤3→
      ∃ k:Fin (s+1), ¬Live U k ∧ w k=0 ∧
        (Q*P).eval (nodes A k)≠0 ∧ ∀ R:K[X],R.natDegree+Q.natDegree≤3→
          (primitive (R*(Q*P))).eval (nodes A k)=0) :
    ∃ u v:K, KnotPair P (0:K[X]) 8 u v := by
  obtain ⟨i,_,_,n₁,h₁⟩:=test (X:K[X]) X_ne_zero (by rw [natDegree_X];omega)
  let u:=nodes A i
  have un : u*P.eval u≠0 := by simpa [u] using n₁
  have u0 : u≠0 := fun e=>un (by rw [e,zero_mul])
  have pu : P.eval u≠0 := fun e=>un (by rw [e,mul_zero])
  let Q : K[X] := X*(X-Polynomial.C u)
  have qn : Q≠0 := mul_ne_zero X_ne_zero (X_sub_C_ne_zero _)
  have qd : Q.natDegree=2 := by
    dsimp [Q]
    rw [natDegree_mul X_ne_zero (X_sub_C_ne_zero _),natDegree_X,natDegree_X_sub_C]
  obtain ⟨j,_,_,n₂,h₂⟩:=test Q qn (by rw [qd];omega)
  let v:=nodes A j
  have nz : v*(v-u)*P.eval v≠0 := by simpa [Q,v] using n₂
  have v0 : v≠0 := by intro e;apply nz;simp [e]
  have vu : v≠u := by intro e;apply nz;simp [e]
  have vp : P.eval v≠0 := by intro e;apply nz;simp [e]
  refine ⟨u,v,⟨u0,v0,vu,pu,vp,eval_zero,eval_zero,?_,?_⟩⟩
  · intro k hk
    exact h₁ (X^k) (by rw [natDegree_X_pow,natDegree_X];omega)
  · intro k hk
    exact h₂ (X^k) (by rw [natDegree_X_pow,qd];omega)

theorem actual_odd_two_knots (ha:StrictLower A)
    (S:Saturated A b 7 1) (M:Margin A b 7 1 d)
    (C:OddSevenChart A d 7 2 U w G) (Pr:SevenProfile A 2 U w P)
    (w4:w∈defectPlus A d 4) (e8:defectPlus A d 8=firstEscape A d 7) :
    ∃ u v:K, KnotPair P (0:K[X]) 8 u v :=
  five_tests_from_paid_knot (physical_odd_eight_knot ha S M C Pr w4 e8)

theorem ordered_no_quartic_five [LinearOrder K] [IsStrictOrderedRing K] {P G:K[X]} {u v:K}
    (J:KnotPair P G 8 u v) (dP:P.natDegree≤4) : P=0 := by
  classical
  letI : DecidableEq K := fun x y => Classical.propDecidable (x=y)
  let e : Fin 5→K := fun k=>P.coeff k.val
  have eq:ofFn 5 e=P := ofFn_comp_toFn_eq_id_of_natDegree_lt (by omega)
  have z : e=0 := (RKCert.EndpointPhysical.rescale_eq_zero_iff e J.u_ne).mp <|
    RKCert.Endpoint.ordered_quartic_three_two _ _ (div_ne_zero J.v_ne J.u_ne)
      (fun h=>J.different ((div_eq_one_iff_eq J.u_ne).mp h))
      (RKCert.EndpointPhysical.normalize J.u_ne (endpoint_tests_three J (by decide) e eq))
  rw [←eq,z,map_zero]

theorem no_four_core_without_early_terminal [LinearOrder K] [IsStrictOrderedRing K]
    (ha:StrictLower A) (ho:HasTreeOrderAtLeast A b 15)
    (S:Saturated A b 7 1) (M:Margin A b 7 1 d) (C:OddSevenChart A d 7 2 U w G)
    (absent:d=0 ∨ terminal (K:=K) s∉treeSpace A 8)
    (d4:finrank K (zeroSpace A 4)=4) : False := by
  obtain ⟨v,P,C',v4,p⟩:=pure_four_profile ha ho S M C absent d4
  obtain ⟨u,v,J⟩:=actual_odd_two_knots ha S M C' p v4 (marked_eight_eq_edge ha ho S C' absent)
  exact p.nonzero (ordered_no_quartic_five J (by have := p.degree;omega))

/-- Every rank-two hypothetical 22-stage order-fifteen chart over an ordered
field is marked, and its actual terminal coordinate is already in E8. -/
theorem order15_rank_two_marked_terminal [LinearOrder K] [IsStrictOrderedRing K] {a:ℕ}
    (ha:StrictLower A) (ho:HasTreeOrderAtLeast A b 15)
    (S:Saturated A b 7 1) (M:Margin A b 7 1 d) (C:OddSevenChart A d a 2 U w G) :
    d=1 ∧ terminal (K:=K) s∈treeSpace A 8 := by
  obtain h7|⟨h6,de⟩:=C.chartType
  · subst a
    have dc : d≤1 := by have :=M.budget;omega
    by_contra denied
    have absent : d=0 ∨ terminal (K:=K) s∉treeSpace A 8 := by
      by_cases dz:d=0
      · exact Or.inl dz
      · exact Or.inr (fun h=>denied ⟨by omega,h⟩)
    have lower := zeroSpace_finrank ha ho (n:=3) (by decide)
    change 3≤finrank K (zeroSpace A 4) at lower
    have upper := Submodule.finrank_lt_finrank_of_lt (zeroSpace_strict_of_separated ha S.separated
      (j:=4) (by decide) (by decide))
    change finrank K (zeroSpace A 4)<finrank K (zeroSpace A 5) at upper
    rw [S.fRank 5 (by decide) (by decide)] at upper
    by_cases r3:finrank K (zeroSpace A 4)=3
    · exact no_three_masks_without_early_terminal ha ho S M C absent r3
    · exact no_four_core_without_early_terminal ha ho S M C absent (by omega)
  · exact ⟨de,(alias_forces_terminal_eight ha ho S M C h6).1⟩

end RKCert.Paired.FiniteMidpoint
