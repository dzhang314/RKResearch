module

public import RKCert.ReviewedNative.ERK8CharElevenHighEarlyFour

import Mathlib.Tactic.Abel
import Mathlib.Tactic.LinearCombination
import Mathlib.Tactic.Ring

@[expose] public section

/-! ## The paid fourth off clock after physical clean row four
The paid sentinel kills its physical prefix, and the exact primitive
remainder forces clock 2. Its output is the complete early chart for
the previously verified seven-off late contradiction. -/
namespace RKResearch.Certified.Graded.ERK8CharEleven

open RKResearch Polynomial OneOff ERKTaggedHorizon ERK8PaidField LobattoEight RKCert.Endpoint
open scoped Classical Matrix BigOperators

variable {K : Type*} [Field K]
variable {A : Matrix (Fin 10) (Fin 10) K} {b : Fin 10 → K}

noncomputable def earlySentinel : K[X] := X*(X-C 6)*(X+C 8)

theorem earlySentinel_degree : (earlySentinel : K[X]).natDegree≤3 := by
  unfold earlySentinel
  have h : ((X:K[X])+C 8).natDegree≤1 := natDegree_add_le_of_degree_le (by simp) (by simp)
  exact natDegree_mul_le_of_le
    (natDegree_mul_le_of_le (show (X:K[X]).natDegree≤1 by simp) (natDegree_X_sub_C_le _)) h

theorem earlySentinel_remainder (p : (11:K)=0) :
    (earlySentinel : K[X])=C 9*(1-X)+exceptionalQuadratic*(X+C 3) := by
  have pP := polynomial_char11 p
  simp only [earlySentinel,exceptionalQuadratic,map_ofNat]
  linear_combination (-4*(X:K[X])-3)*pP

theorem earlySentinel_primitive_remainder (ho : HasOrder 8 A b) (p : (11:K)=0) :
    primitive (earlySentinel : K[X])=C 10+C 7*X+exceptionalQuadratic*(C 3*X^2+C 7) := by
  have expr : (earlySentinel : K[X])=monomial 1 (-48)+monomial 2 2+monomial 3 1 := by
    simp only [earlySentinel,←C_mul_X_pow_eq_monomial,pow_one,map_neg,map_one,map_ofNat,one_mul]
    ring
  have n2 := ERK8PaidField.two_ne ho
  have n3 : (3:K)≠0 := (ho.natCast_isUnit (n:=3) (by decide) (by decide)).ne_zero
  have n4 : (4:K)≠0 := (ho.natCast_isUnit (n:=4) (by decide) (by decide)).ne_zero
  have d2 : (-48:K)/2=-24 := (div_eq_iff n2).mpr (by ring)
  have d3 : (2:K)/3=8 := (div_eq_iff n3).mpr (by linear_combination -2*p)
  have d4 : (1:K)/4=3 := (div_eq_iff n4).mpr (by linear_combination -p)
  rw [expr]
  simp only [map_add,primitive_monomial,Nat.reduceAdd,Nat.cast_ofNat,d2,d3,d4]
  have pP := polynomial_char11 p
  simp only [←C_mul_X_pow_eq_monomial,exceptionalQuadratic,map_neg,map_ofNat]
  linear_combination ((X:K[X])^3-5*X^2-6)*pP

theorem early_n4_sites_of_center_four
    (seven : (offKnots A).card=7) (three : (cleanKnots A).card=3)
    {theta : K} (H : ExceptionalHead A theta) (S : HighCenter A 4) :
    offKnots A \ highTailClocks A 6 7 8 = insert (nodes A 5) (earlyThreeClocks A) := by
  let T := high_tail_of_center_four H S
  have inj := (order8_tag_injective_of_full_count (A:=A) (by omega)).2
  have inc {j : Fin 10} (gj : g A j≠0) (j6 : j<6) :
      nodes A j∈offKnots A \ highTailClocks A 6 7 8 := by
    refine Finset.mem_sdiff.mpr ⟨mem_offKnots.mpr ⟨j,gj,rfl⟩,?_⟩
    intro h
    simp only [highTailClocks,Finset.mem_insert,Finset.mem_singleton] at h
    rcases h with e|e|e
    · exact (ne_of_lt j6) (inj _ _ gj T.f_off e)
    · exact (ne_of_lt (j6.trans T.fu)) (inj _ _ gj T.u_off e)
    · exact (ne_of_lt (j6.trans (T.fu.trans T.uv))) (inj _ _ gj T.v_off e)
  ext x
  constructor
  · intro m
    obtain ⟨j,gj,rfl⟩ := mem_offKnots.mp (Finset.mem_sdiff.mp m).1
    have ne := (Finset.mem_sdiff.mp m).2
    have before : j<(6:Fin 10) := by
      rcases T.earlier j gj with e|e|e|e
      · exact e
      · exact (ne (by simp [highTailClocks,e])).elim
      · exact (ne (by simp [highTailClocks,e])).elim
      · exact (ne (by simp [highTailClocks,e])).elim
    by_cases j5 : j=5
    · simp [j5]
    have j0 : j≠0 := fun e => gj ((S.clean_iff j).2 (Or.inl e))
    have j4 : j≠4 := fun e => gj ((S.clean_iff j).2 (Or.inr (Or.inl e)))
    have lt4 : j<4 := by
      have a : j.val≠4 := fun e => j4 (Fin.ext e)
      have b : j.val≠5 := fun e => j5 (Fin.ext e)
      change j.val<6 at before
      change j.val<4
      omega
    exact Finset.mem_insert_of_mem (earlyThree_lookup A j0 lt4)
  · intro m
    simp only [earlyThreeClocks,Finset.mem_insert,Finset.mem_singleton] at m
    rcases m with h|h|h|h
    · rw [h]
      exact inc (high_off_of_center_four S (by decide) (by decide) (by decide)) (by decide)
    · rw [h]
      exact inc (high_off_of_center_four S (by decide) (by decide) (by decide)) (by decide)
    · rw [h]
      exact inc (high_off_of_center_four S (by decide) (by decide) (by decide)) (by decide)
    · rw [h]
      exact inc (high_off_of_center_four S (by decide) (by decide) (by decide)) (by decide)

theorem early_n4_factor_of_center_four
    (seven : (offKnots A).card=7) (three : (cleanKnots A).card=3)
    {theta : K} (H : ExceptionalHead A theta) (S : HighCenter A 4) :
    highPrefixHull A 6 7 8=(X-C (nodes A 5))*earlyThreeHull A := by
  have inj := (order8_tag_injective_of_full_count (A:=A) (by omega)).2
  have g5 := high_off_of_center_four S (j:=5) (by decide) (by decide) (by decide)
  have g1 := high_off_of_center_four S (j:=1) (by decide) (by decide) (by decide)
  have g2 := high_off_of_center_four S (j:=2) (by decide) (by decide) (by decide)
  have g3 := high_off_of_center_four S (j:=3) (by decide) (by decide) (by decide)
  have notmem : nodes A 5∉earlyThreeClocks A := by
    intro m
    simp only [earlyThreeClocks,Finset.mem_insert,Finset.mem_singleton] at m
    rcases m with e|e|e
    · exact (by decide : (5:Fin 10)≠1) (inj _ _ g5 g1 e)
    · exact (by decide : (5:Fin 10)≠2) (inj _ _ g5 g2 e)
    · exact (by decide : (5:Fin 10)≠3) (inj _ _ g5 g3 e)
  rw [highPrefixHull,early_n4_sites_of_center_four seven three H S]
  unfold nodalHull earlyThreeHull
  exact Finset.prod_insert notmem

/-- All early receipts under the literal physical row-four center:
index 5 has clock 2 and the actual first-four-off hull has the needed
nonzero linear remainder. -/
theorem seven_off_early_chart_of_center_four
    (ha : ∀ i j, i≤j → A i j=0) (ho : HasOrder 8 A b) (p : (11:K)=0)
    (seven : (offKnots A).card=7) (three : (cleanKnots A).card=3)
    {theta : K} (H : ExceptionalHead A theta) (S : HighCenter A 4) :
    nodes A 5=2 ∧ HighPhysicalTail A 6 7 8 ∧
    (∃ beta : K, beta≠0 ∧ ∃ V : K[X],
      highPrefixHull A 6 7 8=C beta*(C 6+C 2*X)+exceptionalQuadratic*V) ∧
    (2:K)∈offKnots A \ highTailClocks A 6 7 8 := by
  obtain ⟨beta,bn,U,Ud,Nrem⟩ := early_three_hull_remainder ha ho p seven three H S
  let q : K[X] := exceptionalQuadratic
  let C₀ : K[X] := earlySentinel
  let N := earlyThreeHull A
  let D := highPrefixHull A 6 7 8
  let e := nodes A 5
  let tau := (9:K)/beta
  let V := C theta⁻¹*(C tau*U-(X+C 3))
  have t : HighPhysicalTail A 6 7 8 := high_tail_of_center_four H S
  have Vbase : ((X:K[X])+C 3).natDegree≤1 := natDegree_add_le_of_degree_le (by simp) (by simp)
  have Vd : V.natDegree≤1 :=
    (natDegree_C_mul_le _ _).trans (natDegree_sub_le_of_le ((natDegree_C_mul_le _ _).trans Ud) Vbase)
  have Cin := earlySentinel_remainder (K:=K) p
  change C₀=C 9*(1-X)+q*(X+C 3) at Cin
  change N=C beta*(1-X)+q*U at Nrem
  have Vfit : C₀+(C theta*q)*V=C tau*N := by
    have tb : (C tau*C beta : K[X])=C 9 := by rw [←map_mul,div_mul_cancel₀ _ bn]
    have tn : (C theta*C theta⁻¹ : K[X])=1 := by rw [←map_mul,mul_inv_cancel₀ H.scale_ne,map_one]
    dsimp only [V]
    rw [Cin,Nrem]
    linear_combination (q*(C tau*U-(X+C 3)))*tn-(1-X)*tb
  let W : Fin 10→K := evalNodes A C₀+diag (g A) (evalNodes A V)
  have zero (j : Fin 10) (j5 : j<5) : W j=0 := by
    simp only [W,Pi.add_apply,evalNodes_apply,diag_apply]
    by_cases j0 : j=0
    · subst j
      have g0 := (S.clean_iff 0).2 (Or.inl rfl)
      simp [g0,S.origin_clock,C₀,earlySentinel]
    by_cases j4 : j=4
    · subst j
      have gc := (S.clean_iff 4).2 (Or.inr (Or.inl rfl))
      simp [gc,S.center_clock,C₀,earlySentinel]
    have lt : j<4 := by
      have z : j.val≠4 := fun e => j4 (Fin.ext e)
      change j.val<5 at j5
      change j.val<4
      omega
    have gj := high_off_before_center S (lt_of_le_of_ne (Fin.zero_le _) (fun h => j0 h.symm)) lt
    have root : N.eval (nodes A j)=0 := nodalHull_eval_of_mem (earlyThree_lookup A j0 lt)
    have ve := congrArg (fun P : K[X] => P.eval (nodes A j)) Vfit
    simp only [eval_add,eval_mul,eval_C,root,mul_zero] at ve
    rw [←H.fit j gj]
    exact ve
  have Av0 (j : Fin 10) (j5 : j≤5) : mat A W j=0 :=
    causal_mat ha j W (fun l lj => zero l (lj.trans_le j5))
  have vm : diag (g A) (evalNodes A V)∈zeroSpace A 3 := band_le A 1 (band_iff.mpr ⟨V,Vd,rfl⟩)
  have cav := mat_zeroSpace ho 3 (by decide) vm
  have dc : C₀.natDegree≤3 := earlySentinel_degree
  have dif := primitive_defect_paid ho C₀ dc (by decide)
  have em : mat A W-evalNodes A (primitive C₀)∈zeroSpace A 4 := by
    have e := (zeroSpace A 4).add_mem dif cav
    convert e using 1
    simp only [W,map_add]
    abel
  rw [H.fourthBand] at em
  obtain ⟨R,Rd,rEq⟩ := band_iff.mp em
  let F := primitive C₀+(C theta*q)*R
  have mon : C 10+C 7*X+q*(C 3*X^2+C 7) = primitive C₀ :=
    (earlySentinel_primitive_remainder ho p).symm
  have Frem : F=C 10+C 7*X+q*(C 3*X^2+C 7+C theta*R) := by
    dsimp only [F]
    rw [←mon]
    ring
  have Fd : F.natDegree≤4 :=
    natDegree_add_le_of_degree_le (primitive_natDegree_le dc)
      (natDegree_mul_le_of_le ((natDegree_C_mul_le _ _).trans exceptionalQuadratic_degree) Rd)
  have Fn : F≠0 := by
    intro fz
    have dvd : q∣(C 10+C 7*X : K[X]) := by
      refine ⟨-(C 3*X^2+C 7+C theta*R),?_⟩
      linear_combination fz-Frem
    have eq := low_quadratic_multiple_eq_zero (affine_degree_le (10:K) 7) dvd
    have c := congrArg (fun P : K[X] => P.coeff 0) eq
    have n10 : (10:K)≠0 := fun e => one_ne_zero (by linear_combination p-e : (1:K)=0)
    exact n10 (by simpa [coeff_C,coeff_X] using c)
  have rz (j : Fin 10) (gj : g A j≠0) (j5 : j≤5) : F.eval (nodes A j)=0 := by
    have eq := congrFun rEq j
    simp only [Pi.sub_apply,diag_apply,evalNodes_apply,Av0 j j5,zero_sub] at eq
    rw [←H.fit j gj] at eq
    simp only [F,eval_add,eval_mul,eval_C]
    linear_combination -eq
  let S₄ := offKnots A \ highTailClocks A 6 7 8
  have S₄card : S₄.card=4 := (natDegree_nodalHull _).symm.trans (highPrefixHull_degree seven three t)
  have fz (x : K) (hx : x∈S₄) : F.eval x=0 := by
    obtain ⟨j,gj,rfl⟩ := mem_offKnots.mp (Finset.mem_sdiff.mp hx).1
    have ne := (Finset.mem_sdiff.mp hx).2
    have b : j<(6:Fin 10) := by
      rcases t.earlier j gj with h|h|h|h
      · exact h
      · exact (ne (by simp [highTailClocks,h])).elim
      · exact (ne (by simp [highTailClocks,h])).elim
      · exact (ne (by simp [highTailClocks,h])).elim
    have le5 : j≤(5:Fin 10) := by change j.val<6 at b; change j.val≤5; omega
    exact rz j gj le5
  obtain ⟨gamma,hg⟩ := polynomial_hull_of_test_zeros S₄ F (by rw [S₄card]; exact Fd) fz
  change F=C gamma*D at hg
  have fact : D=(X-C e)*N := early_n4_factor_of_center_four seven three H S
  have Drem : D=C beta*(C (8-e)+C e*X)+q*((X-C e)*U-C beta) := by
    rw [fact,Nrem]
    dsimp only [q,exceptionalQuadratic]
    simp only [map_sub,map_ofNat]
    ring
  let M₀ : K[X] := C 10+C 7*X
  let M₁ : K[X] := C (gamma*beta)*(C (8-e)+C e*X)
  have Hd₀ : M₀.natDegree≤1 := affine_degree_le _ _
  have Hd₁ : M₁.natDegree≤1 := (natDegree_C_mul_le _ _).trans (affine_degree_le _ _)
  have dvd : q∣M₀-M₁ := by
    refine ⟨C gamma*((X-C e)*U-C beta)-(C 3*X^2+C 7+C theta*R),?_⟩
    dsimp only [M₀,M₁]
    rw [map_mul]
    linear_combination hg-Frem+C gamma*Drem
  have M := sub_eq_zero.mp (low_quadratic_multiple_eq_zero (natDegree_sub_le_of_le Hd₀ Hd₁) dvd)
  have c0 := congrArg (fun P : K[X] => P.coeff 0) M
  have c1 := congrArg (fun P : K[X] => P.coeff 1) M
  have u0 : (10:K)=gamma*beta*(8-e) := by
    simpa only [M₀,M₁,coeff_add,coeff_C_mul,coeff_X_zero,coeff_C_zero,mul_zero,add_zero] using c0
  have u1 : (7:K)=gamma*beta*e := by
    simp only [M₀,M₁,coeff_add,coeff_C_mul,coeff_X_one,coeff_C,one_ne_zero,ite_false,mul_one,zero_add] at c1
    exact c1
  have m : 7*(8-e)-10*e=0 := by linear_combination (8-e)*u1-e*u0
  have e2 : e=2 := by linear_combination -2*m-(3*e-10)*p
  refine ⟨e2,t,⟨beta,bn,(X-C e)*U-C beta,?_⟩,?_⟩
  · change D=C beta*(C 6+C 2*X)+q*((X-C e)*U-C beta)
    rw [Drem,e2,show (8:K)-2=6 by ring]
  · rw [early_n4_sites_of_center_four seven three H S,←e2]
    exact Finset.mem_insert_self _ _

theorem seven_off_contradiction_of_center_four
    (ha : ∀ i j, i≤j → A i j=0) (ho : HasOrder 8 A b) (p : (11:K)=0)
    (seven : (offKnots A).card=7) (three : (cleanKnots A).card=3)
    {theta : K} (H : ExceptionalHead A theta) (S : HighCenter A 4) : False := by
  obtain ⟨_,tail,early,two⟩ := seven_off_early_chart_of_center_four ha ho p seven three H S
  exact seven_off_contradiction_of_early_chart ha ho p seven three tail early two

end RKResearch.Certified.Graded.ERK8CharEleven

#print axioms RKResearch.Certified.Graded.ERK8CharEleven.seven_off_early_chart_of_center_four
#print axioms RKResearch.Certified.Graded.ERK8CharEleven.seven_off_contradiction_of_center_four
