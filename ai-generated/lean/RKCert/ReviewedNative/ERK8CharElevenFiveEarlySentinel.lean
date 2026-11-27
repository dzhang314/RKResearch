module
public import RKCert.ReviewedNative.ERK8CharElevenFiveEarlyFour
import Mathlib.Tactic.FinCases
import Mathlib.Tactic.LinearCombination
import Mathlib.Tactic.Ring

@[expose] public section

/-! Exact fourth off clock and early remainder in the literal five-off row-four chart. -/
namespace RKResearch.Certified.Graded.ERK8CharEleven.FiveOff

open RKResearch Polynomial Module OneOff ERKTaggedHorizon ERK8PaidField LobattoEight RKCert.Endpoint
open RKResearch.Certified.Graded.ERK8CharEleven
open scoped Matrix Classical BigOperators

variable {K : Type*} [Field K]
variable {A : Matrix (Fin 10) (Fin 10) K} {b : Fin 10 → K}


noncomputable def earlyFourClocks (A : Matrix (Fin 10) (Fin 10) K) : Finset K :=
  insert (nodes A 5) (earlyThreeClocks A)

noncomputable def earlyFourHull (A : Matrix (Fin 10) (Fin 10) K) : K[X] :=
  nodalHull (earlyFourClocks A)

theorem early_n4_from_off_row_five
    (five : (offKnots A).card=5) (cleanFive : (cleanKnots A).card=5)
    (S : CenterPrefix A 4) (g5 : g A 5≠0) :
    earlyFourHull A=(X-C (nodes A 5))*earlyThreeHull A ∧ (earlyFourClocks A).card=4 := by
  have inj := (order8_tag_injective_of_full_count (A:=A) (by omega)).2
  have g1 := high_off_before_center S (j:=1) (by decide) (by decide)
  have g2 := high_off_before_center S (j:=2) (by decide) (by decide)
  have g3 := high_off_before_center S (j:=3) (by decide) (by decide)
  have d12 : nodes A 1≠nodes A 2 := fun h => (by decide : (1:Fin 10)≠2) (inj _ _ g1 g2 h)
  have d13 : nodes A 1≠nodes A 3 := fun h => (by decide : (1:Fin 10)≠3) (inj _ _ g1 g3 h)
  have d23 : nodes A 2≠nodes A 3 := fun h => (by decide : (2:Fin 10)≠3) (inj _ _ g2 g3 h)
  have notmem : nodes A 5∉earlyThreeClocks A := by
    intro m
    simp only [earlyThreeClocks,Finset.mem_insert,Finset.mem_singleton] at m
    rcases m with e|e|e
    · exact (by decide : (5:Fin 10)≠1) (inj _ _ g5 g1 e)
    · exact (by decide : (5:Fin 10)≠2) (inj _ _ g5 g2 e)
    · exact (by decide : (5:Fin 10)≠3) (inj _ _ g5 g3 e)
  constructor
  · unfold earlyFourHull earlyThreeHull earlyFourClocks nodalHull
    exact Finset.prod_insert notmem
  · rw [earlyFourClocks,Finset.card_insert_of_notMem notmem]
    simp [earlyThreeClocks,Finset.card_insert_of_notMem,d12,d13,d23]

theorem five_off_early_chart_of_center_four
    (ha : ∀ i j, i≤j → A i j=0) (ho : HasOrder 8 A b) (p : (11:K)=0)
    (five : (offKnots A).card=5) (cleanFive : (cleanKnots A).card=5)
    {theta : K} (H : ExceptionalHead A theta) (S : CenterPrefix A 4) :
    nodes A 5=2 ∧ g A 5≠0 ∧
    ∃ beta : K, beta≠0 ∧ ∃ V : K[X],
      earlyFourHull A=C beta*(C 6+C 2*X)+exceptionalQuadratic*V := by
  obtain ⟨beta,bn,U,Ud,Nrem⟩ := early_three_hull_remainder ha ho p five cleanFive H S
  let q : K[X] := exceptionalQuadratic
  let C₀ : K[X] := earlySentinel
  let N := earlyThreeHull A
  let D := earlyFourHull A
  let e := nodes A 5
  let tau := (9:K)/beta
  let V := C theta⁻¹*(C tau*U-(X+C 3))
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
      have g0 := S.origin_clean
      simp [g0,S.origin_clock,C₀,earlySentinel]
    by_cases j4 : j=4
    · subst j
      have gc := S.center_clean
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
  have g5 : g A 5≠0 := by
    intro g5
    have inj := (order8_tag_injective_of_full_count (A:=A) (by omega)).1
    rcases H.clean_roots 5 g5 with e0|e1|e6|rq
    · exact (by decide : (5:Fin 10)≠0) (inj _ _ g5 S.origin_clean (e0.trans S.origin_clock.symm))
    · exact (by decide : (5:Fin 10)≠Fin.last 9) (H.terminal_unique 5 g5 e1)
    · exact (by decide : (5:Fin 10)≠4) (inj _ _ g5 S.center_clean (e6.trans S.center_clock.symm))
    have ka := clean_four_vanish H.fourthBand g5 em
    change mat A W 5-(primitive C₀).eval (nodes A 5)=0 at ka
    rw [Av0 5 (by decide),zero_sub,neg_eq_zero] at ka
    change (primitive (earlySentinel : K[X])).eval (nodes A 5)=0 at ka
    rw [earlySentinel_primitive_remainder ho p] at ka
    simp only [eval_add,eval_mul,eval_C,eval_X,rq,zero_mul,add_zero] at ka
    have q8 : nodes A 5=8 := by linear_combination 8*ka-(8+5*nodes A 5)*p
    rw [exceptionalQuadratic_eval,q8] at rq
    exact one_ne_zero (by linear_combination 5*rq-29*p : (1:K)=0)
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
  let S₄ := earlyFourClocks A
  obtain ⟨fact,S₄card⟩ := early_n4_from_off_row_five five cleanFive S g5
  have fz (x : K) (hx : x∈S₄) : F.eval x=0 := by
    simp only [S₄,earlyFourClocks,earlyThreeClocks,Finset.mem_insert,Finset.mem_singleton] at hx
    rcases hx with ee|ee|ee|ee
    · rw [ee]
      exact rz 5 g5 (by decide)
    · rw [ee]
      exact rz 1 (high_off_before_center S (by decide) (by decide)) (by decide)
    · rw [ee]
      exact rz 2 (high_off_before_center S (by decide) (by decide)) (by decide)
    · rw [ee]
      exact rz 3 (high_off_before_center S (by decide) (by decide)) (by decide)
  obtain ⟨gamma,hg⟩ := polynomial_hull_of_test_zeros S₄ F (by
    change F.natDegree≤(earlyFourClocks A).card
    rw [S₄card]
    exact Fd) fz
  change F=C gamma*D at hg
  change D=(X-C e)*N at fact
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
  refine ⟨e2,g5,beta,bn,(X-C e)*U-C beta,?_⟩
  change D=C beta*(C 6+C 2*X)+q*((X-C e)*U-C beta)
  rw [Drem,e2,show (8:K)-2=6 by ring]

end RKResearch.Certified.Graded.ERK8CharEleven.FiveOff

#print axioms RKResearch.Certified.Graded.ERK8CharEleven.FiveOff.five_off_early_chart_of_center_four
