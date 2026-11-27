module

public import RKCert.ReviewedNative.ERK8CharElevenHighEarlySetup

import Mathlib.Tactic.FinCases
import Mathlib.Tactic.LinearCombination
import Mathlib.Tactic.Ring

@[expose] public section

/-! For a center at physical row four, the two actual primitive actions
on that row pin the preceding three-clock hull. The sentinel and its
causal zero give the fourth off clock without any reverse profile input. -/
namespace RKResearch.Certified.Graded.ERK8CharEleven

open RKResearch Polynomial OneOff ERKTaggedHorizon ERK8PaidField LobattoEight RKCert.Endpoint
open scoped Matrix Classical BigOperators

variable {K : Type*} [Field K]
variable {A : Matrix (Fin 10) (Fin 10) K} {b : Fin 10 → K}

theorem clean_primitive_action8 (ho : HasOrder 8 A b)
    {theta : K} (H : ExceptionalHead A theta) {i : Fin 10} (gi : g A i=0)
    (P : K[X]) (d : P.natDegree≤3) :
    mat A (evalNodes A P) i=(primitive P).eval (nodes A i) := by
  have e := clean_four_vanish H.fourthBand gi (primitive_defect_paid ho P d (by decide))
  exact sub_eq_zero.mp e

theorem origin_single_action (A : Matrix (Fin 10) (Fin 10) K) (i : Fin 10) (x : K) :
    mat A (Pi.single (0:Fin 10) x) i=A i 0*x := by
  change (∑ j, A i j*(Pi.single (0:Fin 10) x : Fin 10→K) j)=_
  rw [Finset.sum_eq_single (0:Fin 10)]
  · simp
  · intro j _ j0
    simp [j0]
  · simp

theorem high_off_of_center_four {j : Fin 10} (S : HighCenter A 4)
    (j0 : j≠0) (j4 : j≠4) (j9 : j≠9) : g A j≠0 := by
  intro z
  rcases (S.clean_iff j).mp z with e|e|e
  · exact j0 e
  · exact j4 e
  · exact j9 e

theorem high_tail_of_center_four {theta : K} (H : ExceptionalHead A theta)
    (S : HighCenter A 4) : HighPhysicalTail A 6 7 8 := by
  refine ⟨high_off_of_center_four S (by decide) (by decide) (by decide),
    high_off_of_center_four S (by decide) (by decide) (by decide),
    high_off_of_center_four S (by decide) (by decide) (by decide),by decide,by decide,?_,?_⟩
  · intro j gj
    have n9 : j≠(9:Fin 10) := fun e => gj (e.symm ▸ H.terminal_clean)
    fin_cases j <;> first | exact (n9 (by decide)).elim | decide
  · intro j gj late
    rcases (S.clean_iff j).mp gj with h|h|h
    · exact ((show ¬ ((6:Fin 10)<0) by decide) (h ▸ late)).elim
    · exact ((show ¬ ((6:Fin 10)<4) by decide) (h ▸ late)).elim
    · exact h.symm ▸ H.terminal_clock

noncomputable def earlyThreeClocks (A : Matrix (Fin 10) (Fin 10) K) : Finset K :=
  {nodes A 1,nodes A 2,nodes A 3}

noncomputable def earlyThreeHull (A : Matrix (Fin 10) (Fin 10) K) : K[X] :=
  nodalHull (earlyThreeClocks A)

theorem earlyThree_lookup (A : Matrix (Fin 10) (Fin 10) K) {j : Fin 10}
    (j0 : j≠0) (j4 : j<4) : nodes A j∈earlyThreeClocks A := by
  fin_cases j <;> first
    | exact (j0 (by decide)).elim
    | exact ((by decide : ¬ (_ < (4:Fin 10))) j4).elim
    | simp [earlyThreeClocks]

theorem earlyThree_quadratic_coprime {theta : K}
    (H : ExceptionalHead A theta) (S : HighCenter A 4) :
    IsCoprime (exceptionalQuadratic : K[X]) (earlyThreeHull A) := by
  unfold earlyThreeHull nodalHull
  apply IsCoprime.prod_right
  intro x hx
  simp only [earlyThreeClocks,Finset.mem_insert,Finset.mem_singleton] at hx
  have xn : (exceptionalQuadratic : K[X]).eval x≠0 := by
    rcases hx with h|h|h
    · rw [h]
      exact exceptional_quadratic_ne_off H (high_off_before_center S (j:=1) (by decide) (by decide))
    · rw [h]
      exact exceptional_quadratic_ne_off H (high_off_before_center S (j:=2) (by decide) (by decide))
    · rw [h]
      exact exceptional_quadratic_ne_off H (high_off_before_center S (j:=3) (by decide) (by decide))
  let q : K[X] := exceptionalQuadratic
  let alpha := q.eval x
  have z : q=(X-C x)*(X+C (x-1))+C alpha := by
    simp only [q,alpha,exceptionalQuadratic_eval,exceptionalQuadratic,map_add,map_sub,map_one,map_pow]
    ring
  refine ⟨C alpha⁻¹,-C alpha⁻¹*(X+C (x-1)),?_⟩
  have unit : ((C alpha⁻¹ : K[X])*C alpha)=1 := by rw [←map_mul,inv_mul_cancel₀ xn,map_one]
  linear_combination C alpha⁻¹*z+unit

/-- The first clean incoming coefficient at the origin follows from
the actual pure q action, with the fitted off defect factored out. -/
theorem early_four_origin_tap
    (ha : ∀ i j, i≤j → A i j=0) (ho : HasOrder 8 A b) (p : (11:K)=0)
    {theta : K} (H : ExceptionalHead A theta) (S : HighCenter A 4) :
    A 4 0= -1 := by
  let q : K[X] := exceptionalQuadratic
  have gc : g A 4=0 := (S.clean_iff 4).2 (Or.inr (Or.inl rfl))
  have gg : mat A (g A) 4=0 := clean_four_vanish H.fourthBand gc
    (zeroSpace_mono A (by decide : 3≤4) (mat_zeroSpace ho 2 (by decide) (mDef_mem A 1)))
  have e : mat A (evalNodes A q) 4=mat A (theta⁻¹ • g A+Pi.single (0:Fin 10) (8:K)) 4 := by
    apply causal_action_eq ha
    intro j j4
    simp only [evalNodes_apply,Pi.add_apply,Pi.smul_apply,smul_eq_mul]
    by_cases j0 : j=0
    · subst j
      have g0 := (S.clean_iff 0).2 (Or.inl rfl)
      simp [g0,S.origin_clock,q]
    · have gj := high_off_before_center S (lt_of_le_of_ne (Fin.zero_le _) (fun e => j0 e.symm)) j4
      rw [←H.fit j gj,←mul_assoc,inv_mul_cancel₀ H.scale_ne,one_mul]
      simp [j0,q]
  have prim := clean_primitive_action8 ho H gc q (exceptionalQuadratic_degree.trans (by decide : 2≤3))
  rw [S.center_clock,primitive_q_at_six ho p] at prim
  rw [e,map_add,Pi.add_apply,map_smul,Pi.smul_apply,gg,smul_zero,zero_add,origin_single_action] at prim
  have nz : (8:K)≠0 := (ho.natCast_isUnit (n:=8) (by decide) (by decide)).ne_zero
  apply mul_right_cancel₀ nz
  linear_combination prim+p

/-- The paid first clean row with only three preceding off clocks fixes
their hull remainder, with its explicit linear quotient. -/
theorem early_three_hull_remainder
    (ha : ∀ i j, i≤j → A i j=0) (ho : HasOrder 8 A b) (p : (11:K)=0)
    (seven : (offKnots A).card=7) (three : (cleanKnots A).card=3)
    {theta : K} (H : ExceptionalHead A theta) (S : HighCenter A 4) :
    ∃ beta : K, beta≠0 ∧ ∃ U : K[X], U.natDegree≤1 ∧
      earlyThreeHull A=C beta*(1-X)+exceptionalQuadratic*U := by
  let a := nodes A 1
  let c := nodes A 2
  let d := nodes A 3
  let s := a+c+d
  let t := a*c+a*d+c*d
  let r := a*c*d
  let N := earlyThreeHull A
  let q : K[X] := exceptionalQuadratic
  have inj := (order8_tag_injective_of_full_count (A:=A) (by omega)).2
  have g1 := high_off_before_center S (j:=1) (by decide) (by decide)
  have g2 := high_off_before_center S (j:=2) (by decide) (by decide)
  have g3 := high_off_before_center S (j:=3) (by decide) (by decide)
  have ac : a≠c := fun e => (by decide : (1:Fin 10)≠2) (inj _ _ g1 g2 e)
  have ad : a≠d := fun e => (by decide : (1:Fin 10)≠3) (inj _ _ g1 g3 e)
  have cd : c≠d := fun e => (by decide : (2:Fin 10)≠3) (inj _ _ g2 g3 e)
  have prod : N=(X-C a)*(X-C c)*(X-C d) := by
    change nodalHull ({a,c,d}:Finset K)=_
    unfold nodalHull
    rw [Finset.prod_insert (by simp [ac,ad]),Finset.prod_pair cd]
    ring
  have Nform : N=monomial 0 (-r)+monomial 1 t+monomial 2 (-s)+monomial 3 1 := by
    rw [prod]
    simp only [r,s,t,←C_mul_X_pow_eq_monomial,pow_zero,pow_one,map_add,map_mul,map_neg,map_one,
      one_mul,mul_one]
    ring
  have Nd : N.natDegree≤3 := by
    rw [show N.natDegree=(earlyThreeClocks A).card from natDegree_nodalHull _]
    change ({a,c,d}:Finset K).card≤3
    simp [Finset.card_insert_of_notMem,ac,ad,cd]
  have N0 : N.eval 0= -r := by rw [Nform]; simp [eval_monomial]
  have gc : g A 4=0 := (S.clean_iff 4).2 (Or.inr (Or.inl rfl))
  have rep : mat A (evalNodes A N) 4=mat A (Pi.single (0:Fin 10) (N.eval 0)) 4 := by
    apply causal_action_eq ha
    intro j jh
    by_cases j0 : j=0
    · subst j; simp [S.origin_clock]
    · have root : N.eval (nodes A j)=0 := nodalHull_eval_of_mem (earlyThree_lookup A j0 jh)
      simp [j0,root]
  have P := clean_primitive_action8 ho H gc N Nd
  rw [S.center_clock,rep,origin_single_action,early_four_origin_tap ha ho p H S,N0] at P
  have n2 := ERK8PaidField.two_ne ho
  have n3 : (3:K)≠0 := (ho.natCast_isUnit (n:=3) (by decide) (by decide)).ne_zero
  have n4 : (4:K)≠0 := (ho.natCast_isUnit (n:=4) (by decide) (by decide)).ne_zero
  have n7 : (7:K)≠0 := (ho.natCast_isUnit (n:=7) (by decide) (by decide)).ne_zero
  have v2 : (6:K)^2/2=7 := (div_eq_iff n2).mpr (by linear_combination 2*p)
  have v3 : (6:K)^3/3=6 := (div_eq_iff n3).mpr (by linear_combination 18*p)
  have v4 : (6:K)^4/4=5 := (div_eq_iff n4).mpr (by linear_combination 116*p)
  have pv : (primitive N).eval 6=5-6*s+7*t-6*r := by
    rw [Nform]
    simp only [map_add,primitive_monomial,eval_add,eval_monomial,Nat.reduceAdd,Nat.cast_one,
      Nat.cast_ofNat,div_one,pow_one,div_mul_eq_mul_div]
    calc
      _ = -r*6+t*((6:K)^2/2)-s*((6:K)^3/3)+(6:K)^4/4 := by simp only [div_eq_mul_inv]; ring
      _ = _ := by rw [v2,v3,v4]; ring
  rw [pv] at P
  have E : 5-6*s+7*t-7*r=0 := by linear_combination -P
  let beta := -8+8*s-r
  let gamma := t-7-s
  have eq : beta+gamma=0 := by
    have z : (7:K)*(beta+gamma)=0 := by
      dsimp only [beta,gamma]
      linear_combination E+(5*s-10)*p
    exact (mul_eq_zero.mp z).resolve_left n7
  have repr : N=C beta*(1-X)+q*(X+C (1-s)) := by
    rw [Nform]
    have h := congrArg (C : K→+*K[X]) eq
    dsimp only [beta,gamma] at h
    dsimp only [q,exceptionalQuadratic,beta]
    simp only [←C_mul_X_pow_eq_monomial,pow_zero,pow_one,mul_one,one_mul,map_add,map_zero,
      map_sub,map_neg,map_mul,map_ofNat,map_one] at h ⊢
    linear_combination X*h
  have bn : beta≠0 := by
    intro bz
    have div : q∣N := by rw [repr,bz,map_zero,zero_mul,zero_add]; exact dvd_mul_right _ _
    obtain ⟨U,V,hU⟩ := earlyThree_quadratic_coprime H S
    obtain ⟨R,hR⟩ := div
    change U*q+V*N=1 at hU
    have dz : q∣(1:K[X]) := ⟨U+V*R,by rw [hR] at hU; linear_combination -hU⟩
    exact one_ne_zero (low_quadratic_multiple_eq_zero (by simp) dz)
  exact ⟨beta,bn,X+C (1-s),natDegree_add_le_of_degree_le (by simp) (by simp),repr⟩

end RKResearch.Certified.Graded.ERK8CharEleven

#print axioms RKResearch.Certified.Graded.ERK8CharEleven.early_four_origin_tap
#print axioms RKResearch.Certified.Graded.ERK8CharEleven.early_three_hull_remainder
