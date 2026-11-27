module
public import RKCert.ReviewedNative.ERK8CharElevenFourEarlyNewton
public import RKCert.ReviewedNative.ERK8CharElevenFiveEarlyFour
import Mathlib.Tactic.FinCases
import Mathlib.Tactic.LinearCombination
import Mathlib.Tactic.Ring

@[expose] public section

/-! Early-three hull from the literal four-off row-four center. -/
namespace RKResearch.Certified.Graded.ERK8CharEleven.FourOff

open RKResearch Polynomial Module OneOff ERKTaggedHorizon ERK8PaidField LobattoEight RKCert.Endpoint
open FourOffPhysical
open FiveOff (CenterPrefix)
open scoped Matrix Classical BigOperators

variable {K : Type*} [Field K]
variable {A : Matrix (Fin 10) (Fin 10) K} {b : Fin 10 → K}

/-- The paid first clean row with only three preceding off clocks fixes
their hull remainder, with its explicit linear quotient. -/
theorem early_three_hull_remainder
    (ha : ∀ i j, i≤j → A i j=0) (ho : HasOrder 8 A b) (p : (11:K)=0)
    (distinct : EarlyOffDistinct A)
    {theta : K} (H : ExceptionalHead A theta) (S : CenterPrefix A 4) :
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
  have inj (j l : Fin 10) (gj : g A j≠0) (gl : g A l≠0) (j6 : j < 6) (l6 : l < 6) := distinct j l j6 l6 gj gl
  have g1 := FiveOff.high_off_before_center S (j:=1) (by decide) (by decide)
  have g2 := FiveOff.high_off_before_center S (j:=2) (by decide) (by decide)
  have g3 := FiveOff.high_off_before_center S (j:=3) (by decide) (by decide)
  have ac : a≠c := fun e => (by decide : (1:Fin 10)≠2) (inj _ _ g1 g2 (by decide) (by decide) e)
  have ad : a≠d := fun e => (by decide : (1:Fin 10)≠3) (inj _ _ g1 g3 (by decide) (by decide) e)
  have cd : c≠d := fun e => (by decide : (2:Fin 10)≠3) (inj _ _ g2 g3 (by decide) (by decide) e)
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
  have gc : g A 4=0 := S.center_clean
  have rep : mat A (evalNodes A N) 4=mat A (Pi.single (0:Fin 10) (N.eval 0)) 4 := by
    apply causal_action_eq ha
    intro j jh
    by_cases j0 : j=0
    · subst j; simp [S.origin_clock]
    · have root : N.eval (nodes A j)=0 := nodalHull_eval_of_mem (earlyThree_lookup A j0 jh)
      simp [j0,root]
  have P := clean_primitive_action8 ho H gc N Nd
  rw [S.center_clock,rep,origin_single_action,FiveOff.early_four_origin_tap ha ho p H S,N0] at P
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
    obtain ⟨U,V,hU⟩ := FiveOff.earlyThree_quadratic_coprime H S
    obtain ⟨R,hR⟩ := div
    change U*q+V*N=1 at hU
    have dz : q∣(1:K[X]) := ⟨U+V*R,by rw [hR] at hU; linear_combination -hU⟩
    exact one_ne_zero (low_quadratic_multiple_eq_zero (by simp) dz)
  exact ⟨beta,bn,X+C (1-s),natDegree_add_le_of_degree_le (by simp) (by simp),repr⟩

end RKResearch.Certified.Graded.ERK8CharEleven.FourOff

#print axioms RKResearch.Certified.Graded.ERK8CharEleven.FourOff.early_three_hull_remainder
