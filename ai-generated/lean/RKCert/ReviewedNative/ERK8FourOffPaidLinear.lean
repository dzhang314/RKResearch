module

public import RKCert.ReviewedNative.ERK8FourOffPaidTerminal
public import RKCert.ReviewedNative.ERK8FourOffPaidQuadraticClosure

import Mathlib.Tactic.LinearCombination
import Mathlib.Tactic.NormNum
import Mathlib.Tactic.Ring

@[expose] public section

/-! # The genuine linear head specialization (characteristics 37 and 41)
Degree four is retained in both actual quotients. The possible leading
term of the probe cancels on the two monic hulls. -/
namespace RKResearch.Certified.Graded.FourOffNewton

open Polynomial RKResearch RKCert.Endpoint OneOff ERKTaggedHorizon FourOffPhysical ERK8CharEleven ERK8PaidField
open RKResearch.Certified.Graded.MultiOff.FourOff8CleanShape
open scoped Classical Matrix

variable {K : Type*} [Field K]

theorem measure_quotient_four_linear {P G : K[X]}
    (p1 : P.natDegree=1) (gd : G.natDegree≤4)
    {S : Finset K} (sc : S.card=4) (nz : ∀ x∈S,P.eval x≠0) :
    ∃ a : K, P*nodalDivide P S G-G=C a*nodalHull S ∧
      a=P.coeff 1*nodalMeasure P S G-G.coeff 4 := by
  have ud : (nodalDivide P S G).natDegree≤3 := nodalDivide_degree P S G sc
  have d : (P*nodalDivide P S G-G).natDegree≤4 :=
    natDegree_sub_le_of_le (natDegree_mul_le_of_le p1.le ud) gd
  obtain ⟨a,v⟩ := polynomial_hull_of_test_zeros S _ (sc.symm ▸ d) (by
    intro t ht
    simp only [eval_sub,eval_mul,nodalDivide_eval P S G ht,mul_div_cancel₀ _ (nz t ht),sub_self])
  have co := congrArg (fun p : K[X]=>p.coeff 4) v
  have mon : (nodalHull S).coeff 4=1 := by
    have c := (monic_nodalHull S).coeff_natDegree
    rwa [natDegree_nodalHull,sc] at c
  rw [coeff_sub,show (4:ℕ)=1+3 by decide,coeff_mul_add_eq_of_natDegree_le p1.le ud,
    show (1+3:ℕ)=4 by decide,coeff_C_mul,mon,mul_one,←nodalMeasure_top P S G sc] at co
  exact ⟨a,v,co.symm⟩

theorem nodalMeasure_transfer_four_linear {P G R : K[X]}
    (pd : P.natDegree=1) (gd : G.natDegree≤4)
    {S T : Finset K} (sc : S.card=4) (tc : T.card=4)
    (ns : ∀ x∈S,P.eval x≠0) (nt : ∀ x∈T,P.eval x≠0)
    (terminal : nodalHull T+P*R=nodalHull S) :
    nodalMeasure P S G=nodalMeasure P T G := by
  obtain ⟨a,ea,ca⟩ := measure_quotient_four_linear pd gd sc ns
  obtain ⟨b,eb,cb⟩ := measure_quotient_four_linear pd gd tc nt
  have col : nodalHull S*C (a-b)=P*(nodalDivide P S G-nodalDivide P T G-C b*R) := by
    rw [map_sub]
    linear_combination -ea+eb+C b*terminal
  have d : P∣C (a-b) :=
    (coprime_nodalHull_of_eval_ne ns).dvd_of_dvd_mul_left ⟨_,col⟩
  have aeb : a=b := by
    by_contra zz
    have h : (C (a-b):K[X])≠0 := by
      intro e
      exact zz (sub_eq_zero.mp (C_injective (by simpa only [map_zero] using e)))
    have d' := natDegree_le_of_dvd d h
    rw [pd,natDegree_C] at d'
    omega
  have pn : P≠0 := fun e=>by simp [e] at pd
  have p1 : P.coeff 1≠0 := by
    rw [←pd,coeff_natDegree]
    exact leadingCoeff_ne_zero.mpr pn
  apply mul_left_cancel₀ p1
  linear_combination -ca+cb+aeb

variable {A : Matrix (Fin 10) (Fin 10) K} {b : Fin 10→K}
variable {P R : K[X]} {dup k : Fin 10}

theorem actual_linear_terminal (M : Placement A b P dup k)
    {S : Finset K} (Sc : S.card=4) (pd : P.natDegree=1)
    (T : CleanTerminalProfile A (nodalHull S) R) :
    nodalHull S+P*R=nodalHull (offKnots A) := by
  obtain ⟨sig,e⟩ := paid_terminal_hull_raw M Sc T
  have d : (P*R).natDegree≤3 := natDegree_mul_le_of_le pd.le T.degR
  have cs : (nodalHull S).coeff 4=1 := by
    have z := (monic_nodalHull S).coeff_natDegree
    rwa [natDegree_nodalHull,Sc] at z
  have ct : (nodalHull (offKnots A)).coeff 4=1 := by
    have z := (monic_nodalHull (offKnots A)).coeff_natDegree
    rwa [natDegree_nodalHull,M.rankData.offCard] at z
  have coef := congrArg (fun P : K[X]=>P.coeff 4) e
  rw [coeff_add,cs,coeff_eq_zero_of_natDegree_lt (d.trans_lt (by decide)),coeff_C_mul,
    ct,add_zero,mul_one] at coef
  simpa [←coef] using e

theorem paid_newton_clean_transfer_linear
    (ha : ∀ i j, i≤j → A i j=0) (ho : HasOrder 8 A b) (M : Placement A b P dup k)
    {S : Finset K} (Sc : S.card=4) (n : ∀ x∈S,P.eval x≠0) (p1 : P.natDegree=1)
    (terminal : nodalHull S+P*R=nodalHull (offKnots A)) :
    ∃ δ tap gain : K,
      (k=5 → tap=0) ∧
      ∀ r : ℕ, 1≤r → r≤3 →
        let Cᵣ := nodalMeasure P S (X^r)
        let Cₛ := nodalMeasure P S (X^(r+1))
        let e := nodes A (fourthEarlyOff k)
        (δ*(Cₛ-e*Cᵣ)+tap*(nodes A k)^r=Cₛ/((r+1:ℕ):K)) ∧
          (k=4 → gain*(Cₛ-e*Cᵣ)=(nodes A k)^(r+1)/((r+1:ℕ):K)) := by
  obtain ⟨δ,tap,gain,t5,eq⟩ := paid_newton_physical ha ho M
  obtain ⟨insertEq,notin⟩ := early_off_insert M
  refine ⟨δ,tap,gain,t5,?_⟩
  intro r r1 r3
  have d1 : (X^r : K[X]).natDegree≤4 := (natDegree_X_pow_le _).trans (by omega)
  have d2 : (X^(r+1) : K[X]).natDegree≤4 := (natDegree_X_pow_le _).trans (by omega)
  have t1 := nodalMeasure_transfer_four_linear p1 d1 M.rankData.offCard Sc (eval_off_ne M) n terminal
  have t2 := nodalMeasure_transfer_four_linear p1 d2 M.rankData.offCard Sc (eval_off_ne M) n terminal
  have cut := nodalMeasure_erase_pow P notin r
  rw [←insertEq,t1,t2] at cut
  obtain ⟨p,c⟩ := eq r r1 r3
  rw [cut,t2] at p
  refine ⟨p,?_⟩
  intro k4
  rw [←cut]
  exact c k4

theorem linear_moments_geometric {S : Finset K} (Sc : S.card=4) (pd : P.natDegree=1)
    (n : ∀ x∈S,P.eval x≠0) (pzero : P.eval 0≠0) :
    ∃ lam : K, lam≠0 ∧ nodalMeasure P S 1≠0 ∧
      ∀ r : ℕ, r≤2 → nodalMeasure P S (X^(r+1))=lam*nodalMeasure P S (X^r) := by
  have pn : P≠0 := fun e=>by simp [e] at pd
  have p1 : P.coeff 1≠0 := by
    rw [←pd,coeff_natDegree]
    exact leadingCoeff_ne_zero.mpr pn
  have p2 : P.coeff 2=0 := coeff_eq_zero_of_natDegree_lt (by omega)
  have p0 : P.coeff 0≠0 := fun e=>pzero ((coeff_zero_eq_eval_zero P).symm.trans e)
  let lam' := -P.coeff 0/P.coeff 1
  have lamn : lam'≠0 := div_ne_zero (neg_ne_zero.mpr p0) p1
  have rel : P.coeff 1*lam'= -P.coeff 0 := mul_div_cancel₀ _ p1
  have root : P.eval lam'=0 := by
    rw [LobattoEight.quadratic_coeff_expand P (by omega)]
    simp only [eval_add,eval_monomial,pow_zero,pow_one,mul_one,p2,zero_mul,add_zero]
    linear_combination rel
  have nmember : lam'∉S := fun h=>n _ h root
  have c := nodalHull_eval_ne_of_notMem nmember
  obtain ⟨v,e,co⟩ := measure_quotient_four_linear (G:=1) pd (by simp) Sc n
  have u := congrArg (fun Q : K[X]=>Q.eval lam') e
  simp only [eval_sub,eval_mul,eval_C,root,zero_mul,eval_one,zero_sub] at u
  refine ⟨lam',lamn,?_,?_⟩
  · intro en
    have h0 : (1:K[X]).coeff 4=0 := coeff_eq_zero_of_natDegree_lt (by rw [natDegree_one]; decide)
    rw [en,mul_zero,h0,sub_self] at co
    rw [co,zero_mul] at u
    exact (neg_ne_zero.mpr one_ne_zero) u
  · intro r r2
    have h := nodalMeasure_quadratic_recurrence (P:=P) (S:=S) (by omega) Sc n r r2
    rw [p2,zero_mul,add_zero] at h
    apply mul_left_cancel₀ p1
    linear_combination h-nodalMeasure P S (X^r)*rel

end RKResearch.Certified.Graded.FourOffNewton

#print axioms RKResearch.Certified.Graded.FourOffNewton.nodalMeasure_transfer_four_linear
#print axioms RKResearch.Certified.Graded.FourOffNewton.linear_moments_geometric
