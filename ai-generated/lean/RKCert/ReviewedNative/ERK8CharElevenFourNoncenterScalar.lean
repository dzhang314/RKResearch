module

public import RKCert.ReviewedNative.ERK8FourOffNodalTransfer
public import RKCert.ReviewedNative.ERK8CharElevenFourHead

import Mathlib.Tactic.LinearCombination
import Mathlib.Tactic.NormNum
import Mathlib.Tactic.Ring

@[expose] public section

/-! # The two noncenter scalar charts in characteristic eleven
The receipts below use exact reduction by h²-h+8 and 11, not a
finite tableau search or an assumption that the field has 121 elements. -/
namespace RKResearch.Certified.Graded.FourOffNewton

open RKResearch Polynomial OneOff ERKTaggedHorizon ERK8CharEleven ERK8PaidField RKCert.Endpoint
open RKResearch.Certified.Graded.MultiOff.FourOff8CleanShape
open RKResearch.Certified.Graded.MultiOff.FourOff8Scalar
open scoped Classical Matrix BigOperators

variable {K : Type*} [Field K]

noncomputable def cleanSites (h x z : K) : Finset K := {0,h,x,z}

theorem lobatto_clock_ne_zero {t : K} (h : lobattoNumer t=0) : t≠0 := by
  intro tz
  rw [tz] at h
  simp [lobattoNumer] at h

theorem cleanSites_card {h x z : K} (D : CleanClocks h x z) : (cleanSites h x z).card=4 := by
  simp [cleanSites,Finset.card_insert_of_notMem,D.h_ne_x,D.h_ne_z,D.x_ne_z,
    (lobatto_clock_ne_zero D.root_h).symm,(lobatto_clock_ne_zero D.root_x).symm,
    (lobatto_clock_ne_zero D.root_z).symm]

theorem cleanSites_hull {h x z : K} (D : CleanClocks h x z) :
    nodalHull (cleanSites h x z)=quartic h x z := by
  simp only [cleanSites,nodalHull,Finset.prod_insert (by
    simp [ne_comm, lobatto_clock_ne_zero D.root_h,lobatto_clock_ne_zero D.root_x,
      lobatto_clock_ne_zero D.root_z] : (0:K)∉({h,x,z}:Finset K)),
    Finset.prod_insert (by simp [D.h_ne_x,D.h_ne_z] : h∉({x,z}:Finset K)),Finset.prod_pair D.x_ne_z,
    quartic,tapFactor,cleanPair,map_zero,sub_zero]
  ring

theorem four_clean_cofactors {h x z : K} (D : CleanClocks h x z) :
    nodalCofactor (cleanSites h x z) 0=(0-h)*(0-x)*(0-z) ∧
    nodalCofactor (cleanSites h x z) h=h*(h-x)*(h-z) ∧
    nodalCofactor (cleanSites h x z) x=x*(x-h)*(x-z) ∧
    nodalCofactor (cleanSites h x z) z=z*(z-h)*(z-x) := by
  have hn := lobatto_clock_ne_zero D.root_h
  have xn := lobatto_clock_ne_zero D.root_x
  have zn := lobatto_clock_ne_zero D.root_z
  have A : (cleanSites h x z).erase 0={h,x,z} := by
    unfold cleanSites
    rw [Finset.erase_insert (by simp [hn.symm,xn.symm,zn.symm])]
  have B : (cleanSites h x z).erase h={0,x,z} := by
    unfold cleanSites
    rw [Finset.erase_insert_of_ne hn.symm,
      Finset.erase_insert (by simp [D.h_ne_x,D.h_ne_z])]
  have C₃ : (cleanSites h x z).erase x={0,h,z} := by
    unfold cleanSites
    rw [Finset.erase_insert_of_ne xn.symm,Finset.erase_insert_of_ne D.h_ne_x,
      Finset.erase_insert (by simp [D.x_ne_z])]
  have D₃ : (cleanSites h x z).erase z={0,h,x} := by
    unfold cleanSites
    rw [Finset.erase_insert_of_ne zn.symm,Finset.erase_insert_of_ne D.h_ne_z,
      Finset.erase_insert_of_ne D.x_ne_z,Finset.erase_singleton,Finset.insert_empty]
  refine ⟨?_, ?_, ?_, ?_⟩
  · rw [nodalCofactor,A,nodalHull,Finset.prod_insert (by simp [D.h_ne_x,D.h_ne_z]),Finset.prod_pair D.x_ne_z]
    simp only [eval_mul,eval_sub,eval_X,eval_C,mul_assoc]
  · rw [nodalCofactor,B,nodalHull,Finset.prod_insert (by simp [xn.symm,zn.symm]),Finset.prod_pair D.x_ne_z]
    simp only [eval_mul,eval_sub,eval_X,eval_C,sub_zero,mul_assoc]
  · rw [nodalCofactor,C₃,nodalHull,Finset.prod_insert (by simp [hn.symm,zn.symm]),Finset.prod_pair D.h_ne_z]
    simp only [eval_mul,eval_sub,eval_X,eval_C,sub_zero,mul_assoc]
  · rw [nodalCofactor,D₃,nodalHull,Finset.prod_insert (by simp [hn.symm,xn.symm]),Finset.prod_pair D.h_ne_x]
    simp only [eval_mul,eval_sub,eval_X,eval_C,sub_zero,mul_assoc]

theorem nodalMeasure_four (P G : K[X]) {h x z : K} (D : CleanClocks h x z) :
    nodalMeasure P (cleanSites h x z) G=
      G.eval 0/P.eval 0/nodalCofactor (cleanSites h x z) 0+
      G.eval h/P.eval h/nodalCofactor (cleanSites h x z) h+
      G.eval x/P.eval x/nodalCofactor (cleanSites h x z) x+
      G.eval z/P.eval z/nodalCofactor (cleanSites h x z) z := by
  let S := cleanSites h x z
  change (∑ t∈({0,h,x,z}:Finset K),G.eval t/P.eval t/nodalCofactor S t)=_
  rw [Finset.sum_insert (by simp [←ne_comm (b:=(0:K)),lobatto_clock_ne_zero D.root_h,
        lobatto_clock_ne_zero D.root_x,lobatto_clock_ne_zero D.root_z] : (0:K)∉({h,x,z}:Finset K)),
    Finset.sum_insert (by simp [D.h_ne_x,D.h_ne_z] : h∉({x,z}:Finset K)),Finset.sum_pair D.x_ne_z]
  ring

private theorem scaled_clean_term {kap a b inv v : K} (kn : kap≠0) (invId : a*b*inv=1) :
    kap*(v/(kap*a)/b)=v*inv := by
  have an : a≠0 := fun z=>(one_ne_zero : (1:K)≠0) (by simpa [z] using invId.symm)
  have bn : b≠0 := fun z=>(one_ne_zero : (1:K)≠0) (by simpa [z] using invId.symm)
  rw [div_div,mul_assoc kap a b,←mul_div_assoc,mul_div_mul_left _ _ kn]
  exact (div_eq_iff (mul_ne_zero an bn)).mpr (by linear_combination -v*invId)

structure QuadraticHeadReceipt (P : K[X]) (h x z : K) : Prop where
  degree : P.natDegree=2
  nonzero : ∀ u∈cleanSites h x z,P.eval u≠0
  atFour : let M := fun r : ℕ=>nodalMeasure P (cleanSites h x z) (X^r)
    M 4-2*h*M 3+h^2*M 2≠0
  atFiveA : let M := fun r : ℕ=>nodalMeasure P (cleanSites h x z) (X^r)
    M 1*M 3-(M 2)^2≠0
  atFiveB : let M := fun r : ℕ=>nodalMeasure P (cleanSites h x z) (X^r)
    P.coeff 2*M 4-2*P.coeff 0*M 2≠0

private theorem center_second {P : K[X]} {h theta kap : K}
    (p : (11:K)=0) (qh : h^2-h+8=0) (hd : P.natDegree≤2) (pn : P≠0)
    (D : CleanClocks h (6) (1 - h))
    (s : RawPaidShape P h (6) (1 - h) theta kap) :
    QuadraticHeadReceipt P h (6) (1 - h) := by
  have Eunit : cleanE h (6) (1 - h) * (9*h : K)=1 := by
    unfold cleanE
    linear_combination (63*h - 513)*qh + (373 - 63*h)*p
  have Tprod : ((9*h + 6 : K))*cleanE h (6) (1 - h)=cleanNumer h (6) := by
    unfold cleanE cleanNumer
    linear_combination (63*h - 468)*qh + (360 - 96*h)*p
  have en : cleanE h (6) (1 - h) ≠ 0 :=
    fun z=>(one_ne_zero : (1:K)≠0) (by simpa [z] using Eunit.symm)
  have thetaEq : theta=kap*(9*h + 6 : K) := by
    apply mul_right_cancel₀ en
    linear_combination s.ratio-kap*Tprod
  have kn : kap≠0 := by
    intro kn
    exact pn (by rw [s.identity,thetaEq,kn]; simp)
  have we (u : K) : P.eval u=kap*((9*h + 6 : K)*((u-(6))*(u-(1 - h))))+
      kap*(5*u^2-(4*(6)+3*h)*u+2*h*(6)) := by
    rw [s.identity,thetaEq]
    simp only [cleanPair,eval_add,eval_sub,eval_mul,eval_C,eval_X,eval_pow]
    ring
  have coef₂ : P.coeff 2=kap*(9*h : K) := by
    have cc : (cleanPair (6) (1 - h)).coeff 2=1 := by
      have lin (u : K) : ((X:K[X])-C u).coeff 1=1 := by
        rw [coeff_sub,coeff_X_one,coeff_C]
        simp
      unfold cleanPair
      rw [show (2:ℕ)=1+1 by decide,
        coeff_mul_add_eq_of_natDegree_le (natDegree_X_sub_C_le _) (natDegree_X_sub_C_le _),
        lin,lin,one_mul]
    rw [s.identity,thetaEq]
    simp only [coeff_add,coeff_sub,coeff_C_mul,cc,coeff_X_pow,coeff_X,coeff_C,
      show (1:ℕ)≠2 by decide,show (2:ℕ)≠0 by decide,ite_false,ite_true,
      mul_zero,mul_one,sub_zero,add_zero]
    linear_combination kap*p
  have co2Unit : (9*h : K)*(9*h + 2 : K)=1 := by
    linear_combination (81)*qh + (9*h - 59)*p
  have c2n : P.coeff 2≠0 := by
    rw [coef₂]
    exact mul_ne_zero kn (fun e=>(one_ne_zero : (1:K)≠0) (by simpa [e] using co2Unit.symm))
  have deg : P.natDegree=2 := natDegree_eq_of_le_of_coeff_ne_zero hd c2n
  obtain ⟨cf₀,cf₁,cf₂,cf₃⟩ := four_clean_cofactors D
  have pe0 : P.eval (0)=kap*(9*h + 6 : K) := by
    rw [we]
    linear_combination kap*((-54)*qh + (42 - 3*h)*p)
  have I0 : (9*h + 6 : K)*(6*h^2 - 6*h : K)*(5*h + 10 : K)=1 := by
    linear_combination (270*h^2 + 720*h - 1800)*qh + (1309 - 720*h)*p
  have pn0 : P.eval (0)≠0 := by
    rw [pe0]
    exact mul_ne_zero kn (fun e=>(one_ne_zero : (1:K)≠0) (by simpa [e] using I0.symm))
  have val0 (w : K) : kap*(w/P.eval (0)/nodalCofactor (cleanSites h (6) (1 - h)) (0))=w*(5*h + 10 : K) := by
    rw [pe0,cf₀]
    apply scaled_clean_term kn
    linear_combination I0
  have pe1 : P.eval (h)=kap*(10*h + 1 : K) := by
    rw [we]
    linear_combination kap*((18*h - 85)*qh + (65 - 25*h)*p)
  have I1 : (10*h + 1 : K)*(2*h^3 - 13*h^2 + 6*h : K)*(7 : K)=1 := by
    linear_combination (140*h^2 - 756*h - 1547)*qh + (413*h + 1125)*p
  have pn1 : P.eval (h)≠0 := by
    rw [pe1]
    exact mul_ne_zero kn (fun e=>(one_ne_zero : (1:K)≠0) (by simpa [e] using I1.symm))
  have val1 (w : K) : kap*(w/P.eval (h)/nodalCofactor (cleanSites h (6) (1 - h)) (h))=w*(7 : K) := by
    rw [pe1,cf₁]
    apply scaled_clean_term kn
    linear_combination I1
  have pe2 : P.eval (6)=kap*(5*h + 3 : K) := by
    rw [we]
    linear_combination kap*((3 - h)*p)
  have I2 : (5*h + 3 : K)*(-6*h^2 + 6*h + 180 : K)*(5*h + 3 : K)=1 := by
    linear_combination (-150*h^2 - 180*h + 5646)*qh + (1140*h - 3959)*p
  have pn2 : P.eval (6)≠0 := by
    rw [pe2]
    exact mul_ne_zero kn (fun e=>(one_ne_zero : (1:K)≠0) (by simpa [e] using I2.symm))
  have val2 (w : K) : kap*(w/P.eval (6)/nodalCofactor (cleanSites h (6) (1 - h)) (6))=w*(5*h + 3 : K) := by
    rw [pe2,cf₂]
    apply scaled_clean_term kn
    linear_combination I2
  have pe3 : P.eval (1 - h)=kap*(9*h + 5 : K) := by
    rw [we]
    linear_combination kap*((8)*qh + (2*h - 8)*p)
  have I3 : (9*h + 5 : K)*(-2*h^3 - 7*h^2 + 14*h - 5 : K)*(8*h + 3 : K)=1 := by
    linear_combination (-144*h^3 - 782*h^2 + 879*h + 7608)*qh + (41*h - 5540)*p
  have pn3 : P.eval (1 - h)≠0 := by
    rw [pe3]
    exact mul_ne_zero kn (fun e=>(one_ne_zero : (1:K)≠0) (by simpa [e] using I3.symm))
  have val3 (w : K) : kap*(w/P.eval (1 - h)/nodalCofactor (cleanSites h (6) (1 - h)) (1 - h))=w*(8*h + 3 : K) := by
    rw [pe3,cf₃]
    apply scaled_clean_term kn
    linear_combination I3
  let S := cleanSites h (6) (1 - h)
  have paid (r : ℕ) : kap*nodalMeasure P S (X^r)=
      0^r*(5*h + 10 : K)+h^r*(7 : K)+(6)^r*(5*h + 3 : K)+(1 - h)^r*(8*h + 3 : K) := by
    rw [show S=cleanSites h (6) (1 - h) from rfl,nodalMeasure_four P _ D]
    simp only [eval_pow,eval_X,mul_add,val0,val1,val2,val3]
  have g1 : kap*nodalMeasure P S (X^1)=(h + 8 : K) := by
    rw [paid]
    linear_combination (-8)*qh + (3*h + 7)*p
  have g2 : kap*nodalMeasure P S (X^2)=(10*h + 7 : K) := by
    rw [paid]
    linear_combination (8*h + 2)*qh + (10*h + 8)*p
  have g3 : kap*nodalMeasure P S (X^3)=(9*h : K) := by
    rw [paid]
    linear_combination (-8*h^2 + 20*h + 69)*qh + (89*h + 9)*p
  have g4 : kap*nodalMeasure P S (X^4)=(4*h : K) := by
    rw [paid]
    linear_combination (8*h^3 - 14*h^2 - 42*h + 56)*qh + (624*h + 313)*p
  have f4 : (10*h^3 - 11*h^2 + 4*h : K)*(7 : K)=1 := by
    linear_combination (70*h - 7)*qh + (5 - 49*h)*p
  have f5a : (-91*h^2 - 68*h - 49 : K)*(4*h + 9 : K)=1 := by
    linear_combination (-364*h - 1455)*qh + (59*h + 1018)*p
  have f5b : (-144*h^2 - 246*h - 84 : K)*(3*h + 2 : K)=1 := by
    linear_combination (-432*h - 1458)*qh + (114*h + 1045)*p
  let C₁ := nodalMeasure P S (X^1)
  let C₂ := nodalMeasure P S (X^2)
  let C₃ := nodalMeasure P S (X^3)
  let C₄ := nodalMeasure P S (X^4)
  change kap*C₁=_ at g1
  change kap*C₂=_ at g2
  change kap*C₃=_ at g3
  change kap*C₄=_ at g4
  refine ⟨deg,?_,?_,?_,?_⟩
  · intro t ht
    simp only [cleanSites,Finset.mem_insert,Finset.mem_singleton] at ht
    rcases ht with rfl|rfl|rfl|rfl
    · exact pn0
    · exact pn1
    · exact pn2
    · exact pn3
  · dsimp only
    intro eq₀
    change C₄-2*h*C₃+h^2*C₂=0 at eq₀
    exact (one_ne_zero : (1:K)≠0) (by linear_combination (7 : K)*(kap*eq₀-g4+2*h*g3-h^2*g2)-f4 : (1:K)=0)
  · dsimp only
    intro eq₀
    change C₁*C₃-C₂^2=0 at eq₀
    have a : (-91*h^2 - 68*h - 49 : K)=0 := by
      linear_combination kap^2*eq₀-kap*C₃*g1-(h + 8 : K)*g3+(kap*C₂+(10*h + 7 : K))*g2
    exact (one_ne_zero : (1:K)≠0) (by linear_combination (4*h + 9 : K)*a-f5a : (1:K)=0)
  · dsimp only
    intro eq₀
    change P.coeff 2*C₄-2*P.coeff 0*C₂=0 at eq₀
    rw [coef₂,coeff_zero_eq_eval_zero,pe0] at eq₀
    have a : (-144*h^2 - 246*h - 84 : K)=0 := by linear_combination eq₀-(9*h : K)*g4+2*(9*h + 6 : K)*g2
    exact (one_ne_zero : (1:K)≠0) (by linear_combination (3*h + 2 : K)*a-f5b : (1:K)=0)

private theorem center_third {P : K[X]} {h theta kap : K}
    (p : (11:K)=0) (qh : h^2-h+8=0) (hd : P.natDegree≤2) (pn : P≠0)
    (D : CleanClocks h (1 - h) (6))
    (s : RawPaidShape P h (1 - h) (6) theta kap) :
    QuadraticHeadReceipt P h (1 - h) (6) := by
  have Eunit : cleanE h (1 - h) (6) * (9*h : K)=1 := by
    unfold cleanE
    linear_combination (63*h - 513)*qh + (373 - 63*h)*p
  have Tprod : ((4*h + 7 : K))*cleanE h (1 - h) (6)=cleanNumer h (1 - h) := by
    unfold cleanE cleanNumer
    linear_combination (28*h - 172)*qh + (148 - 64*h)*p
  have en : cleanE h (1 - h) (6) ≠ 0 :=
    fun z=>(one_ne_zero : (1:K)≠0) (by simpa [z] using Eunit.symm)
  have thetaEq : theta=kap*(4*h + 7 : K) := by
    apply mul_right_cancel₀ en
    linear_combination s.ratio-kap*Tprod
  have kn : kap≠0 := by
    intro kn
    exact pn (by rw [s.identity,thetaEq,kn]; simp)
  have we (u : K) : P.eval u=kap*((4*h + 7 : K)*((u-(1 - h))*(u-(6))))+
      kap*(5*u^2-(4*(1 - h)+3*h)*u+2*h*(1 - h)) := by
    rw [s.identity,thetaEq]
    simp only [cleanPair,eval_add,eval_sub,eval_mul,eval_C,eval_X,eval_pow]
    ring
  have coef₂ : P.coeff 2=kap*(4*h + 1 : K) := by
    have cc : (cleanPair (1 - h) (6)).coeff 2=1 := by
      have lin (u : K) : ((X:K[X])-C u).coeff 1=1 := by
        rw [coeff_sub,coeff_X_one,coeff_C]
        simp
      unfold cleanPair
      rw [show (2:ℕ)=1+1 by decide,
        coeff_mul_add_eq_of_natDegree_le (natDegree_X_sub_C_le _) (natDegree_X_sub_C_le _),
        lin,lin,one_mul]
    rw [s.identity,thetaEq]
    simp only [coeff_add,coeff_sub,coeff_C_mul,cc,coeff_X_pow,coeff_X,coeff_C,
      show (1:ℕ)≠2 by decide,show (2:ℕ)≠0 by decide,ite_false,ite_true,
      mul_zero,mul_one,sub_zero,add_zero]
    linear_combination kap*p
  have co2Unit : (4*h + 1 : K)*(7*h + 5 : K)=1 := by
    linear_combination (28)*qh + (5*h - 20)*p
  have c2n : P.coeff 2≠0 := by
    rw [coef₂]
    exact mul_ne_zero kn (fun e=>(one_ne_zero : (1:K)≠0) (by simpa [e] using co2Unit.symm))
  have deg : P.natDegree=2 := natDegree_eq_of_le_of_coeff_ne_zero hd c2n
  obtain ⟨cf₀,cf₁,cf₂,cf₃⟩ := four_clean_cofactors D
  have pe0 : P.eval (0)=kap*(2*h + 8 : K) := by
    rw [we]
    linear_combination kap*((-26)*qh + (22 - 4*h)*p)
  have I0 : (2*h + 8 : K)*(6*h^2 - 6*h : K)*(3*h + 7 : K)=1 := by
    linear_combination (36*h^2 + 228*h + 48)*qh + (-192*h - 35)*p
  have pn0 : P.eval (0)≠0 := by
    rw [pe0]
    exact mul_ne_zero kn (fun e=>(one_ne_zero : (1:K)≠0) (by simpa [e] using I0.symm))
  have val0 (w : K) : kap*(w/P.eval (0)/nodalCofactor (cleanSites h (1 - h) (6)) (0))=w*(3*h + 7 : K) := by
    rw [pe0,cf₀]
    apply scaled_clean_term kn
    linear_combination I0
  have pe1 : P.eval (h)=kap*(6*h + 8 : K) := by
    rw [we]
    linear_combination kap*((8*h - 26)*qh + (22 - 15*h)*p)
  have I1 : (6*h + 8 : K)*(2*h^3 - 13*h^2 + 6*h : K)*(3*h + 1 : K)=1 := by
    linear_combination (36*h^3 - 138*h^2 - 692*h + 488)*qh + (552*h - 355)*p
  have pn1 : P.eval (h)≠0 := by
    rw [pe1]
    exact mul_ne_zero kn (fun e=>(one_ne_zero : (1:K)≠0) (by simpa [e] using I1.symm))
  have val1 (w : K) : kap*(w/P.eval (h)/nodalCofactor (cleanSites h (1 - h) (6)) (h))=w*(3*h + 1 : K) := by
    rw [pe1,cf₁]
    apply scaled_clean_term kn
    linear_combination I1
  have pe2 : P.eval (1 - h)=kap*(10*h + 7 : K) := by
    rw [we]
    linear_combination kap*((2)*qh + (-h - 2)*p)
  have I2 : (10*h + 7 : K)*(-2*h^3 - 7*h^2 + 14*h - 5 : K)*(10*h + 9 : K)=1 := by
    linear_combination (-200*h^3 - 1220*h^2 + 534*h + 11593)*qh + (673*h - 8460)*p
  have pn2 : P.eval (1 - h)≠0 := by
    rw [pe2]
    exact mul_ne_zero kn (fun e=>(one_ne_zero : (1:K)≠0) (by simpa [e] using I2.symm))
  have val2 (w : K) : kap*(w/P.eval (1 - h)/nodalCofactor (cleanSites h (1 - h) (6)) (1 - h))=w*(10*h + 9 : K) := by
    rw [pe2,cf₂]
    apply scaled_clean_term kn
    linear_combination I2
  have pe3 : P.eval (6)=kap*(6*h + 7 : K) := by
    rw [we]
    linear_combination kap*((-2)*qh + (15)*p)
  have I3 : (6*h + 7 : K)*(-6*h^2 + 6*h + 180 : K)*(7*h + 5 : K)=1 := by
    linear_combination (-252*h^2 - 474*h + 9366)*qh + (2508*h - 6239)*p
  have pn3 : P.eval (6)≠0 := by
    rw [pe3]
    exact mul_ne_zero kn (fun e=>(one_ne_zero : (1:K)≠0) (by simpa [e] using I3.symm))
  have val3 (w : K) : kap*(w/P.eval (6)/nodalCofactor (cleanSites h (1 - h) (6)) (6))=w*(7*h + 5 : K) := by
    rw [pe3,cf₃]
    apply scaled_clean_term kn
    linear_combination I3
  let S := cleanSites h (1 - h) (6)
  have paid (r : ℕ) : kap*nodalMeasure P S (X^r)=
      0^r*(3*h + 7 : K)+h^r*(3*h + 1 : K)+(1 - h)^r*(10*h + 9 : K)+(6)^r*(7*h + 5 : K) := by
    rw [show S=cleanSites h (1 - h) (6) from rfl,nodalMeasure_four P _ D]
    simp only [eval_pow,eval_X,mul_add,val0,val1,val2,val3]
  have g1 : kap*nodalMeasure P S (X^1)=(4*h + 7 : K) := by
    rw [paid]
    linear_combination (-7)*qh + (3*h + 8)*p
  have g2 : kap*nodalMeasure P S (X^2)=(0 : K) := by
    rw [paid]
    linear_combination (13*h + 3)*qh + (13*h + 15)*p
  have g3 : kap*nodalMeasure P S (X^3)=(2*h + 6 : K) := by
    rw [paid]
    linear_combination (-7*h^2 + 15*h + 68)*qh + (131*h + 49)*p
  have g4 : kap*nodalMeasure P S (X^4)=(8*h + 4 : K) := by
    rw [paid]
    linear_combination (13*h^3 - 17*h^2 - 97*h + 53)*qh + (897*h + 551)*p
  have f4 : (-4*h^2 - 4*h + 4 : K)*(4*h + 3 : K)=1 := by
    linear_combination (-16*h - 44)*qh + (8*h + 33)*p
  have f5a : (8*h^2 + 38*h + 42 : K)*(2*h + 9 : K)=1 := by
    linear_combination (16*h + 164)*qh + (42*h - 85)*p
  have f5b : (32*h^2 + 24*h + 4 : K)*(h + 9 : K)=1 := by
    linear_combination (32*h + 344)*qh + (28*h - 247)*p
  let C₁ := nodalMeasure P S (X^1)
  let C₂ := nodalMeasure P S (X^2)
  let C₃ := nodalMeasure P S (X^3)
  let C₄ := nodalMeasure P S (X^4)
  change kap*C₁=_ at g1
  change kap*C₂=_ at g2
  change kap*C₃=_ at g3
  change kap*C₄=_ at g4
  refine ⟨deg,?_,?_,?_,?_⟩
  · intro t ht
    simp only [cleanSites,Finset.mem_insert,Finset.mem_singleton] at ht
    rcases ht with rfl|rfl|rfl|rfl
    · exact pn0
    · exact pn1
    · exact pn2
    · exact pn3
  · dsimp only
    intro eq₀
    change C₄-2*h*C₃+h^2*C₂=0 at eq₀
    exact (one_ne_zero : (1:K)≠0) (by linear_combination (4*h + 3 : K)*(kap*eq₀-g4+2*h*g3-h^2*g2)-f4 : (1:K)=0)
  · dsimp only
    intro eq₀
    change C₁*C₃-C₂^2=0 at eq₀
    have a : (8*h^2 + 38*h + 42 : K)=0 := by
      linear_combination kap^2*eq₀-kap*C₃*g1-(4*h + 7 : K)*g3+(kap*C₂+(0 : K))*g2
    exact (one_ne_zero : (1:K)≠0) (by linear_combination (2*h + 9 : K)*a-f5a : (1:K)=0)
  · dsimp only
    intro eq₀
    change P.coeff 2*C₄-2*P.coeff 0*C₂=0 at eq₀
    rw [coef₂,coeff_zero_eq_eval_zero,pe0] at eq₀
    have a : (32*h^2 + 24*h + 4 : K)=0 := by linear_combination eq₀-(4*h + 1 : K)*g4+2*(2*h + 8 : K)*g2
    exact (one_ne_zero : (1:K)≠0) (by linear_combination (h + 9 : K)*a-f5b : (1:K)=0)

theorem noncenter_char11_receipt {P : K[X]} {h x z theta kap : K}
    (p : (11:K)=0) (qh : (exceptionalQuadratic : K[X]).eval h=0)
    (hd : P.natDegree≤2) (pn : P≠0) (D : CleanClocks h x z)
    (s : RawPaidShape P h x z theta kap) : QuadraticHeadReceipt P h x z := by
  rw [exceptionalQuadratic_eval] at qh
  have comp {a : K} (ha : (exceptionalQuadratic : K[X]).eval a=0) (hn : h≠a) : a=1-h := by
    rw [exceptionalQuadratic_eval] at ha
    have eq : (h-a)*(h+a-1)=0 := by linear_combination qh-ha
    have sum := (mul_eq_zero.mp eq).resolve_left (sub_ne_zero.mpr hn)
    linear_combination sum
  rcases clean_center_or_quadratic p D.root_x with xh|xq
  · have zq := (clean_center_or_quadratic p D.root_z).resolve_left (fun e=>D.x_ne_z (xh.trans e.symm))
    have z1 := comp zq D.h_ne_z
    rw [xh,z1] at D s ⊢
    exact center_second p qh hd pn D s
  · have x1 := comp xq D.h_ne_x
    have z6 := (clean_center_or_quadratic p D.root_z).resolve_right (fun qz =>
      D.x_ne_z (x1.trans (comp qz D.h_ne_z).symm))
    rw [x1,z6] at D s ⊢
    exact center_third p qh hd pn D s

end RKResearch.Certified.Graded.FourOffNewton

#print axioms RKResearch.Certified.Graded.FourOffNewton.noncenter_char11_receipt
