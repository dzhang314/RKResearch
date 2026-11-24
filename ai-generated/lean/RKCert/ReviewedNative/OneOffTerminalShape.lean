module

public import RKCert.ReviewedNative.OneOffMaximal
public import RKCert.ReviewedNative.OneOffPencilArithmetic

@[expose] public section

/-! # Endpoint polynomial from native paid moments and its two-dimensional beta pencil -/
namespace RKResearch.Certified.Graded.OneOff
open RKResearch Polynomial Module RKCert.GoodPrimeDense
open RKCert.Paired.OneOff (endpointF readGrid endpointFData)
open scoped Classical Matrix

variable {K : Type*} [Field K] [CharZero K]

set_option maxHeartbeats 550000 in
/-- Homogeneous version of the native monic pencil decoder. -/
theorem beta_pair_decoder (Q : K[X]) (hd : Q.natDegree≤4)
    (mom : ∀ k : Fin 3,
      (∑ j : Fin 5, Q.coeff j.val/((k.val+j.val+3:ℕ):K))-
      (∑ j : Fin 5, Q.coeff j.val/((k.val+j.val+2:ℕ):K))=0) :
    Q=C (Q.coeff 4)*lobattoPencil 0+C (Q.coeff 3+2*Q.coeff 4)*lobattoCubic := by
  have m0 := mom 0
  have m1 := mom 1
  have m2 := mom 2
  norm_num [Fin.sum_univ_succ] at m0 m1 m2
  have h0 : Q.coeff 0=Q.coeff 4/42-(Q.coeff 3+2*Q.coeff 4)/14 := by
    linear_combination -120*m0+480*m1-420*m2
  have h1 : Q.coeff 1= -Q.coeff 4/3+9*(Q.coeff 3+2*Q.coeff 4)/14 := by
    linear_combination 480*m0-2220*m1+2100*m2
  have h2 : Q.coeff 2=4*Q.coeff 4/3-3*(Q.coeff 3+2*Q.coeff 4)/2 := by
    linear_combination -420*m0+2100*m1-2100*m2
  ext n
  by_cases hn : n≤4
  · simp only [coeff_add,coeff_C_mul,lobattoPencil,lobattoCubic,coeff_monomial_apply]
    interval_cases n <;> norm_num [h0,h1,h2] <;> ring
  · have h0 : 0≠n := by omega
    have h1 : 1≠n := by omega
    have h2 : 2≠n := by omega
    have h3 : 3≠n := by omega
    have h4 : 4≠n := by omega
    rw [coeff_eq_zero_of_natDegree_lt (by omega : Q.natDegree<n)]
    simp only [coeff_add,coeff_C_mul,lobattoPencil,lobattoCubic,coeff_monomial_apply,
      ite_eq_right h0,ite_eq_right h1,ite_eq_right h2,ite_eq_right h3,ite_eq_right h4,mul_zero,add_zero]

theorem beta_pair_no_common_root (x : K) :
    (lobattoCubic : K[X]).eval x≠0 ∨ (lobattoPencil 0 : K[X]).eval x≠0 := by
  by_contra! e
  let u := x*(1-x)
  have j : (2*x-1)*(1-7*u)=0 := by
    have h := e.1
    simp only [lobattoCubic,eval_add,eval_monomial] at h
    dsimp only [u]
    linear_combination 14*h
  have k : 42*u^2-14*u+1=0 := by
    have h := e.2
    simp only [lobattoPencil,eval_add,eval_monomial] at h
    norm_num at h
    dsimp only [u]
    linear_combination 42*h
  rcases mul_eq_zero.mp j with j|j
  · have xx : x=1/2 := by linear_combination (1/2:K)*j
    rw [show u=1/4 by dsimp only [u]; rw [xx]; norm_num] at k
    norm_num at k
  · have uu : u=1/7 := by linear_combination -(1/7:K)*j
    rw [uu] at k
    norm_num at k

/-- No root isolation: the normalization follows from the two-dimensional
kernel at the doubled clock. -/
theorem terminal_beta_formula {d α β : K} {B : K[X]}
    (Beq : B=C α*lobattoPencil 0+C β*lobattoCubic)
    (t1 : 2*d≠1) (Bt : B.eval (2*d)=0) (B1 : B.eval 1=1) :
    endpointF d 1≠0 ∧ ∀ x,
      B.eval x=(x-2*d)*endpointF d x/((1-2*d)*endpointF d 1) := by
  let u := (lobattoCubic : K[X]).eval (2*d)
  let v := (lobattoPencil 0 : K[X]).eval (2*d)
  have rel : α*v+β*u=0 := by simpa only [Beq,eval_add,eval_mul,eval_C] using Bt
  have rep : ∃ k : K, α=k*u ∧ β= -k*v := by
    rcases beta_pair_no_common_root (2*d) with un|vn
    · refine ⟨α/u,?_ ,?_⟩
      · exact (div_mul_cancel₀ _ un).symm
      · calc β = -(α*v)/u := (eq_div_iff un).mpr (by linear_combination rel)
             _ = -(α/u)*v := by field_simp [un]
    · refine ⟨-β/v,?_,?_⟩
      · calc α = (-β*u)/v := (eq_div_iff vn).mpr (by linear_combination rel)
             _ = (-β/v)*u := by field_simp [vn]
      · rw [neg_mul,div_mul_cancel₀ _ vn,neg_neg]
  obtain ⟨k,ak,bk⟩ := rep
  have h (x : K) : B.eval x=k*((x-2*d)*endpointF d x)/588 := by
    rw [Beq,eval_add,eval_mul,eval_mul,eval_C,eval_C,ak,bk,endpointF_jacobi]
    dsimp only [u,v]
    ring
  have all : k*((1-2*d)*endpointF d 1)=588 := by
    have e := (h 1).symm.trans B1
    linear_combination 588*e
  have fn : endpointF d 1≠0 := by
    intro z
    simp [z] at all
  refine ⟨fn,fun x=>?_⟩
  rw [h]
  have den := mul_ne_zero (sub_ne_zero.mpr (Ne.symm t1)) fn
  apply (div_eq_div_iff (by norm_num : (588:K)≠0) den).mpr
  linear_combination ((x-2*d)*endpointF d x)*all

omit [CharZero K] in
theorem endpointF_at_one (d : K) : endpointF d 1=2*(168*d^3-112*d^2+21*d-1) := by
  simp [endpointF,readGrid,endpointFData,RKCert.GoodPrimeDense.read]
  ring

omit [CharZero K] in
/-- Convert the genuine `X(X-1)` probe into the two shifted sums, with
the exact tree-order budget visible in the statement. -/
theorem beta_probe_coeff {s p : ℕ} {A : Matrix (Fin s) (Fin s) K} {b : Fin s → K}
    (ho : HasOrder A b p) (Q : K[X]) {n k : ℕ}
    (hd : Q.natDegree ≤ n) (hpay : k+n+3 ≤ p)
    (h : probe A b k (evalNodes A ((X^2-X)*Q))=0) :
    (∑ j : Fin (n+1), Q.coeff j.val / ((k+j.val+3:ℕ):K)) -
      (∑ j : Fin (n+1), Q.coeff j.val / ((k+j.val+2:ℕ):K))=0 := by
  have he :
      probe A b k (evalNodes A ((X^2-X)*Q)) =
        probe A b (k+2) (evalNodes A Q) - probe A b (k+1) (evalNodes A Q) := by
    simp only [probe,row_apply,dotProduct,evalNodes_apply,←Finset.sum_sub_distrib,eval_mul,eval_sub,eval_pow,eval_X]
    apply Finset.sum_congr rfl
    intro i _
    simp only [pow_add,pow_one]
    ring
  rw [he,evalNodes_eq_coeffEval A Q hd,probe_coeffEval ho (by omega),
    probe_coeffEval ho (by omega)] at h
  have e (j : Fin (n+1)) : k+2+j.val+1=k+j.val+3 := by omega
  have e' (j : Fin (n+1)) : k+1+j.val+1=k+j.val+2 := by omega
  simpa only [e,e'] using h

variable {A : Matrix (Fin 12) (Fin 12) K} {b : Fin 12 → K}

omit [CharZero K] in
theorem probe_shift_diag (A : Matrix (Fin 12) (Fin 12) K) (b v : Fin 12 → K) (k : ℕ) :
    probe A b k (diag (nodes A) v)=probe A b (k+1) v := by
  simp only [probe,row_apply,dotProduct,diag_apply,pow_succ]
  apply Finset.sum_congr rfl
  intro j _
  ring

/-- The terminal unit's native profile. The endpoint normalizer is
nonzero, and the coefficient of Ag vanishes at the doubled clock. -/
theorem order9_terminal_normal_profile (ha : ∀ i j, i ≤ j → A i j = 0) (ho : HasOrder A b 9)
    {a d : K} {i j : Fin 12} (D : GlobalNormal A a d i j) (F : FirstFour A a d (by decide)) :
    ∃ w : NormalCoeffs K,
      normalProfileMap A w=Reverse.coordinate (Fin.last 11) ∧
      endpointF d 1≠0 ∧
      (ofFn 3 w.2.2).eval (2*d)=0 ∧
      (∀ x, (ofFn 6 w.1).eval x=x*(x-2*d)*endpointF d x/((1-2*d)*endpointF d 1)) ∧
      (ofFn 6 w.1).eval 1=1 := by
  obtain ⟨rk,mEq,_,t1⟩ := order9_maximal_normal_profile ha ho D F
  obtain ⟨_,ct,um,_,_,_⟩ := Reverse.orderNine_rank_five_full ha ho rk
  let jT : Fin 12 := Fin.last 11
  let U : Fin 12 → K := Reverse.coordinate jT
  have ru : U∈LinearMap.range (normalProfileMap A) := mEq.symm ▸ um
  obtain ⟨w,wU⟩ := ru
  let P := ofFn 6 w.1
  let Q := ofFn 3 w.2.2
  have f0 : nodes A (0:Fin 12)=0 ∧ g A (0:Fin 12)=0 ∧ h A (0:Fin 12)=0 := by
    simpa [chartNode,chartDefect,chartH] using F.features 0
  have f3 : nodes A (3:Fin 12)=2*d ∧ g A (3:Fin 12)=0 ∧ h A (3:Fin 12)=a*d^2 := by
    simpa [chartNode,chartDefect,chartH] using F.features 3
  have f4 := order9_fifth_feature ha ho D F
  have e0 := (normal_profile_value w (0:Fin 12)).symm.trans (congrFun wU (0:Fin 12))
  have e3 := (normal_profile_value w (3:Fin 12)).symm.trans (congrFun wU (3:Fin 12))
  have e4 := (normal_profile_value w (4:Fin 12)).symm.trans (congrFun wU (4:Fin 12))
  have p0 : P.eval 0=0 := by simpa [f0.1,f0.2.1,f0.2.2,U,Reverse.coordinate,jT] using e0
  have dre : h A (4:Fin 12)≠h A (3:Fin 12) := by rw [f3.2.2]; exact f4.2.2
  have e3' : (0:K)+h A (3:Fin 12)*0=P.eval (2*d)+h A (3:Fin 12)*Q.eval (2*d) := by
    simpa [f3.1,f3.2.1,U,Reverse.coordinate,jT,P,Q] using e3.symm
  have e4' : (0:K)+h A (4:Fin 12)*0=P.eval (2*d)+h A (4:Fin 12)*Q.eval (2*d) := by
    simpa [f4.1,f4.2.1,U,Reverse.coordinate,jT,P,Q] using e4.symm
  obtain ⟨pt,qt⟩ := common_clock_affine_parameters dre e3' e4'
  have gt := rank_five_full_terminal_defect ha ho rk (zeroSpace_mono A (by decide) (mDef_mem A 1))
  have ht := rank_five_full_terminal_defect ha ho rk (h_in_grade_three A)
  have ct' : nodes A jT=1 := ct
  have gt' : g A jT=0 := gt
  have ht' : h A jT=0 := ht
  have p1 : P.eval 1=1 := by
    have e := (normal_profile_value w jT).symm.trans (congrFun wU jT)
    simpa only [ct',gt',ht',U,Reverse.coordinate,Pi.single_eq_same,zero_mul,mul_zero,zero_add,add_zero] using e
  obtain ⟨B,PEq⟩ := X_dvd_iff.mpr (by rwa [coeff_zero_eq_eval_zero] : P.coeff 0=0)
  have Bn : B≠0 := by intro e; simp [PEq,e] at p1
  have bd : B.natDegree≤4 := by
    have pd : P.natDegree<6 := ofFn_natDegree_lt (by decide) _
    have dd := natDegree_mul X_ne_zero Bn
    rw [←PEq,natDegree_X] at dd
    omega
  have Bt : B.eval (2*d)=0 := by
    rw [PEq,eval_mul,eval_X] at pt
    exact (mul_eq_zero.mp pt).resolve_left (mul_ne_zero (by norm_num) D.base.dn)
  have B1 : B.eval 1=1 := by simpa only [PEq,eval_mul,eval_X,one_mul] using p1
  have sumEq : evalNodes A P+wideDefect A (w,0)=U :=
    (wideProfileMap_apply A (w,0)).symm.trans ((wide_at_normal w).trans wU)
  have DM := wide_defect_mem ho (w,0)
  have probesP (k : ℕ) (h : k≤3) : probe A b k (evalNodes A P)=b jT := by
    have e := congrArg (probe A b k) sumEq
    rw [map_add,probe_zeroSpace ho (by omega) DM,add_zero] at e
    rw [e]
    change row _ (Reverse.coordinate jT) = b jT
    rw [Reverse.row_coordinate,ct',one_pow,mul_one]
  have hh (k : Fin 3) : probe A b k.val (evalNodes A ((X^2-X)*B))=0 := by
    have E : evalNodes A ((X^2-X)*B)=diag (nodes A) (evalNodes A P)-evalNodes A P := by
      ext l
      simp only [evalNodes_apply,diag_apply,Pi.sub_apply,PEq,eval_mul,eval_sub,eval_pow,eval_X]
      ring
    rw [E,map_sub,probe_shift_diag,probesP _ (by have := k.isLt; omega),
      probesP _ (by have := k.isLt; omega),sub_self]
  have dec := beta_pair_decoder B bd (fun k => beta_probe_coeff ho B bd
    (by have := k.isLt; omega) (hh k))
  obtain ⟨fn,Be⟩ := terminal_beta_formula dec t1 Bt B1
  refine ⟨w,wU,fn,qt,fun x=>?_,p1⟩
  change P.eval x=_
  rw [PEq,eval_mul,eval_X,Be]
  ring

end RKResearch.Certified.Graded.OneOff
