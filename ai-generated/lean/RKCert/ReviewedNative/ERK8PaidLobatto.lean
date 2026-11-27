module

public import RKCert.ReviewedNative.ERK8PaidPrimitiveTools

import Mathlib.Tactic.IntervalCases

@[expose] public section

/-! # Exact paid Lobatto decoder with its sole extra prime guard
All primitive and moment denominators are paid by order eight. The
omitted-factor resultant is the integer 22, not a characteristic-zero
typeclass. -/
namespace RKResearch.Certified.Graded.ERK8PaidField

open RKResearch Polynomial ERKTaggedHorizon LobattoEight RKCert.Endpoint
open scoped Matrix Classical

variable {K : Type*} [Field K] {s : ℕ} {A : Matrix (Fin s) (Fin s) K}
    {b : Fin s → K}

theorem two_ne (ho : HasOrder 8 A b) : (2:K)≠0 :=
    (ho.natCast_isUnit (n:=2) (by decide) (by decide)).ne_zero

theorem fourteen_ne (ho : HasOrder 8 A b) : (14:K)≠0 := by
  have seven : (7:K)≠0 := (ho.natCast_isUnit (n:=7) (by decide) (by decide)).ne_zero
  rw [show (14:K)=2*7 by ring]
  exact mul_ne_zero (two_ne ho) seven

theorem beta_cubic_from_probes_paid (ho : HasOrder 8 A b) (Q : K[X]) (hd : Q.natDegree≤3)
    (hz : ∀ k : Fin 3, probe A b k.val (evalNodes A ((X^2-X)*Q))=0) :
    Q = C (Q.coeff 3)*lobattoCubic := by
  let c (n : Nat) := Q.coeff n
  let m (n : Nat) : K := 1/((n+1:Nat):K)
  have M (j : Nat) (hj : j<8) : ((j:K)+1)*m j=1 := by
    have nz : (((j+1:Nat):K))≠0 := (ho.natCast_isUnit (by omega) (by omega)).ne_zero
    simpa only [m,Nat.cast_add,Nat.cast_one] using mul_div_cancel₀ (1:K) nz
  have B (j : Nat) (hj : j≤6) :
      ((j:K)+1)*((j:K)+2)*(m j-m (j+1))=1 := by
    have u := M j (by omega)
    have v := M (j+1) (by omega)
    simp only [Nat.cast_add,Nat.cast_one] at v
    linear_combination ((j:K)+2)*u-((j:K)+1)*v
  have raw (k : Fin 3) := beta_probe_coeff ho Q hd (by have := k.isLt; omega) (hz k)
  have E₀ : c 0*(m 1-m 2)+c 1*(m 2-m 3)+c 2*(m 3-m 4)+c 3*(m 4-m 5)=0 := by
    have r := raw 0
    norm_num only [Fin.sum_univ_succ, Fin.val_zero, Fin.val_succ, Nat.reduceAdd,
      Nat.cast_ofNat, Fin.sum_univ_zero, add_zero] at r
    simp only [c,m,Nat.reduceAdd,Nat.cast_ofNat,div_eq_mul_inv,one_mul]
    simp only [div_eq_mul_inv] at r
    linear_combination -r
  have E₁ : c 0*(m 2-m 3)+c 1*(m 3-m 4)+c 2*(m 4-m 5)+c 3*(m 5-m 6)=0 := by
    have r := raw 1
    norm_num only [Fin.sum_univ_succ, Fin.val_zero, Fin.val_one, Fin.val_succ, Nat.reduceAdd,
      Nat.cast_ofNat, Fin.sum_univ_zero, add_zero] at r
    simp only [c,m,Nat.reduceAdd,Nat.cast_ofNat,div_eq_mul_inv,one_mul]
    simp only [div_eq_mul_inv] at r
    linear_combination -r
  have E₂ : c 0*(m 3-m 4)+c 1*(m 4-m 5)+c 2*(m 5-m 6)+c 3*(m 6-m 7)=0 := by
    have r := raw 2
    rw [show (2:Fin 3).val=2 by decide] at r
    norm_num only [Fin.sum_univ_succ, Fin.val_zero, Fin.val_succ, Fin.val_ofNat, Nat.reduceAdd,
      Nat.cast_ofNat, Fin.sum_univ_zero, add_zero] at r
    simp only [c,m,Nat.reduceAdd,Nat.cast_ofNat,div_eq_mul_inv,one_mul]
    simp only [div_eq_mul_inv] at r
    linear_combination -r
  have B₁ := B 1 (by decide)
  have B₂ := B 2 (by decide)
  have B₃ := B 3 (by decide)
  have B₄ := B 4 (by decide)
  have B₅ := B 5 (by decide)
  have B₆ := B 6 (by decide)
  norm_num at B₁ B₂ B₃ B₄ B₅ B₆
  have R₀ : 10*c 0+5*c 1+3*c 2+2*c 3=0 := by
    linear_combination 60*E₀-10*c 0*B₁-5*c 1*B₂-3*c 2*B₃-2*c 3*B₄
  have R₁ : 35*c 0+21*c 1+14*c 2+10*c 3=0 := by
    linear_combination 420*E₁-35*c 0*B₂-21*c 1*B₃-14*c 2*B₄-10*c 3*B₅
  have R₂ : 42*c 0+28*c 1+20*c 2+15*c 3=0 := by
    linear_combination 840*E₂-42*c 0*B₃-28*c 1*B₄-20*c 2*B₅-15*c 3*B₆
  have H₀ : 14*c 0+c 3=0 := by linear_combination 28*R₀-16*R₁+7*R₂
  have H₁ : 14*c 1-9*c 3=0 := by linear_combination -112*R₀+74*R₁-35*R₂
  have H₂ : 2*c 2+3*c 3=0 := by linear_combination 14*R₀-10*R₁+5*R₂
  have q₀ : Q.coeff 0=Q.coeff 3*(-1/14) := by
    change c 0=c 3*(-1/14)
    calc
      c 0=(-c 3)/14 := (eq_div_iff (fourteen_ne ho)).mpr (by linear_combination H₀)
      _=c 3*(-1/14) := by simp only [div_eq_mul_inv]; ring
  have q₁ : Q.coeff 1=Q.coeff 3*(9/14) := by
    change c 1=c 3*(9/14)
    calc
      c 1=(9*c 3)/14 := (eq_div_iff (fourteen_ne ho)).mpr (by linear_combination H₁)
      _=c 3*(9/14) := by simp only [div_eq_mul_inv]; ring
  have q₂ : Q.coeff 2=Q.coeff 3*(-3/2) := by
    change c 2=c 3*(-3/2)
    calc
      c 2=(-3*c 3)/2 := (eq_div_iff (two_ne ho)).mpr (by linear_combination H₂)
      _=c 3*(-3/2) := by simp only [div_eq_mul_inv]; ring
  ext j
  by_cases hj : j≤3
  · interval_cases j <;> simp [coeff_C_mul,lobattoCubic,coeff_monomial,q₀,q₁,q₂]
  · rw [coeff_eq_zero_of_natDegree_lt (by omega : Q.natDegree<j),coeff_C_mul]
    have h0 : 0≠j := by omega
    have h1 : 1≠j := by omega
    have h2 : 2≠j := by omega
    have h3 : 3≠j := by omega
    simp [lobattoCubic,coeff_monomial,coeff_C,Ne.symm h0,h1,h2,h3]

theorem lobatto_zero_ne (ho : HasOrder 8 A b) : (lobattoCubic : K[X]).eval 0 ≠ 0 := by
  simpa [lobattoCubic,eval_monomial] using
    (div_ne_zero (neg_ne_zero.mpr one_ne_zero) (fourteen_ne ho) : ((-1:K)/14) ≠ 0)

theorem lobatto_first_omitted_scalar_paid (ho : HasOrder 8 A b) (elev : (11:K)≠0)
    {P : K[X]} (hP : P.natDegree≤2) {u : K} (hu : u≠0)
    (hf : lobattoCubic = (X-C u)*P) (hprim : (primitive (X*P)).eval u=0) : False := by
  have d0 : ((-1:K)/14)*14=-1 := div_mul_cancel₀ _ (fourteen_ne ho)
  have d1 : ((9:K)/14)*14=9 := div_mul_cancel₀ _ (fourteen_ne ho)
  have d2 : ((-3:K)/2)*2=-3 := div_mul_cancel₀ _ (two_ne ho)
  have rr := lobatto_isRoot_of_linear hf
  simp only [lobattoCubic,eval_add,eval_monomial,pow_zero,pow_one,mul_one,one_mul] at rr
  have root : 14*u^3-21*u^2+9*u-1=0 := by
    linear_combination 14*rr-d0-u*d1-7*u^2*d2
  have hcoef (n : ℕ) : (lobattoCubic : K[X]).coeff (n+1) = P.coeff n-u*P.coeff (n+1) := by
    rw [hf,sub_mul,coeff_sub,coeff_X_mul,coeff_C_mul]
  have h3 := hcoef 2
  have h2 := hcoef 1
  have h1 := hcoef 0
  have uz : P.coeff 3=0 := coeff_eq_zero_of_natDegree_lt (by omega)
  norm_num [lobattoCubic,coeff_add,coeff_monomial,Finsupp.single_apply,uz] at h3 h2 h1
  have H3 : P.coeff 2-1=0 := by linear_combination -h3
  have H2 : 2*P.coeff 1-2*u*P.coeff 2+3=0 := by linear_combination -2*h2+d2
  have H1 : 14*P.coeff 0-14*u*P.coeff 1-9=0 := by linear_combination -14*h1+d1
  rw [primitive_eval_X_quadratic P hP] at hprim
  have np3 : (3:K)≠0 := (ho.natCast_isUnit (n:=3) (by decide) (by decide)).ne_zero
  have np4 : (4:K)≠0 := (ho.natCast_isUnit (n:=4) (by decide) (by decide)).ne_zero
  have e₀ : (P.coeff 0*u^2/2)*2=P.coeff 0*u^2 := div_mul_cancel₀ _ (two_ne ho)
  have e₁ : (P.coeff 1*u^3/3)*3=P.coeff 1*u^3 := div_mul_cancel₀ _ np3
  have e₂ : (P.coeff 2*u^4/4)*4=P.coeff 2*u^4 := div_mul_cancel₀ _ np4
  have m : 6*P.coeff 0*u^2+4*P.coeff 1*u^3+3*P.coeff 2*u^4=0 := by
    linear_combination 12*hprim-6*e₀-4*e₁-3*e₂
  have z : u^2*(91*u^2-105*u+27)=0 := by
    linear_combination 7*m-91*u^4*H3-35*u^3*H2-3*u^2*H1
  have g := (mul_eq_zero.mp z).resolve_left (pow_ne_zero _ hu)
  have h22 : (2:K)*11=0 := by
    linear_combination (464-819*u)*root+(126*u^2-115*u+18)*g
  exact mul_ne_zero (two_ne ho) elev h22

theorem lobattoCubic_degree_paid : (lobattoCubic : K[X]).natDegree=3 := by
  apply natDegree_eq_of_le_of_coeff_ne_zero
  · apply natDegree_le_iff_coeff_eq_zero.mpr
    intro i hi
    have hi0 : 0≠i := by omega
    have hi1 : 1≠i := by omega
    have hi2 : 2≠i := by omega
    have hi3 : 3≠i := by omega
    simp [lobattoCubic,coeff_monomial,coeff_C,Ne.symm hi0,hi1,hi2,hi3]
  · simp [lobattoCubic,coeff_monomial]

/-- A quadratic divisor of the fixed cubic leaves one exact linear
factor, with no ordering on roots needed. -/
theorem lobatto_divisor_linear_factor_paid {P : K[X]} (hd : P.natDegree=2)
    (hdiv : P∣lobattoCubic) :
    ∃ u a : K, a≠0 ∧ lobattoCubic = (X-C u)*(C a*P) := by
  obtain ⟨R,he⟩ := hdiv
  have hn : (lobattoCubic : K[X])≠0 := by
    intro h; have hd := lobattoCubic_degree_paid (K:=K); simp [h] at hd
  have hR : R≠0 := by intro h; apply hn; simp [he,h]
  have hP : P≠0 := by intro h; apply hn; simp [he,h]
  have hdeg := natDegree_mul hP hR
  rw [←he,lobattoCubic_degree_paid,hd] at hdeg
  obtain ⟨a,ha,b,hb⟩ := Polynomial.natDegree_eq_one.mp (by omega : R.natDegree=1)
  let u := -b/a
  have hconst : -(a*u)=b := by
    dsimp [u]
    field_simp [ha]
  have hR' : R=(X-C u)*C a := by
    rw [←hb,sub_mul,mul_comm X,←map_mul,mul_comm u a,sub_eq_add_neg,← map_neg,hconst]
  exact ⟨u,a,ha,by rw [he,hR']; ring⟩

end RKResearch.Certified.Graded.ERK8PaidField
