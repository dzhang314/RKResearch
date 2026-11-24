module

public import RKCert.Dirk15SignatureAlgebra

@[expose] public section

/-! # A field-safe, nearly balanced two-pivot primitive cut
No positivity or ordering of the field is used. Triple integration pins the
degree-three profile to one explicit polynomial; the two shifted tests at
the second nonzero pivot are then incompatible in characteristic zero. -/
namespace RKCert.Paired.Signature
open RKCert.Endpoint Polynomial

variable {K : Type*} [Field K] [CharZero K]

set_option maxHeartbeats 500000 in
theorem balanced_three_two_impossible (P : K[X]) (hP : P≠0) (dP : P.natDegree≤3)
    {u v : K} (hu : u≠0) (hv : v≠0) (hneq : v≠u)
    (h₁ : paidMoment P u 1=0) (h₂ : paidMoment P u 2=0) (h₃ : paidMoment P u 3=0)
    (k₁ : paidMoment ((X-C u)*P) v 1=0)
    (k₂ : paidMoment ((X-C u)*P) v 2=0) : False := by
  let F := formalPrimitive (formalPrimitive (formalPrimitive ((X:K[X])*P)))
  have F₁ : F.derivative=formalPrimitive (formalPrimitive (X*P)) := derivative_formalPrimitive _
  have F₂ : F.derivative.derivative=formalPrimitive (X*P) := by rw [F₁,derivative_formalPrimitive]
  have F₃ : F.derivative.derivative.derivative=X*P := by rw [F₂,derivative_formalPrimitive]
  have hz0 : F.eval 0=0 := formalPrimitive_eval_zero _
  have hz1 : F.derivative.eval 0=0 := by rw [F₁,formalPrimitive_eval_zero]
  have hz2 : F.derivative.derivative.eval 0=0 := by rw [F₂,formalPrimitive_eval_zero]
  have hz3 : F.derivative.derivative.derivative.eval 0=0 := by rw [F₃,eval_mul,eval_X,zero_mul]
  have hn : F≠0 := by
    intro he
    rw [he,derivative_zero,derivative_zero,derivative_zero] at F₃
    exact (mul_ne_zero X_ne_zero hP) F₃.symm
  have hdeg : F.natDegree≤7 := by
    have h1 := natDegree_mul_le (p:=(X:K[X])) (q:=P)
    rw [natDegree_X] at h1
    have h2 := natDegree_formalPrimitive_le (X*P)
    have h3 := natDegree_formalPrimitive_le (formalPrimitive (X*P))
    have h4 := natDegree_formalPrimitive_le
      (formalPrimitive (formalPrimitive ((X:K[X])*P)))
    dsimp [F]
    omega
  have j₂ : formalPrimitive (X^2*P)=X*F.derivative.derivative-F.derivative := by
    apply eq_of_derivative_and_eval_zero
    · rw [derivative_formalPrimitive,derivative_sub,derivative_mul,derivative_X,F₃,one_mul]
      ring
    · simp only [eval_sub,eval_mul,eval_X,zero_mul,hz1,sub_self,formalPrimitive_eval_zero]
  have j₃ : formalPrimitive (X^3*P)=
      X^2*F.derivative.derivative-2*X*F.derivative+2*F := by
    apply eq_of_derivative_and_eval_zero
    · simp only [derivative_formalPrimitive,derivative_add,derivative_sub,derivative_mul,
        derivative_pow,derivative_X,derivative_ofNat,F₃,map_natCast]
      norm_num; ring
    · simp only [eval_add,eval_sub,eval_mul,eval_X,eval_ofNat,eval_pow,zero_pow (by decide : 2≠0),
        zero_mul,mul_zero,hz0,sub_self,add_zero,formalPrimitive_eval_zero]
  have t₂ : F.derivative.derivative.eval u=0 := by simpa only [F₂,paidMoment,pow_one] using h₁
  have t₁ : F.derivative.eval u=0 := by
    simp only [paidMoment,j₂,eval_sub,eval_mul,eval_X,t₂,mul_zero,zero_sub,neg_eq_zero] at h₂
    exact h₂
  have t₀ : F.eval u=0 := by
    simp only [paidMoment,j₃,eval_add,eval_sub,eval_mul,eval_ofNat,eval_pow,eval_X,t₂,t₁,
      mul_zero,sub_self,zero_add] at h₃
    exact (mul_eq_zero.mp h₃).resolve_left (by norm_num)
  have factor0 : X^4∣F := by
    suffices h : (X-C (0:K))^4∣F from by simpa only [C_0,sub_zero] using h
    apply (le_rootMultiplicity_iff hn).mp
    apply lt_rootMultiplicity_of_isRoot_iterate_derivative hn
    intro n hh
    rcases (show n=0 ∨ n=1 ∨ n=2 ∨ n=3 by omega) with rfl|rfl|rfl|rfl
    · simpa [IsRoot.def] using hz0
    · simpa [IsRoot.def] using hz1
    · simpa [IsRoot.def,Function.iterate_succ_apply'] using hz2
    · simpa [IsRoot.def,Function.iterate_succ_apply'] using hz3
  have factoru : (X-C u)^3∣F := by
    apply (le_rootMultiplicity_iff hn).mp
    apply lt_rootMultiplicity_of_isRoot_iterate_derivative hn
    intro n hh
    rcases (show n=0 ∨ n=1 ∨ n=2 by omega) with rfl|rfl|rfl
    · simpa [IsRoot.def] using t₀
    · simpa [IsRoot.def] using t₁
    · simpa [IsRoot.def,Function.iterate_succ_apply'] using t₂
  have hcop : IsCoprime (X:K[X]) (X-C u) := by
    simpa using isCoprime_X_sub_C_of_isUnit_sub (sub_ne_zero.mpr hu.symm).isUnit
  have nXu : (X-C u:K[X]) ≠ 0 := (monic_X_sub_C u).ne_zero
  obtain ⟨G,hG⟩ := hcop.pow.mul_dvd factor0 factoru
  have hnA : (X^4*(X-C u)^3:K[X])≠0 :=
    mul_ne_zero (pow_ne_zero _ X_ne_zero) (pow_ne_zero _ nXu)
  have hnG : G≠0 := fun hg => hn (by rw [hG,hg,mul_zero])
  have hdA : (X^4*(X-C u)^3:K[X]).natDegree=7 := by
    rw [natDegree_mul (pow_ne_zero _ X_ne_zero) (pow_ne_zero _ nXu),natDegree_pow,
      natDegree_pow,natDegree_X,natDegree_X_sub_C]
  have hdG : G.natDegree=0 := by
    rw [hG,natDegree_mul hnA hnG,hdA] at hdeg
    omega
  let κ := G.coeff 0
  have hGc : G=C κ := eq_C_of_natDegree_eq_zero hdG
  have hκ : κ≠0 := fun e => hnG (by rw [hGc,e,C_0])
  have hfact : F=C κ*(X^4*(X-C u)^3) := by rw [hG,hGc,mul_comm]
  let t := v-u
  have ht : t≠0 := sub_ne_zero.mpr hneq
  have f0 : F.eval v=κ*v^4*t^3 := by simp only [hfact,eval_mul,eval_C,eval_pow,eval_X,eval_sub,t]; ring
  have full1 : F.derivative=C κ*(4*X^3*(X-C u)^3+3*X^4*(X-C u)^2) := by
    rw [hfact]
    simp only [derivative_mul,derivative_C,zero_mul,zero_add,derivative_pow,derivative_sub,
      derivative_X,sub_zero,map_natCast]
    norm_num; ring_nf; simp
  have full2 : F.derivative.derivative=
      C κ*(12*X^2*(X-C u)^3+24*X^3*(X-C u)^2+6*X^4*(X-C u)) := by
    rw [full1]
    simp only [derivative_add,derivative_mul,derivative_C,derivative_ofNat,zero_mul,zero_add,
      derivative_pow,derivative_sub,derivative_X,sub_zero,map_natCast]
    norm_num; ring_nf; simp
  have f1 : F.derivative.eval v=κ*(4*v^3*t^3+3*v^4*t^2) := by
    simp [full1,t]
  have f2 : F.derivative.derivative.eval v=κ*(12*v^2*t^3+24*v^3*t^2+6*v^4*t) := by
    simp [full2,t]
  have hlin (i : ℕ) : formalPrimitive (X^i*((X-C u)*P)) =
      formalPrimitive (X^(i+1)*P)-C u*formalPrimitive (X^i*P) := by
    have e : (X^i*((X-C u)*P):K[X])=X^(i+1)*P-u • (X^i*P) := by
      rw [pow_succ,smul_eq_C_mul]; ring
    change formalPrimitiveLinear (X^i*((X-C u)*P))=_
    rw [e,map_sub,map_smul,smul_eq_C_mul]
    rfl
  have g1 : t*F.derivative.derivative.eval v-F.derivative.eval v=0 := by
    unfold paidMoment at k₁
    rw [hlin] at k₁
    simp only [Nat.reduceAdd,j₂,pow_one,←F₂,eval_sub,eval_mul,eval_X,eval_C] at k₁
    dsimp [t]
    linear_combination k₁
  have g2 : t*F.derivative.eval v-2*F.eval v=0 := by
    unfold paidMoment at k₂
    rw [hlin] at k₂
    simp only [Nat.reduceAdd,j₂,j₃,eval_add,eval_sub,eval_mul,eval_C,eval_ofNat,eval_pow,eval_X] at k₂
    dsimp [t] at g1 ⊢
    linear_combination v*g1-k₂
  rw [f0,f1] at g2
  have g2' : κ*v^3*t^3*(4*t+v)=0 := by linear_combination g2
  have rel := (mul_eq_zero.mp g2').resolve_left (mul_ne_zero
    (mul_ne_zero hκ (pow_ne_zero _ hv)) (pow_ne_zero _ ht))
  have ev : v= -(4*t) := by linear_combination rel
  rw [f1,f2] at g1
  have g1' : κ*v^2*t^2*(12*t^2+20*v*t+3*v^2)=0 := by linear_combination g1
  have E := (mul_eq_zero.mp g1').resolve_left (mul_ne_zero
    (mul_ne_zero hκ (pow_ne_zero _ hv)) (pow_ne_zero _ ht))
  rw [ev] at E
  have hz : (-20:K)*t^2=0 := by linear_combination E
  exact (mul_ne_zero (by norm_num) (pow_ne_zero _ ht)) hz

end RKCert.Paired.Signature
