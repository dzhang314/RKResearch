module

public import RKCert.DirkPolynomialMarked

@[expose] public section

/-! # Exact polynomial consequences of the two-ended DIRK signatures

This module handles multiplicities when two different physical signatures
share one clock. The affine reduction is exact divisibility, retaining any
repeated polynomial factor. The Gram gate derives necessary determinants;
it does not by itself assert their nonvanishing. -/
namespace RKCert.Paired.Signature
open RKCert.Endpoint Polynomial
open scoped Classical

noncomputable section
variable {K : Type*} [Field K] {n : ℕ}

def fiberAt (clock : Fin n → K) (x : K) : Finset (Fin n) :=
  Finset.univ.filter fun i => clock i=x

/-- A signature at a double clock pays a double root only when BOTH factors
vanish there. Counting physical coordinates as simple roots is not sound. -/
theorem counted_factors_zero (clock : Fin n → K) (F G : K[X])
    (hd : F.natDegree+G.natDegree<n)
    (hcap : ∀ x, (fiberAt clock x).card≤2)
    (hf : ∀ i, F.eval (clock i)*G.eval (clock i)=0)
    (hboth : ∀ i j, i≠j → clock i=clock j →
      F.eval (clock i)=0 ∧ G.eval (clock i)=0) :
    F*G=0 := by
  let Z := Finset.univ.image clock
  let Q := fun x : K => (X-C x) ^ ((fiberAt clock x).card)
  have all (x : K) (hx : x∈Z) : Q x ∣ F*G := by
    obtain ⟨i,_,hi⟩ := Finset.mem_image.mp hx
    have hiT : i∈fiberAt clock x := by simp [fiberAt,hi]
    have hc0 : 0<(fiberAt clock x).card := Finset.card_pos.mpr ⟨i,hiT⟩
    have hc2 := hcap x
    rcases (show (fiberAt clock x).card=1 ∨ (fiberAt clock x).card=2 by omega) with hc|hc
    · dsimp [Q]
      rw [hc,pow_one,dvd_iff_isRoot,IsRoot.def,eval_mul,←hi]
      exact hf i
    · have he : ∃ j∈fiberAt clock x,j≠i := by
        by_contra hx
        have hs : fiberAt clock x ⊆ {i} := by
          intro j hj
          apply Finset.mem_singleton.mpr
          by_contra hne
          exact hx ⟨j,hj,hne⟩
        have hc' := Finset.card_le_card hs
        rw [Finset.card_singleton,hc] at hc'
        omega
      obtain ⟨j,hj,hne⟩ := he
      have hxj : clock j=x := by simpa [fiberAt] using hj
      have hfG := hboth i j hne.symm (hi.trans hxj.symm)
      have hX1 : X-C x∣F := dvd_iff_isRoot.mpr (hi ▸ hfG.1)
      have hX2 : X-C x∣G := dvd_iff_isRoot.mpr (hi ▸ hfG.2)
      dsimp [Q]
      rw [hc,pow_two]
      exact mul_dvd_mul hX1 hX2
  have hdiv : (∏ x ∈ Z,Q x)∣F*G := by
    apply Finset.prod_dvd_of_coprime _ all
    intro a _ b _ hab
    exact (isCoprime_X_sub_C_of_isUnit_sub (sub_ne_zero.mpr hab).isUnit).pow
  have hp : (∏ x∈Z,Q x).natDegree = n := by
    rw [natDegree_prod_of_monic Z Q (fun x _ => (monic_X_sub_C x).pow _)]
    simp only [Q,natDegree_pow,natDegree_X_sub_C,mul_one]
    simpa only [Z,fiberAt,Finset.card_univ,Fintype.card_fin] using
      (Finset.card_eq_sum_card_image clock (Finset.univ : Finset (Fin n))).symm
  exact eq_zero_of_dvd_of_natDegree_lt hdiv (by
    have h := natDegree_mul_le (p:=F) (q:=G)
    omega)

/-- The exact k=1 finite-signature reduction. It is not a stage-rank result:
the hypothesis that the eighteen retained signatures are distinct must
come from the actual terminal-deleted evaluation. -/
theorem close_mixed_signatures (c w : Fin n → K) (D R S P : K[X])
    (hD : D≠0)
    (hdeg : D.natDegree+(D*S-P*R).natDegree<n)
    (hpair : Function.Injective (fun i => (c i,w i)))
    (hcounts : ∀ x, (fiberAt c x).card≤2)
    (hR : ∀ i,D.eval (c i)=w i*R.eval (c i))
    (hP : ∀ i,w i≠0 → P.eval (c i)=w i*S.eval (c i)) :
    D*S=P*R := by
  have hzero := counted_factors_zero c D (D*S-P*R) hdeg hcounts ?_ ?_
  · exact sub_eq_zero.mp ((mul_eq_zero.mp hzero).resolve_left hD)
  · intro i
    by_cases hwi : w i=0
    · simp [hR i,hwi]
    · rw [eval_sub,eval_mul,eval_mul,hR i,hP i hwi]
      ring
  · intro i j hij he
    have hww : w i≠w j := fun e => hij (hpair (Prod.ext he e))
    have h0 : (w i-w j)*R.eval (c i)=0 := by
      have h₁ := hR i
      have h₂ := hR j
      rw [←he] at h₂
      rw [sub_mul,←h₁,←h₂,sub_self]
    have hR0 := (mul_eq_zero.mp h0).resolve_left (sub_ne_zero.mpr hww)
    have hD0 : D.eval (c i)=0 := by rw [hR i,hR0,mul_zero]
    exact ⟨hD0,by simp [hD0,hR0]⟩

/-- Degree-one expansion without allocating a positive leading coefficient. -/
theorem affine_expansion (S : K[X]) (hS : S.natDegree≤1) :
    S=C (S.coeff 0)+C (S.coeff 1)*X := by
  have h := S.as_sum_range' 2 (by omega)
  rw [Finset.sum_range_succ,Finset.sum_range_one] at h
  rw [←C_mul_X_pow_eq_monomial,←C_mul_X_pow_eq_monomial,pow_zero,pow_one,mul_one] at h
  exact h

/-- When P does not divide D there is a genuine affine factor of P and its
other factor divides D, including multiplicities. -/
theorem affine_factor_from_mixed (D R S P : K[X]) (hP : P≠0) (hS : S≠0)
    (dS : S.natDegree≤1) (dP : P.natDegree≤4)
    (he : D*S=P*R) (hno : ¬P∣D) :
    ∃ T : K[X], T≠0 ∧ T.natDegree≤3 ∧ P=S*T ∧ T∣D := by
  have notdvd : ¬S∣R := by
    rintro ⟨Q,rfl⟩
    apply hno
    refine ⟨Q,?_⟩
    apply mul_right_cancel₀ hS
    rw [he]
    ring
  have dS' : S.natDegree=1 := by
    by_contra hne
    have hz : S.natDegree=0 := by omega
    have H := eq_C_of_natDegree_eq_zero hz
    have hc : S.coeff 0≠0 := by intro hh; rw [H,hh,C_0] at hS; exact hS rfl
    apply notdvd
    refine ⟨C (S.coeff 0)⁻¹ * R,?_⟩
    calc
      R = (C (S.coeff 0)*C ((S.coeff 0)⁻¹)) * R := by
        rw [←map_mul,mul_inv_cancel₀ hc,map_one,one_mul]
      _ = S * (C ((S.coeff 0)⁻¹) * R) := by
        rw [mul_assoc]
        exact congrArg (fun u : K[X] => u * (C ((S.coeff 0)⁻¹) * R)) H.symm
  have h1 : S.coeff 1≠0 := by
    rw [←dS']
    exact leadingCoeff_ne_zero.mpr hS
  let t := -S.coeff 0/S.coeff 1
  have ht : S.eval t=0 := by
    rw [affine_expansion S dS]
    simp only [eval_add,eval_mul,eval_C,eval_X,t]
    field_simp
    ring
  have hSX : S=C (S.coeff 1)*(X-C t) := by
    calc
      S = C (S.coeff 0)+C (S.coeff 1)*X := affine_expansion S dS
      _ = C (S.coeff 1)*(X-C t) := by
        rw [mul_sub,←map_mul]
        have he' : S.coeff 1*t= -S.coeff 0 := by
          dsimp [t]
          field_simp
        rw [he',map_neg,sub_neg_eq_add,add_comm]
  have dvd_of_zero (Q : K[X]) (hQ : Q.eval t=0) : S∣Q := by
    obtain ⟨V,hV⟩ := dvd_iff_isRoot.mpr (show Q.IsRoot t from hQ)
    refine ⟨C (S.coeff 1)⁻¹*V,?_⟩
    calc
      Q = (X-C t) * V := hV
      _ = (X-C t)*(C (S.coeff 1)*C ((S.coeff 1)⁻¹))*V := by
        rw [←map_mul,mul_inv_cancel₀ h1,map_one,mul_one]
      _ = (C (S.coeff 1)*(X-C t))*(C ((S.coeff 1)⁻¹)*V) := by ac_rfl
      _ = S*(C ((S.coeff 1)⁻¹)*V) :=
        congrArg (fun u : K[X] => u*(C ((S.coeff 1)⁻¹)*V)) hSX.symm
  have hg := congrArg (Polynomial.eval t) he
  simp only [eval_mul,ht,mul_zero] at hg
  have htp := (mul_eq_zero.mp hg.symm).resolve_right (fun hz => notdvd (dvd_of_zero R hz))
  obtain ⟨T,hT⟩ := dvd_of_zero P htp
  have htn : T≠0 := fun z => hP (by simp [hT,z])
  have dT : T.natDegree≤3 := by
    rw [hT,natDegree_mul hS htn,dS'] at dP
    omega
  refine ⟨T,htn,dT,hT,⟨R,?_⟩⟩
  apply mul_right_cancel₀ hS
  rw [he,hT]
  ring

variable [CharZero K]

def paidMoment (T : K[X]) (u : K) (j : ℕ) : K := (formalPrimitive (X^j*T)).eval u

theorem paidMoment_affine (S T : K[X]) (hS : S.natDegree≤1) (u : K) (j : ℕ) :
    paidMoment (S*T) u j =
      S.coeff 0*paidMoment T u j + S.coeff 1*paidMoment T u (j+1) := by
  have e : X^j*(S*T)=S.coeff 0 • (X^j*T)+S.coeff 1 • (X^(j+1)*T) := by
    conv_lhs => rw [affine_expansion S hS]
    rw [smul_eq_C_mul,smul_eq_C_mul,pow_succ]
    ring
  change (formalPrimitiveLinear (X^j*(S*T))).eval u=_
  rw [e,map_add,map_smul,map_smul,eval_add,eval_smul,eval_smul,smul_eq_mul,smul_eq_mul]
  rfl

/-- The two adjacent primitive equations imply the 2-by-2 Gram
determinant, even if one coefficient of the affine multiplier is zero. -/
theorem affine_gram_zero (S T : K[X]) (hS : S≠0) (dS : S.natDegree≤1)
    (u : K) (j : ℕ) (h1 : paidMoment (S*T) u j=0)
    (h2 : paidMoment (S*T) u (j+1)=0) :
    paidMoment T u j*paidMoment T u (j+2)-(paidMoment T u (j+1))^2=0 := by
  rw [paidMoment_affine S T dS] at h1 h2
  have d0 (h : S.coeff 0≠0) :
      paidMoment T u j*paidMoment T u (j+2)-(paidMoment T u (j+1))^2=0 := by
    apply mul_left_cancel₀ h
    rw [mul_zero]
    linear_combination paidMoment T u (j+2)*h1 - paidMoment T u (j+1)*h2
  by_cases ha : S.coeff 0=0
  · have hb : S.coeff 1≠0 := by
      intro hh
      exact hS (by rw [affine_expansion S dS,ha,hh]; simp)
    apply mul_left_cancel₀ hb
    rw [mul_zero]
    linear_combination paidMoment T u j*h2 - paidMoment T u (j+1)*h1
  · exact d0 ha

/-- The two low-degree monomial base cases need no finite certificate. -/
theorem affine_monomial_impossible (S : K[X]) (dS : S.natDegree≤1) (e : ℕ)
    (u : K) (hu : u≠0)
    (h1 : paidMoment (S*X^e) u 1=0)
    (h2 : paidMoment (S*X^e) u 2=0) : S=0 := by
  apply primitive_shift_detect S dS u hu (k:=1+e)
  intro k
  have hk : k.val=0 ∨ k.val=1 := by have := k.isLt; omega
  have hm (j : ℕ) : X^(j+e)*S=X^j*(S*X^e) := by
    rw [pow_add]
    ac_rfl
  rcases hk with h|h
  · simpa only [h,add_zero,hm,paidMoment] using h1
  · have e' : (1+e)+1=2+e := by omega
    simpa only [h,e',hm,paidMoment] using h2

end
end RKCert.Paired.Signature
