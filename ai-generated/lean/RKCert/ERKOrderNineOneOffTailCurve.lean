module

public import RKCert.ERKOrderNineOneOffSeventh
public import RKCert.ERKOrderNineOneOffTailCubic

@[expose] public section

/-! # A polynomial ordinary curve after the two actual repeated fibres -/
namespace RKCert.Paired.OneOff.Seven
open Polynomial Module
open scoped Classical

variable {K : Type*} [Field K] [CharZero K] {A : Fin 12→Fin 12→K}

def betaScale (d : K) : K := 588/(2*(1-2*d)*paramU d)
noncomputable def betaAlpha (d : K) : K := betaScale d*(lobattoCubic : K[X]).eval (2*d)
noncomputable def betaEta (d : K) : K := -(betaScale d*(lobattoPencil 0 : K[X]).eval (2*d))

noncomputable def endBeta (d : K) : K[X] :=
  C (betaAlpha d)*lobattoPencil 0+C (betaEta d)*lobattoCubic

theorem endBeta_times_x (d x : K) : x*(endBeta d).eval x=endP d x := by
  rw [endP,show x*(x-2*d)*endpointF d x=x*((x-2*d)*endpointF d x) by ring,
    endpointF_jacobi]
  simp only [endBeta,betaAlpha,betaEta,betaScale,eval_add,eval_mul,eval_C]
  ring

theorem endBeta_degree (d : K) : (endBeta d).natDegree≤4 := by
  unfold endBeta
  apply natDegree_add_le_of_le (m:=4) (n:=4)
  · exact (natDegree_C_mul_le _ _).trans (lobattoPencil_natDegree 0).le
  · exact (natDegree_C_mul_le _ _).trans ((lobattoCubic_degree (K:=K)).le.trans (by decide))

theorem endBeta_roots (d z : K) (dn : d≠0) (zn : z≠0)
    (pz : endP d z=0) (pd : endP d d≠0) (p1 : endP d 1=1) :
    (endBeta d).eval (2*d)=0 ∧ (endBeta d).eval z=0 ∧
    (endBeta d).eval d≠0 ∧ (endBeta d).eval 1≠0 := by
  have rt := endBeta_times_x d (2*d)
  rw [show endP d (2*d)=0 by simp [endP]] at rt
  have rz := (endBeta_times_x d z).trans pz
  refine ⟨(mul_eq_zero.mp rt).resolve_left (mul_ne_zero (by norm_num) dn),
    (mul_eq_zero.mp rz).resolve_left zn,?_,?_⟩
  · intro e
    exact pd (by rw [←endBeta_times_x,e,mul_zero])
  · intro e
    exact zero_ne_one (by rw [←p1,←endBeta_times_x,e,mul_zero])

theorem endBeta_alternatives (d z : K) (dn : d≠0) (zn : z≠0)
    (pz : endP d z=0) (pd : endP d d≠0) (p1 : endP d 1=1) :
    ((lobattoCubic : K[X]).eval (2*d)=0 ∧ (lobattoCubic : K[X]).eval z=0 ∧
      (lobattoCubic : K[X]).eval d≠0 ∧ (lobattoCubic : K[X]).eval 1≠0) ∨
    ∃ l : K, (lobattoPencil l).eval (2*d)=0 ∧ (lobattoPencil l).eval z=0 ∧
      (lobattoPencil l).eval d≠0 ∧ (lobattoPencil l).eval 1≠0 := by
  obtain ⟨rt,rz,rd,r1⟩ := endBeta_roots d z dn zn pz pd p1
  by_cases aa : betaAlpha d=0
  · have rep (x : K) : (endBeta d).eval x=betaEta d*(lobattoCubic : K[X]).eval x := by
      simp [endBeta,aa]
    have en : betaEta d≠0 := by intro e; exact r1 (by rw [rep,e,zero_mul])
    rw [rep, mul_eq_zero] at rt rz
    exact Or.inl ⟨rt.resolve_left en,rz.resolve_left en,
      fun h=>rd (by rw [rep,h,mul_zero]),fun h=>r1 (by rw [rep,h,mul_zero])⟩
  · let l := betaEta d/betaAlpha d
    have rep (x : K) : (endBeta d).eval x=betaAlpha d*(lobattoPencil l).eval x := by
      rw [eval_lobattoPencil_affine l x]
      simp only [endBeta,eval_add,eval_mul,eval_C]
      simp only [l]
      field_simp [aa] <;> ring
    rw [rep,mul_eq_zero] at rt rz
    exact Or.inr ⟨l,rt.resolve_left aa,rz.resolve_left aa,
      fun h=>rd (by rw [rep,h,mul_zero]),fun h=>r1 (by rw [rep,h,mul_zero])⟩

theorem two_fibres_divide {P : K[X]} {t z : K} (zt : z≠t)
    (ht : P.eval t=0) (hz : P.eval z=0) :
    fibrePoly t z∣P := by
  exact (isCoprime_X_sub_C_of_isUnit_sub (sub_ne_zero.mpr (Ne.symm zt)).isUnit).mul_dvd
    (dvd_iff_isRoot.mpr ht) (dvd_iff_isRoot.mpr hz)

theorem ordinary_curve {a d z : K} (D : TwoFibres A a d z)
    (dn : d≠0) (zn : z≠0) (zt : z≠2*d) :
    ∃ L : K[X], L.natDegree≤3 ∧
      ∀ r : Fin 12, r≠Fin.last 11 → g A r=0 →
        nodes A r≠2*d → nodes A r≠z → scaledH A a r=L.eval (nodes A r) := by
  let t := 2*d
  let F := fibrePoly t z
  let P := endBeta d
  let Q := terminalQ d z
  have qn : Q≠0 := D.q_nonzero
  have pn : P≠0 := by
    intro p
    exact ((endBeta_roots d z dn zn D.pz D.pd D.endpoint.p1).2.2.2) (by rw [show endBeta d=0 from p];simp)
  obtain ⟨W,ew⟩ := two_fibres_divide zt (show Q.eval t=0 from by simp [Q,t,terminalQ_eval]) D.qz
  have Wn : W≠0 := by intro e; exact qn (by rw [ew,e,mul_zero])
  have WD : W.natDegree≤0 := by
    have dQ := terminalQ_degree d z
    have dd := natDegree_mul (fibrePoly_monic t z).ne_zero Wn
    change (F*W).natDegree=F.natDegree+W.natDegree at dd
    rw [←ew,show F.natDegree=2 from fibrePoly_degree t z] at dd
    change Q.natDegree≤2 at dQ
    omega
  let k := W.coeff 0
  rw [eq_C_of_natDegree_le_zero WD] at ew
  have kn : k≠0 := by intro e; exact qn (by rw [ew,show W.coeff 0=0 from e,C_0,mul_zero])
  obtain ⟨pt,pz,_,_⟩ := endBeta_roots d z dn zn D.pz D.pd D.endpoint.p1
  obtain ⟨B,eb⟩ := two_fibres_divide zt pt pz
  have Bn : B≠0 := by intro h; exact pn (by change endBeta d=0; rw [eb,h,mul_zero])
  have Bd : B.natDegree≤2 := by
    have hh := natDegree_mul (fibrePoly_monic t z).ne_zero Bn
    rw [←eb,fibrePoly_degree] at hh
    have hb := endBeta_degree d
    omega
  let L : K[X] := C (-k⁻¹)*(X*B)
  refine ⟨L,(natDegree_C_mul_le _ _).trans (natDegree_mul_le_of_le
    (show (X:K[X]).natDegree≤1 by simp) Bd),?_⟩
  intro r rne gr nt nz
  let x := nodes A r
  have e := D.endpoint.eq_on r rne gr
  change endP d x+Q.eval x*scaledH A a r=0 at e
  rw [←endBeta_times_x,eb,ew,eval_mul,eval_mul,eval_C] at e
  have non : F.eval x≠0 := by
    simp only [F,fibrePoly,eval_mul,eval_sub,eval_X,eval_C]
    exact mul_ne_zero (sub_ne_zero.mpr nt) (sub_ne_zero.mpr nz)
  have ez : F.eval x*(x*B.eval x+k*scaledH A a r)=0 := by linear_combination e
  have ez' := (mul_eq_zero.mp ez).resolve_left non
  simp only [L,eval_mul,eval_C,eval_X]
  apply mul_left_cancel₀ kn
  have cancel : k*k⁻¹=1 := mul_inv_cancel₀ kn
  linear_combination ez' + (x*B.eval x)*cancel

end RKCert.Paired.OneOff.Seven
