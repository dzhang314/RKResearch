module

public import RKCert.CompanionPaidMoment

@[expose] public section

/-! # Exact omitted-root reduction to one fixed divided-difference family

The unknown free parameter is eliminated using the actual omitted root.
No polynomial splitting is needed to pass an arbitrary factor to the
companion quotient, even when repeated factors remain after taking out
one explicit endpoint factor.
-/
namespace RKCert.FixedPolynomial
open Polynomial RKCert.Compound RKCert.Paired.Signature
open scoped Classical
noncomputable section
variable {K : Type*} [Field K]

def omittedDifference (H L : K[X]) (u : K) : K[X] :=
  (C (L.eval u)*H-C (H.eval u)*L) /ₘ (X-C u)

theorem linear_factor_coprime_of_eval_ne {P : K[X]} {u : K} (nonzero : P.eval u≠0) :
    IsCoprime P (X-C u) := by
  have rz : (P-C (P.eval u)).eval u=0 := by simp
  obtain ⟨Q,e⟩ := dvd_iff_isRoot.mpr rz
  let a := (P.eval u)⁻¹
  have t : C a*C (P.eval u)=1 := by
    change C (P.eval u)⁻¹*C (P.eval u)=1
    rw [←map_mul,inv_mul_cancel₀ nonzero,map_one]
  refine ⟨C a,-C a*Q,?_⟩
  have p : P-C (P.eval u)=(X-C u)*Q := e
  linear_combination C a*p+t

theorem omittedDifference_mul (H L : K[X]) (u a : K)
    (root : (H+C a*L).eval u=0) :
    (X-C u)*omittedDifference H L u=C (L.eval u)*(H+C a*L) := by
  let P := C (L.eval u)*H-C (H.eval u)*L
  have e : P=C (L.eval u)*(H+C a*L) := by
    have root : H.eval u+a*L.eval u=0 := by simpa only [eval_add,eval_mul,eval_C] using root
    have ec : H.eval u= -(a*L.eval u) := eq_neg_of_add_eq_zero_left root
    change C (L.eval u)*H-C (H.eval u)*L=_
    rw [ec,map_neg,map_mul]
    ring
  have he : P.eval u=0 := by rw [e,eval_mul,root,mul_zero]
  exact ((mul_divByMonic_eq_iff_isRoot).mpr he).trans e

theorem omitted_factor_no_endpoint (H L : K[X]) (u a : K)
    (root : (H+C a*L).eval u=0) {T : K[X]} (d : T∣H+C a*L) (uNe : T.eval u≠0) :
    T∣omittedDifference H L u := by
  have e : T∣(X-C u)*omittedDifference H L u := by
    rw [omittedDifference_mul H L u a root]
    exact d.mul_left _
  exact (linear_factor_coprime_of_eval_ne uNe).dvd_of_dvd_mul_left e

/-- Remove at most one explicit X from the paid factor. This does not
discard any additional multiplicity at the endpoint in the pencil. -/
theorem omitted_factor_reduction (H L : K[X]) (u a : K)
    (root : (H+C a*L).eval u=0) {T : K[X]} (d : T∣X*(H+C a*L)) (uNe : T.eval u≠0) :
    ∃ e : ℕ, e≤1 ∧ ∃ V : K[X], V≠0 ∧ T=X^e*V ∧ V.eval u≠0 ∧ V∣omittedDifference H L u := by
  by_cases iz : T.eval 0=0
  · have f : X-C (0:K)∣T := dvd_iff_isRoot.mpr iz
    rw [map_zero,sub_zero] at f
    obtain ⟨V,e⟩ := f
    have hn : V.eval u≠0 := by
      intro eq
      apply uNe
      rw [e,eval_mul,eq,mul_zero]
    have d' : V∣H+C a*L := by
      obtain ⟨Q,eq⟩ := d
      refine ⟨Q,mul_left_cancel₀ X_ne_zero ?_⟩
      rw [eq,e]
      ring
    refine ⟨1,le_rfl,V,fun z=>hn (by simp [z]),?_,hn,omitted_factor_no_endpoint H L u a root d' hn⟩
    simpa only [pow_one] using e
  · have c : IsCoprime T (X:K[X]) := by
      simpa only [map_zero,sub_zero] using linear_factor_coprime_of_eval_ne iz
    have tn : T≠0 := fun z=>uNe (by simp [z])
    exact ⟨0,by decide,T,tn,by rw [pow_zero,one_mul],uNe,
      omitted_factor_no_endpoint H L u a root (c.dvd_of_dvd_mul_left d) uNe⟩

theorem omittedDifference_degree (H L : K[X]) (u : K) {n : ℕ}
    (dH : H.natDegree=n+1) (dL : L.natDegree≤n) (ne : L.eval u≠0) :
    (omittedDifference H L u).natDegree=n := by
  let P := C (L.eval u)*H-C (H.eval u)*L
  have p : P.natDegree=n+1 := by
    have e : (C (L.eval u)*H).natDegree=n+1 := by rw [natDegree_C_mul ne,dH]
    have lt : (C (H.eval u)*L).natDegree<(C (L.eval u)*H).natDegree :=
      ((natDegree_C_mul_le _ _).trans dL).trans_lt (e ▸ Nat.lt_succ_self n)
    exact (natDegree_sub_eq_left_of_natDegree_lt lt).trans e
  change (P /ₘ (X-C u)).natDegree=n
  rw [natDegree_divByMonic P (monic_X_sub_C u),natDegree_X_sub_C,p]
  rfl

theorem paidMoment_remove_origin (V : K[X]) (u : K) (j e : ℕ) :
    paidMoment (X^e*V) u j=paidMoment V u (j+e) := by
  unfold paidMoment
  rw [←mul_assoc,←pow_add]

end
end RKCert.FixedPolynomial
