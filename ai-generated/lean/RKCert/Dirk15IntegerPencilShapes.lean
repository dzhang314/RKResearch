module

public import RKCert.Dirk15IntegerJacobi
public import RKCert.PencilDividedDifference

@[expose] public section

/-! # Actual pencil factors and removal of at most one physical endpoint -/
namespace RKCert.FixedPolynomial
open Polynomial RKCert.Paired RKCert.Paired.Signature
open scoped Classical
noncomputable section
variable {K : Type*} [Field K] [CharZero K]

abbrev fieldPencil (K : Type*) [Field K] (n : ℕ) (a : K) : K[X] :=
  fieldJacobi K (n+1)+C a*fieldJacobi K n

theorem fieldPencil_degree (n : ℕ) (a : K) : (fieldPencil K n a).natDegree=n+1 := by
  have d : (C a*fieldJacobi K n).natDegree≤n :=
    (natDegree_C_mul_le _ _).trans (fieldJacobi_degree n).le
  exact (natDegree_add_eq_left_of_natDegree_lt (d.trans_lt
    (by rw [fieldJacobi_degree]; omega))).trans (fieldJacobi_degree _)

theorem integer_pencil_shape {D : K[X]} (shape : Order15PencilShape D) :
    ∃ n : ℕ, (n=5 ∨ n=6) ∧ ∃ a t : K,a≠0 ∧ D=C a*(X*fieldPencil K n t) := by
  obtain ⟨v,v0,J6⟩ := fieldJacobi_scale (K:=K) 6
  rcases shape with ⟨a,a0,e⟩|⟨a,t,a0,e⟩
  · refine ⟨5,Or.inl rfl,a/v,0,div_ne_zero a0 v0,?_⟩
    change D=C (a/v)*(X*(fieldJacobi K 6+C (0:K)*fieldJacobi K 5))
    rw [e,J6,map_zero,zero_mul,add_zero]
    have he : C (a/v)*C v=C a := by rw [←map_mul,div_mul_cancel₀ _ v0]
    calc
      _ = (C (a/v)*C v)*(X*jacobiTwo K 6) := by rw [he]
      _ = _ := by ring
  · obtain ⟨w,w0,J7⟩ := fieldJacobi_scale (K:=K) 7
    refine ⟨6,Or.inr rfl,a/w,(w*t)/v,div_ne_zero a0 w0,?_⟩
    change D=C (a/w)*(X*(fieldJacobi K 7+C ((w*t)/v)*fieldJacobi K 6))
    rw [e,J7,J6]
    have h1 : C (a/w)*C w=C a := by rw [←map_mul,div_mul_cancel₀ _ w0]
    have h2 : C ((w*t)/v)*C v=C w*C t := by
      rw [←map_mul,div_mul_cancel₀ _ v0,map_mul]
    calc
      _ = (C (a/w)*C w)*(X*(jacobiTwo K 7+C t*jacobiTwo K 6)) := by rw [h1]
      _ = _ := by rw [←mul_assoc (C ((w*t)/v)),h2]; ring

omit [CharZero K] in
theorem factor_remove_one_endpoint {T E : K[X]} (T0 : T≠0) (dvd : T∣X*E) :
    ∃ e : ℕ, e≤1 ∧ ∃ V : K[X],V≠0 ∧ T=X^e*V ∧ V∣E ∧
      (T.eval 0≠0 → e=0) := by
  by_cases t0 : T.eval 0=0
  · have dvd0 : X-C (0:K)∣T := dvd_iff_isRoot.mpr t0
    rw [map_zero,sub_zero] at dvd0
    obtain ⟨V,h⟩ := dvd0
    have vn : V≠0 := fun v => T0 (by rw [h,v,mul_zero])
    obtain ⟨Q,hQ⟩ := dvd
    have e : V*Q=E := by
      apply mul_left_cancel₀ (X_ne_zero (R:=K))
      rw [←mul_assoc,←h,←hQ]
    exact ⟨1,le_rfl,V,vn,by simpa only [pow_one] using h,⟨Q,e.symm⟩,fun ne=>False.elim (ne t0)⟩
  · have h : IsCoprime T (X:K[X]) := by
      simpa only [map_zero,sub_zero] using linear_factor_coprime_of_eval_ne t0
    exact ⟨0,by decide,T,T0,by rw [pow_zero,one_mul],h.dvd_of_dvd_mul_left dvd,fun _=>rfl⟩

omit [CharZero K] in
theorem cancel_nonzero_constant_factor {T Q : K[X]} {a : K} (a0 : a≠0)
    (d : T∣C a*Q) : T∣Q := by
  obtain ⟨R,h⟩ := d
  have u : C a⁻¹*C a=1 := by rw [←map_mul,inv_mul_cancel₀ a0,map_one]
  refine ⟨C a⁻¹*R,?_⟩
  calc
    Q=(C a⁻¹*C a)*Q := by rw [u,one_mul]
    _ = C a⁻¹*(C a*Q) := by ring
    _ = _ := by rw [h]; ring

omit [CharZero K] in
theorem reflectPolynomial_eval_exact (T : K[X]) (u : K) :
    (reflectPolynomial T).eval u=T.eval (1-u) := by
  rw [reflectPolynomial,eval_comp,eval_sub,eval_one,eval_X]

omit [CharZero K] in
theorem reflectPolynomial_degree_eq (T : K[X]) :
    (reflectPolynomial T).natDegree=T.natDegree := by
  apply le_antisymm (reflectPolynomial_degree _)
  have e := reflectPolynomial_degree (reflectPolynomial T)
  rwa [reflectPolynomial_involutive] at e

omit [CharZero K] in
theorem reflectPolynomial_mul_exact (T S : K[X]) :
    reflectPolynomial (T*S)=reflectPolynomial T*reflectPolynomial S := by
  exact mul_comp _ _ _

omit [CharZero K] in
theorem reflectPolynomial_endpoint (e : ℕ) (T : K[X]) :
    reflectPolynomial (X^e*T)=(1-X)^e*reflectPolynomial T := by
  unfold reflectPolynomial
  rw [mul_comp,pow_comp,X_comp]

theorem factor_reflected_pencil {V : K[X]} (n : ℕ) (a : K)
    (dvd : V∣fieldPencil K n a) :
    reflectPolynomial V∣fieldPencil K n (-a) := by
  obtain ⟨R,e⟩ := dvd
  apply cancel_nonzero_constant_factor (pow_ne_zero (n+1) (neg_ne_zero.mpr one_ne_zero))
  rw [←fieldJacobi_pencil_reflect n a]
  change reflectPolynomial V∣reflectPolynomial (fieldPencil K n a)
  rw [e,reflectPolynomial_mul_exact]
  exact dvd_mul_right _ _

omit [CharZero K] in
theorem factor_degree_one_endpoint {T V : K[X]} (V0 : V≠0) (e : ℕ) (eq : T=X^e*V) :
    T.natDegree=e+V.natDegree := by
  rw [eq,natDegree_mul (pow_ne_zero e X_ne_zero) V0,natDegree_X_pow]

omit [CharZero K] in
theorem factor_omit_eval {T V : K[X]} (e : ℕ) (eq : T=X^e*V) {u : K}
    (h : T.eval u≠0) : V.eval u≠0 := by
  intro he
  exact h (by rw [eq,eval_mul,he,mul_zero])

end
end RKCert.FixedPolynomial
