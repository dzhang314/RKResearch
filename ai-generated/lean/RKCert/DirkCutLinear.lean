module

public import RKCert.DirkDirtyWitness

@[expose] public section

/-! # Field-algebraic identities for exact prefix taps -/

namespace RKCert.Paired
open RKCert.Endpoint Polynomial
open scoped Classical

variable {K : Type*} [Field K] {s : ℕ}
variable {B : Matrix (Fin s) (Fin s) K} {c v : Vec K s}

abbrev LowerArray (B : Fin s → Fin s → K) : Prop :=
  ∀ i j : Fin s, i.val<j.val → B i j=0

def commutatorMatrix (B : Matrix (Fin s) (Fin s) K) (c : Vec K s) :
    Matrix (Fin s) (Fin s) K :=
  Matrix.diagonal c*B - B*Matrix.diagonal c - B*B

theorem commutatorMatrix_apply (B : Matrix (Fin s) (Fin s) K) (c : Vec K s)
    (i j : Fin s) :
    commutatorMatrix B c i j = (c i-c j)*B i j-∑ k, B i k*B k j := by
  rw [commutatorMatrix,Matrix.sub_apply,Matrix.sub_apply,Matrix.diagonal_mul,Matrix.mul_diagonal,
    Matrix.mul_apply]
  ring

theorem mat_commutatorMatrix (B : Matrix (Fin s) (Fin s) K) (c : Vec K s) :
    mat (commutatorMatrix B c) = commutatorR (mat B) (diag c) := by
  have h : Matrix.toLin' (Matrix.diagonal c) = diag c := by
    exact LinearMap.ext (fun v => funext (Matrix.mulVec_diagonal c v))
  change Matrix.toLin' (commutatorMatrix B c)=_
  simp only [commutatorMatrix,map_sub,Matrix.toLin'_mul,h,commutatorR]
  rfl

theorem commutatorMatrix_lower (ha : LowerArray B) : LowerArray (commutatorMatrix B c) := by
  intro i j h
  rw [commutatorMatrix_apply,ha _ _ h,mul_zero,zero_sub,neg_eq_zero]
  apply Finset.sum_eq_zero
  intro k _
  by_cases hi : i < k
  · rw [ha _ _ hi,zero_mul]
  · rw [ha _ _ ((le_of_not_gt hi).trans_lt h),mul_zero]

theorem commutatorMatrix_zero_col {j : Fin s} (hz : ∀ i, B i j=0) (i : Fin s) :
    commutatorMatrix B c i j=0 := by
  simp [commutatorMatrix_apply,hz]

theorem commutatorMatrix_zero_row {i : Fin s} (hz : ∀ j, B i j=0) (j : Fin s) :
    commutatorMatrix B c i j=0 := by
  simp [commutatorMatrix_apply,hz]

theorem commutatorMatrix_diagonal {i : Fin s} (ha : LowerArray B) :
    commutatorMatrix B c i i=-(B i i)^2 := by
  rw [commutatorMatrix_apply,sub_self,zero_mul,zero_sub,pow_two]
  congr 1
  apply Finset.sum_eq_single i
  · intro k _ hn
    rcases lt_or_gt_of_ne hn with hh|hh
    · rw [ha _ _ hh,mul_zero]
    · rw [ha _ _ hh,zero_mul]
  · simp

theorem commutatorMatrix_offdiag {i j : Fin s} (ha : LowerArray B)
    (hi : B i i=0) (hj : B j j=0)
    (h : ∀ k : Fin s, j < k → k < i → B i k=0 ∨ B k j=0) :
    commutatorMatrix B c i j=(c i-c j)*B i j := by
  rw [commutatorMatrix_apply]
  have hs : (∑ k, B i k*B k j)=0 := by
    apply Finset.sum_eq_zero
    intro k _
    by_cases hki : k < i
    · by_cases hjk : j < k
      · rcases h k hjk hki with he|he
        · rw [he,zero_mul]
        · rw [he,mul_zero]
      · rcases lt_or_eq_of_le (le_of_not_gt hjk) with hlt|rfl
        · rw [ha _ _ hlt,mul_zero]
        · rw [hj,mul_zero]
    · rcases lt_or_eq_of_le (le_of_not_gt hki) with hlt|rfl
      · rw [ha _ _ hlt,zero_mul]
      · rw [hi,zero_mul]
  rw [hs,sub_zero]

theorem row_restrict_sum (B : Matrix (Fin s) (Fin s) K) (i : Fin s) (v : Vec K s)
    (S : Finset (Fin s)) (hS : ∀ j∉S, B i j=0 ∨ v j=0) :
    mat B v i=∑ j∈S, B i j*v j := by
  change (∑ j : Fin s, B i j*v j) = _
  symm
  apply Finset.sum_subset (Finset.subset_univ _)
  intro j _ hj
  rcases hS j hj with h|h
  · rw [h,zero_mul]
  · rw [h,mul_zero]

theorem row_single_tap (B : Matrix (Fin s) (Fin s) K) (i j : Fin s) (v : Vec K s)
    (h : ∀ k ≠ j, B i k=0 ∨ v k=0) :
    mat B v i=B i j*v j := by
  rw [row_restrict_sum B i v {j} (fun k hk => h k (by simpa using hk))]
  simp

theorem row_zero_from_taps (B : Matrix (Fin s) (Fin s) K) (i : Fin s) (v : Vec K s)
    (h : ∀ j, B i j=0 ∨ v j=0) :
    mat B v i=0 := by
  rw [row_restrict_sum B i v ∅ (fun j _ => h j),Finset.sum_empty]

/-- Exact interpolation of a set of row values; the statement includes
the empty set, so it is safe for the first physical receiver. -/
theorem exists_polynomial_interpolate {ι : Type*} (S : Finset ι) (nodes : ι → K)
    (hinj : Set.InjOn nodes S) (f : ι → K) {d : ℕ} (h : S.card≤d+1) :
    ∃ P : K[X], P.natDegree≤d ∧ ∀ z∈S, P.eval (nodes z)=f z := by
  let Q := Lagrange.interpolate S nodes f
  refine ⟨Q,?_,fun z hz => Lagrange.eval_interpolate_at_node f hinj hz⟩
  by_cases he : Q=0
  · simp [he]
  have hdegree := (natDegree_lt_iff_degree_lt he).mpr (Lagrange.degree_interpolate_lt f hinj)
  omega

/-- A row annihilating all low powers on at most d+1 distinct donors
has zero taps there, even if the row is not represented by output weights. -/
theorem vanish_taps {ι : Type*} (S : Finset ι) (nodes coeff : ι → K)
    (hinj : Set.InjOn nodes S) {d : ℕ} (hS : S.card≤d+1)
    (h : ∀ Q : K[X], Q.natDegree≤d → ∑ j∈S, coeff j*Q.eval (nodes j)=0) :
    ∀ j∈S, coeff j=0 := by
  intro j hj
  let f : ι → K := fun k => if k=j then 1 else 0
  obtain ⟨Q,hQ,ee⟩ := exists_polynomial_interpolate S nodes hinj f hS
  have hz := h Q hQ
  rw [Finset.sum_eq_single_of_mem j hj] at hz
  · simpa [ee j hj,f] using hz
  · intro k hk hne
    rw [ee k hk]
    simp [f,hne]

variable [CharZero K]

theorem primitive_X_eval (u : K) : (formalPrimitive X).eval u = u^2/2 := by
  rw [show (X:K[X])=monomial 1 1 by simpa only [pow_one] using (monomial_one_right_eq_X_pow (R:=K) 1).symm,formalPrimitive_eq_treePrimitive,primitive_monomial,
    eval_monomial]
  norm_num
  ring

theorem primitive_X_sq_eval (u : K) : (formalPrimitive (X^2)).eval u = u^3/3 := by
  rw [←monomial_one_right_eq_X_pow,formalPrimitive_eq_treePrimitive,primitive_monomial,
    eval_monomial]
  norm_num
  ring

/-- Two nonzero distinct clean pivots cannot each kill the first two
primitives of xP. The second primitive has three roots at 0 and two each
at u and v, a total of seven against degree at most six. -/
theorem two_clean_primitive_impossible (P : K[X]) (hP : P≠0) (hd : P.natDegree≤3)
    (u v : K) (hu : u≠0) (hv : v≠0) (hne : u≠v)
    (hu1 : (formalPrimitive (X*P)).eval u=0)
    (hu2 : (formalPrimitive (X*(X*P))).eval u=0)
    (hv1 : (formalPrimitive (X*P)).eval v=0)
    (hv2 : (formalPrimitive (X*(X*P))).eval v=0) : False := by
  let F := formalPrimitive (formalPrimitive (X*P))
  have hF : F≠0 := by
    intro hzero
    have he := congrArg (fun Q : K[X] => Q.derivative.derivative) hzero
    simp [F,hP,X_ne_zero] at he
  have hdF : F.natDegree≤6 := by
    have h := natDegree_mul_le (p:=(X:K[X])) (q:=P)
    rw [natDegree_X] at h
    have h1 := natDegree_formalPrimitive_le (X*P)
    have h2 := natDegree_formalPrimitive_le (formalPrimitive (X*P))
    dsimp [F]
    omega
  have atRoot (a : K) (ha : (formalPrimitive (X*P)).eval a=0)
      (hb : (formalPrimitive (X*(X*P))).eval a=0) : (X-C a)^2∣F := by
    apply (le_rootMultiplicity_iff hF).mp
    apply (one_lt_rootMultiplicity_iff_isRoot hF).mpr
    constructor
    · have hh := congrArg (Polynomial.eval a) (primitive_commutation (X*P))
      simpa [ha,hb,F,IsRoot.def] using hh
    · simpa [F,IsRoot.def] using ha
  have atZero : X^3∣F := by
    suffices hh : (X-C (0:K))^3∣F from by simpa using hh
    apply (le_rootMultiplicity_iff hF).mp
    apply lt_rootMultiplicity_of_isRoot_iterate_derivative hF
    intro n hn
    rcases (show n=0 ∨ n=1 ∨ n=2 by omega) with rfl|rfl|rfl
    · simp [F,IsRoot.def]
    · simp [F,IsRoot.def]
    · simp [F,IsRoot.def,Function.iterate_succ_apply']
  have cop (a b : K) (h : a≠b) : IsCoprime (X-C a) (X-C b) :=
    isCoprime_X_sub_C_of_isUnit_sub (sub_ne_zero.mpr h).isUnit
  have hX (a : K) (h : a≠0) : IsCoprime (X:K[X]) (X-C a) := by
    simpa using cop 0 a h.symm
  have r := ((hX u hu).pow).mul_dvd atZero (atRoot u hu1 hu2)
  have hh := ((hX v hv).pow.mul_left (cop u v hne).pow).mul_dvd r (atRoot v hv1 hv2)
  have hdeg : (X^3*(X-C u)^2*(X-C v)^2 : K[X]).natDegree=7 := by
    have a : (X-C u) ≠ 0 := (monic_X_sub_C u).ne_zero
    have b : (X-C v) ≠ 0 := (monic_X_sub_C v).ne_zero
    rw [natDegree_mul (mul_ne_zero (pow_ne_zero _ X_ne_zero) (pow_ne_zero _ a)) (pow_ne_zero _ b),
      natDegree_mul (pow_ne_zero _ X_ne_zero) (pow_ne_zero _ a),natDegree_pow,
      natDegree_pow,natDegree_pow,natDegree_X,natDegree_X_sub_C,natDegree_X_sub_C]
  exact hF (eq_zero_of_dvd_of_natDegree_lt hh (by omega))

/-- A second clean receiver cannot integrate every f that starts at zero
and already obeys its previous receptor's primitive constraints, because
one can make f(v)=0 while leaving Jf(v) nonzero. -/
theorem second_clean_test (u v : K) (hv : v≠0) (hvu : v≠u) :
    ∃ f : K[X], f.natDegree≤5 ∧ f.eval 0=0 ∧ f.eval u=0 ∧
      (formalPrimitive f).eval u=0 ∧ f.eval v=0 ∧ (formalPrimitive f).eval v≠0 := by
  let H : K[X] := X^2*(X-C u)^2
  have hH : H.eval v≠0 := by
    simp [H,hv,sub_ne_zero.mpr hvu]
  let k := -H.derivative.eval v/H.eval v
  let V : K[X] := 1+C k*(X-C v)
  let G := H*V
  have hdegG : G.natDegree≤5 := by
    have h1 := natDegree_mul_le (p:=H) (q:=V)
    have h2 := natDegree_mul_le (p:=(X^2:K[X])) (q:=(X-C u)^2)
    rw [natDegree_pow,natDegree_X,natDegree_pow,natDegree_X_sub_C] at h2
    change H.natDegree≤4 at h2
    have h3 := natDegree_add_le (p:=(1:K[X])) (q:=C k*(X-C v))
    have h4 := natDegree_C_mul_le k (X-C v)
    rw [natDegree_X_sub_C] at h4
    simp only [natDegree_one] at h3
    dsimp only [G,V] at *
    omega
  have jG : formalPrimitive G.derivative = G := by
    apply eq_of_derivative_and_eval_zero
    · simp
    · simp [G,H]
  refine ⟨G.derivative,by have := natDegree_derivative_le G; omega,?_,?_,?_,?_,?_⟩
  · simp [G,H,derivative_mul,derivative_pow]
  · simp [G,H,derivative_mul,derivative_pow]
  · rw [jG]
    simp [G,H]
  · simp only [G,V,derivative_mul,derivative_add,derivative_one,derivative_sub,derivative_X,
      derivative_C,sub_zero,zero_mul,mul_one,zero_add,eval_add,eval_mul,eval_one,
      eval_C,eval_sub,eval_X,sub_self,mul_zero,add_zero,k]
    field_simp
    ring
  · rw [jG]
    simpa [G,V] using hH

end RKCert.Paired
