module

public import RKCert.GradeSeparation
public import RKCert.GradedProducts
public import Mathlib.Algebra.Polynomial.OfFn
public import Mathlib.Algebra.Polynomial.Roots
public import Mathlib.Algebra.Polynomial.Derivative
public import Mathlib.Algebra.Polynomial.Eval.SMul

@[expose] public section

/-! # Polynomial profiles and residual calculus independent of an output row

After chronology-preserving compression the lower-grade stage columns
are retained but the original output order need not survive. These
lemmas use only characteristic zero and actual normalized tree weights.
-/
namespace RKCert.Paired
open Polynomial
open Module

variable {K : Type*} [Field K] [CharZero K] {s : ℕ}

theorem mat_zeroSpace_charZero (A : Fin s → Fin s → K) (n : ℕ) :
    zeroSpace A n ≤ (zeroSpace A (n+1)).comap (mat A) := by
  apply Submodule.span_le.mpr
  rintro _ ⟨t,u,he,ht,rfl⟩
  change mat A (normTree A t - normTree A u) ∈ zeroSpace A (n+1)
  have hgen := normDiff_mem (n:=n+1) A (t.attach .leaf) (u.attach .leaf)
    (by simp only [Tree.order,he]) (by change t.order+1≤n+1+1; omega)
  rw [normTree_unary, normTree_unary, ← he, ← smul_sub, ← map_sub] at hgen
  have hn : (t.order:K)≠0 := Nat.cast_ne_zero.mpr t.order_pos.ne'
  simpa only [smul_smul, inv_mul_cancel₀ hn, one_smul] using
    (zeroSpace A (n+1)).smul_mem (t.order:K)⁻¹ hgen

/-- Evaluate a polynomial at every actual tableau node. -/
def evalNodes (A : Fin s → Fin s → K) (P : Polynomial K) : Vec K s :=
  fun i => P.eval (nodes A i)

omit [CharZero K] in
@[simp] theorem evalNodes_apply (A : Fin s → Fin s → K) (P : Polynomial K) (i : Fin s) :
    evalNodes A P i = P.eval (nodes A i) := rfl

omit [CharZero K] in
@[simp] theorem evalNodes_X (A : Fin s → Fin s → K) : evalNodes A X = nodes A := by
  ext i; simp

omit [CharZero K] in
theorem evalNodes_eq_polyEval (A : Fin s → Fin s → K) (P : Polynomial K) {q : ℕ}
    (hP : P.natDegree≤q) : evalNodes A P = polyEval A q (fun j => P.coeff j.val) := by
  ext i
  rw [evalNodes_apply,Polynomial.eval_eq_sum_range' (n:=q+1) (by omega),Finset.sum_range,
    polyEval_apply]
  simp only [Finset.sum_apply,Pi.smul_apply,normTree_bush,smul_eq_mul]

omit [CharZero K] in
theorem evalNodes_ofFn [DecidableEq K] (A : Fin s → Fin s → K) (q : ℕ) (a : Fin (q+1) → K) :
    evalNodes A (Polynomial.ofFn (q+1) a) = polyEval A q a := by
  classical
  have hd : (Polynomial.ofFn (q+1) a).natDegree≤q := by
    have := Polynomial.ofFn_natDegree_lt (by omega : 1≤q+1) a
    omega
  rw [evalNodes_eq_polyEval A _ hd]
  have he : (fun j : Fin (q+1) => (Polynomial.ofFn (q+1) a).coeff j.val) = a :=
    funext fun j => Polynomial.ofFn_coeff_eq_val_of_lt a j.isLt
  rw [he]

omit [CharZero K] in
theorem evalNodes_mem_treeSpace (A : Fin s → Fin s → K) (P : Polynomial K) {q : ℕ}
    (hP : P.natDegree≤q) : evalNodes A P ∈ treeSpace A q := by
  rw [evalNodes_eq_polyEval A P hP]
  exact polyEval_mem_treeSpace _ _ _

/-- Through the given grade, no nonzero scalar profile evaluates to a pure defect. -/
def Separated (A : Fin s → Fin s → K) (q : ℕ) : Prop :=
  ∀ P : Polynomial K, P.natDegree≤q → evalNodes A P ∈ zeroSpace A q → P=0

omit [CharZero K] in
theorem Separated.mono {A : Fin s → Fin s → K} {q r : ℕ}
    (h : Separated A q) (hr : r≤q) : Separated A r :=
  fun P hp hv => h P (hp.trans hr) (zeroSpace_mono A hr hv)

omit [CharZero K] in
theorem separated_iff_coeff (A : Fin s → Fin s → K) (q : ℕ) :
    Separated A q ↔ ∀ a, polyEval A q a ∈ zeroSpace A q → a=0 := by
  classical
  constructor
  · intro h a ha
    have hP : (Polynomial.ofFn (q+1) a).natDegree≤q := by
      have h := Polynomial.ofFn_natDegree_lt (by omega : 1 ≤ q+1) a
      omega
    have hz := h _ hP (evalNodes_ofFn A q a ▸ ha)
    exact Polynomial.injective_ofFn (q+1) (hz.trans (Polynomial.ofFn_zero _).symm)
  · intro h P hp hP
    rw [evalNodes_eq_polyEval A P hp] at hP
    have hcoe := h _ hP
    ext k
    by_cases hk : k < q+1
    · exact congrFun hcoe ⟨k,hk⟩
    · simpa using Polynomial.coeff_eq_zero_of_natDegree_lt (show P.natDegree<k by omega)

omit [CharZero K] in
theorem explicit_separated {A : Fin s → Fin s → K} {b : Vec K s} {p q : ℕ}
    (ha : StrictLower A) (ho : HasTreeOrderAtLeast A b p) (hp : 2*q≤p) (hs : 0<s) :
    Separated A q := (separated_iff_coeff A q).mpr (explicit_poly_separated ha ho hp hs)

omit [CharZero K] in
theorem nodes_not_zeroSpace {A : Fin s → Fin s → K} {q : ℕ}
    (h : Separated A q) (hq : 1≤q) : nodes A ∉ zeroSpace A q := by
  intro hc
  have hX : (X : Polynomial K) = 0 := h X (by simpa using hq) (by simpa using hc)
  exact X_ne_zero hX

theorem zeroSpace_strict_of_separated {A : Fin s → Fin s → K} {q j : ℕ}
    (ha : StrictLower A) (hsep : Separated A q) (hj : 1≤j) (hjq : j+1≤q) :
    zeroSpace A j < zeroSpace A (j+1) := by
  refine lt_of_le_of_ne (zeroSpace_mono A (by omega)) ?_
  intro he
  apply nodes_not_zeroSpace hsep (by omega)
  apply zeroSpace_mono A (show j+1≤q from hjq)
  rw [← he]
  have hh : diag (nodes A) (1 : Vec K s) = nodes A := by ext i; simp
  rw [← hh]
  apply mem_of_invariant_seed (Equiv.refl _) (mat A) (causal_mat ha) (nodes A) 1
    (zeroSpace A j)
  · intro v hv
    rw [he]
    exact mat_zeroSpace_charZero A j hv
  · intro v hv
    rw [he]
    exact diag_zeroSpace A j hv
  · rw [he]
    exact zeroSpace_mono A (by omega : 2≤j+1) (forward_seed_mem A)

theorem exists_poly_zeroSpace_charZero (A : Fin s → Fin s → K) {q : ℕ}
    {v : Vec K s} (hv : v∈treeSpace A q) :
    ∃ P : Polynomial K, P.natDegree≤q ∧ v-evalNodes A P ∈ zeroSpace A q := by
  induction hv using Submodule.span_induction with
  | mem v hg =>
    obtain ⟨t,ht,rfl⟩ := hg
    have hpos := t.order_pos
    let r := (t.childDensityProduct:K)⁻¹
    have hr : r • normTree A t = stageWeight A t := by
      have hn : (t.childDensityProduct:K) ≠ 0 := Nat.cast_ne_zero.mpr t.childDensityProduct_pos.ne'
      simp [r,normTree,smul_smul,inv_mul_cancel₀ hn]
    refine ⟨C r * X^(t.order-1), ?_, ?_⟩
    · exact (Polynomial.natDegree_C_mul_le _ _).trans (by simpa using (show t.order-1≤q by omega))
    · have ht' : (Tree.bush (t.order-1)).order=t.order := by rw [Tree.order_bush]; omega
      have h := (zeroSpace A q).smul_mem r (normDiff_mem A t _ ht'.symm ht)
      have he : evalNodes A (C r * X^(t.order-1)) =
          r • normTree A (Tree.bush (t.order-1)) := by ext i; simp [normTree_bush]
      rwa [smul_sub,hr,← he] at h
  | zero =>
    refine ⟨0,by simp,?_⟩
    have h : evalNodes A (0 : Polynomial K)=0 := by ext i; simp
    rw [h,sub_zero]; exact (zeroSpace A q).zero_mem
  | add x y _ _ hx hy =>
    obtain ⟨P,hdP,hP⟩ := hx
    obtain ⟨Q,hdQ,hQ⟩ := hy
    refine ⟨P+Q,Polynomial.natDegree_add_le_of_degree_le hdP hdQ,?_⟩
    convert (zeroSpace A q).add_mem hP hQ using 1
    ext i; simp; ring
  | smul a x _ hx =>
    obtain ⟨P,hd,hP⟩ := hx
    refine ⟨C a * P,(Polynomial.natDegree_C_mul_le _ _).trans hd,?_⟩
    convert (zeroSpace A q).smul_mem a hP using 1
    ext i; simp [mul_sub]

/-- Algebraic primitive with zero integration constant. -/
noncomputable def primitive : Polynomial K →ₗ[K] Polynomial K where
  toFun P := P.sum fun n a => monomial (n+1) (a / (n+1:ℕ))
  map_add' P Q := by
    apply Polynomial.sum_add_index <;> simp [add_div]
  map_smul' a P := by
    rw [Polynomial.sum_smul_index]
    · rw [Polynomial.smul_sum]
      apply Finset.sum_congr rfl
      intro n _
      change monomial (n+1) (a * P.coeff n / ((n+1:ℕ):K)) = a • monomial (n+1) (P.coeff n / ((n+1:ℕ):K))
      rw [Polynomial.smul_monomial,smul_eq_mul,mul_div_assoc]
    · intro n; simp

omit [CharZero K] in
theorem primitive_monomial (n : ℕ) (a : K) :
    primitive (monomial n a) = monomial (n+1) (a / (n+1:ℕ)) := by
  let f (m : ℕ) (x : K) : Polynomial K := monomial (m+1) (x / ((m+1:ℕ):K))
  change (monomial n a).sum f = f n a
  exact Polynomial.sum_monomial_index a f (by simp [f]) 

omit [CharZero K] in
theorem primitive_coeff_succ (P : Polynomial K) (n : ℕ) :
    (primitive P).coeff (n+1) = P.coeff n / (n+1:ℕ) := by
  change (∑ i ∈ P.support, monomial (i+1) (P.coeff i / (i+1:ℕ))).coeff (n+1) = _
  rw [finsetSum_coeff,Finset.sum_eq_single n]
  · simp
  · intro i _ hi
    simp [Polynomial.coeff_monomial,Ne.symm hi]
  · intro h
    simp [Polynomial.notMem_support_iff.mp h]

omit [CharZero K] in
theorem primitive_coeff_zero (P : Polynomial K) : (primitive P).coeff 0 = 0 := by
  change (∑ i ∈ P.support, monomial (i+1) (P.coeff i / (i+1:ℕ))).coeff 0 = _
  simp [Polynomial.coeff_monomial]

theorem primitive_derivative (P : Polynomial K) (hP : P.coeff 0=0) :
    primitive (derivative P) = P := by
  ext n
  cases n with
  | zero => rw [primitive_coeff_zero,hP]
  | succ n =>
    rw [primitive_coeff_succ,Polynomial.coeff_derivative]
    have hn : ((n+1:ℕ):K) ≠ 0 := Nat.cast_ne_zero.mpr (by omega)
    simpa only [Nat.cast_add,Nat.cast_one] using mul_div_cancel_right₀ (P.coeff (n+1)) hn

omit [CharZero K] in
theorem primitive_natDegree_le {P : Polynomial K} {q : ℕ} (hq : P.natDegree≤q) :
    (primitive P).natDegree≤q+1 := by
  rw [Polynomial.natDegree_le_iff_coeff_eq_zero]
  intro n hn
  cases n with
  | zero => omega
  | succ n => rw [primitive_coeff_succ,Polynomial.coeff_eq_zero_of_natDegree_lt (by omega),zero_div]

/-- Extension of a polynomial pair, with its exact defect grade. -/
theorem primitive_defect (A : Fin s → Fin s → K) (P : Polynomial K) {q : ℕ}
    (hP : P.natDegree≤q) :
    mat A (evalNodes A P) - evalNodes A (primitive P) ∈ zeroSpace A (q+1) := by
  have hm (k : ℕ) (hk : k≤q) (a : K) :
      mat A (evalNodes A (monomial k a)) - evalNodes A (primitive (monomial k a))
        ∈ zeroSpace A (q+1) := by
    have h := normDiff_mem (n:=q+1) A ((Tree.bush k).attach .leaf) (Tree.bush (k+1))
      (by simp only [Tree.order,Tree.order_bush]) (by simp only [Tree.order,Tree.order_bush]; omega)
    have hn : ((k+1:ℕ):K) ≠ 0 := Nat.cast_ne_zero.mpr (by omega)
    have h' := (zeroSpace A (q+1)).smul_mem (a / ((k+1:ℕ):K)) h
    rw [normTree_unary,Tree.order_bush,smul_sub,smul_smul,div_mul_cancel₀ _ hn] at h'
    have e1 : evalNodes A (monomial k a) = a • normTree A (Tree.bush k) := by
      ext i; simp [normTree_bush]
    have e2 : evalNodes A (primitive (monomial k a)) =
        (a / ((k+1:ℕ):K)) • normTree A (Tree.bush (k+1)) := by
      ext i; simp [primitive_monomial,normTree_bush]
    rwa [e1,e2,map_smul]
  let L : Polynomial K →ₗ[K] Vec K s := LinearMap.pi (fun i => Polynomial.leval (nodes A i))
  have hl (P : Polynomial K) : L P = evalNodes A P := rfl
  let D := (mat A).comp L - L.comp (primitive (K:=K))
  have hd (P : Polynomial K) : D P = mat A (evalNodes A P) - evalNodes A (primitive P) := rfl
  rw [← hd, Polynomial.as_sum_range' P (q+1) (by omega),map_sum]
  exact (zeroSpace A (q+1)).sum_mem (fun k hk => by rw [hd]; exact hm k (by simpa using hk) _)

end RKCert.Paired
