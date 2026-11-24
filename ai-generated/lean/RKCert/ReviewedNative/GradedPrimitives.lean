module

public import RKCert.ReviewedNative.GradedDefects
public import Mathlib.Algebra.Polynomial.Coeff
public import Mathlib.Algebra.Polynomial.Degree.Lemmas
public import Mathlib.Algebra.Polynomial.Derivative
public import Mathlib.Algebra.Polynomial.Eval.SMul

@[expose] public section

/-! # Polynomial primitives in the actual reviewed defect space -/
namespace RKResearch.Certified.Graded

open RKResearch FiniteRootedTree Polynomial
open scoped FiniteRootedTree Matrix

section Semiring
variable {ι R : Type*} [Fintype ι] [CommSemiring R]

/-- Polynomial evaluation at the actual stage clocks, as Mathlib linear maps. -/
noncomputable abbrev evalNodes (A : Matrix ι ι R) : R[X] →ₗ[R] (ι→R) :=
  LinearMap.pi (fun i => Polynomial.leval (nodes A i))

@[simp] theorem evalNodes_apply (A : Matrix ι ι R) (P:R[X]) (i:ι) :
    evalNodes A P i=P.eval (nodes A i) := rfl

theorem evalNodes_monomial (A : Matrix ι ι R) (n : ℕ) (a : R) :
    evalNodes A (monomial n a)=a•normTree A (clockTree n) := by
  rw [normTree_clockTree]
  ext i
  simp

theorem evalNodes_mem_treeSpace (A : Matrix ι ι R) (P : R[X]) {q : ℕ} (hp:P.natDegree≤q) :
    evalNodes A P∈treeSpace A q := by
  rw [P.as_sum_range' (q+1) (by omega),map_sum]
  apply (treeSpace A q).sum_mem
  intro n hn
  have hn':n<q+1 := Finset.mem_range.mp hn
  rw [evalNodes_monomial]
  apply (treeSpace A q).smul_mem
  apply (treeSpace A q).smul_mem
  exact Φ_mem_treeSpace A _ (by rw [order_clockTree];omega)

end Semiring

section Field
variable {K : Type*} [Field K]

/-- Primitive with zero constant, implemented through Mathlib's polynomial
linear sum on coefficient functionals. -/
noncomputable def primitive : K[X] →ₗ[K] K[X] :=
  Polynomial.lsum fun n => (monomial (n+1)) ∘ₗ LinearMap.mulLeft K (((n+1:ℕ):K)⁻¹)

@[simp] theorem primitive_monomial (n : ℕ) (a : K) :
    primitive (monomial n a)=monomial (n+1) (a/((n+1:ℕ):K)) := by
  rw [primitive,Polynomial.lsum_apply,Polynomial.sum_monomial_index]
  · simp [div_eq_mul_inv,mul_comm]
  · simp

@[simp] theorem primitive_coeff_zero (P:K[X]) : (primitive P).coeff 0=0 := by
  change (∑ n∈P.support,monomial (n+1) ((((n+1:ℕ):K))⁻¹*P.coeff n)).coeff 0=0
  simp [coeff_monomial]

@[simp] theorem primitive_coeff_succ (P:K[X]) (n:ℕ) :
    (primitive P).coeff (n+1)=P.coeff n/((n+1:ℕ):K) := by
  change (∑ i∈P.support,monomial (i+1) ((((i+1:ℕ):K))⁻¹*P.coeff i)).coeff (n+1)=_
  rw [finsetSum_coeff,Finset.sum_eq_single n]
  · simp [div_eq_mul_inv,mul_comm]
  · intro i _ hin; simp [coeff_monomial,Ne.symm hin]
  · intro hn; simp [Polynomial.notMem_support_iff.mp hn]

theorem primitive_derivative [CharZero K] (P:K[X]) (P0:P.coeff 0=0) :
    primitive P.derivative=P := by
  ext n
  cases n with
  | zero => rw [primitive_coeff_zero,P0]
  | succ n =>
    rw [primitive_coeff_succ,Polynomial.coeff_derivative]
    have h : ((n+1:ℕ):K)≠0 := Nat.cast_ne_zero.mpr (Nat.succ_ne_zero n)
    simpa only [Nat.cast_add,Nat.cast_one] using mul_div_cancel_right₀ (P.coeff (n+1)) h

theorem primitive_natDegree_le {P:K[X]} {q:ℕ} (hp:P.natDegree≤q) :
    (primitive P).natDegree≤q+1 := by
  rw [natDegree_le_iff_coeff_eq_zero]
  intro n hn
  cases n with
  | zero => simp
  | succ n =>
    rw [primitive_coeff_succ,coeff_eq_zero_of_natDegree_lt (by omega),zero_div]

variable {ι : Type*} [Fintype ι] {A : Matrix ι ι K} {b : ι→K} {p : ℕ}

theorem primitive_defect [CharZero K] (A : Matrix ι ι K) (P:K[X]) {q:ℕ}
    (hp:P.natDegree≤q) :
    mat A (evalNodes A P)-evalNodes A (primitive P)∈zeroSpace A (q+1) := by
  let D : K[X] →ₗ[K] (ι→K) := (mat A).comp (evalNodes A)-(evalNodes A).comp primitive
  have mono (n:ℕ) (hn:n≤q) (a:K) :
      D (monomial n a)∈zeroSpace A (q+1) := by
    have unit : ((n+1:ℕ):K)≠0 := Nat.cast_ne_zero.mpr (Nat.succ_ne_zero n)
    have h : ((n+1:ℕ):K) • mat A (fun i=>(nodes A i)^n) -
      (fun i=>(nodes A i)^(n+1))∈zeroSpace A (n+1) := monomialStageDefect_mem A n
    have old := (zeroSpace A (n+1)).smul_mem (a/((n+1:ℕ):K)) h
    rw [smul_sub,smul_smul,div_mul_cancel₀ _ unit] at old
    apply zeroSpace_mono A (by omega : n+1≤q+1)
    change (mat A) (evalNodes A (monomial n a))-evalNodes A (primitive (monomial n a))∈_
    rw [primitive_monomial,evalNodes_monomial,evalNodes_monomial,map_smul,normTree_clockTree,normTree_clockTree]
    exact old
  change D P∈_
  rw [P.as_sum_range' (q+1) (by omega),map_sum]
  exact (zeroSpace A (q+1)).sum_mem (fun n hn=>mono n (by have :=Finset.mem_range.mp hn;omega) _)

theorem probe_evalNodes (ho:HasOrder p A b) (P:K[X]) (k:ℕ) (hp:k+P.natDegree+1≤p) :
    probe A b k (evalNodes A P)=(primitive (X^k*P)).eval 1 := by
  let F := (probe A b k).comp (evalNodes A)
  let J := (Polynomial.leval 1).comp (primitive.comp (LinearMap.mulLeft K (X^k:K[X])))
  let q := P.natDegree
  have hmono (n:ℕ) (hn:n≤q) (a:K) : F (monomial n a)=J (monomial n a) := by
    change probe A b k (evalNodes A (monomial n a))=(primitive (X^k*monomial n a)).eval 1
    rw [evalNodes_monomial,map_smul,smul_eq_mul,X_pow_mul_monomial,primitive_monomial,eval_monomial,
      one_pow,mul_one]
    have h : ((n+k+1:ℕ):K) * probe A b k (normTree A (clockTree n)) = 1 := by
      simpa only [normTree_clockTree, probe, row_apply, dotProduct, Pi.pow_apply,
        Nat.add_comm n k, pow_add, mul_assoc] using ho.hasQuadratureOrder (n+k) (by omega)
    have nz := (IsUnit.of_mul_eq_one _ h).ne_zero
    apply (eq_div_iff nz).mpr
    rw [mul_assoc,mul_comm (probe A b k (normTree A (clockTree n))),h,mul_one]
  change F P=J P
  rw [P.as_sum_range' (q+1) (by dsimp [q];omega),map_sum,map_sum]
  exact Finset.sum_congr rfl fun n hn=>hmono n (by have :=Finset.mem_range.mp hn;omega) _

end Field
end RKResearch.Certified.Graded
