module

public import RKCert.ReviewedNative.DIRK12MidpointPolynomialPrimitive
import Mathlib.Algebra.Polynomial.Degree.Lemmas
import Mathlib.Algebra.Polynomial.Monic
import Mathlib.Tactic.Ring

@[expose] public section

/-! Scalar polynomial reads on actual coordinate vectors, with an
explicit degree budget and no dimension hypothesis. -/
namespace RKResearch.Certified.DIRK12MidpointProbes.Vector

open RKResearch Graded Polynomial
open scoped BigOperators Polynomial Matrix

variable {ι K : Type*} [Field K]

noncomputable def evalVector (c : ι → K) : K[X] →ₗ[K] (ι → K) where
  toFun p i := p.eval (c i)
  map_add' p q := by ext i; simp
  map_smul' r p := by
    ext i
    simp [Polynomial.smul_eq_C_mul]

@[simp] theorem at_apply (c : ι → K) (p : K[X]) (i : ι) :
    evalVector c p i=p.eval (c i) := rfl

@[simp] theorem at_pow (c : ι → K) (j : Nat) :
    evalVector c ((X:K[X])^j)=c^j := by ext i; simp

@[simp] theorem at_C_mul_pow (c : ι → K) (a : K) (j : Nat) :
    evalVector c (C a*X^j)=a • c^j := by ext i; simp

theorem reflection_degree : ((1:K[X])-X).natDegree≤1 := by
  simpa using Polynomial.natDegree_sub_le (1:K[X]) X

theorem reflect_degree (p : K[X]) :
    (p.comp (1-X)).natDegree≤p.natDegree :=
  Polynomial.natDegree_comp_le.trans (by
    simpa using Nat.mul_le_mul_left p.natDegree (reflection_degree (K:=K)))

@[simp] theorem at_reflect (c : ι → K) (p : K[X]) :
    evalVector c (p.comp (1-X))=evalVector (1-c) p := by
  ext i
  simp [Polynomial.eval_comp]

@[simp] theorem at_reflect_pow (c : ι → K) (j : Nat) :
    evalVector (1-c) (((1:K[X])-X)^j)=c^j := by
  ext i
  simp

theorem cut_top {p : K[X]} {n : Nat} (hn : 0 < n) (dp : p.natDegree≤n)
    {q : K[X]} (mq : q.Monic) (dq : q.natDegree=n) :
    (p-p.coeff n • q).natDegree<n := by
  have hd : (p-p.coeff n • q).natDegree≤n :=
    (Polynomial.natDegree_sub_le _ _).trans
      (max_le dp ((Polynomial.natDegree_smul_le _ _).trans dq.le))
  have coef0 : (p-p.coeff n • q).coeff n=0 := by
    rw [coeff_sub,Polynomial.smul_eq_C_mul,coeff_C_mul,←dq]
    have qc : q.coeff q.natDegree=1 := mq
    rw [qc,mul_one,sub_self]
  by_contra! h
  have e := le_antisymm hd h
  have nz : p-p.coeff n • q≠0 := by
    intro h0
    rw [h0,natDegree_zero] at e
    omega
  have b := leadingCoeff_ne_zero.mpr nz
  unfold leadingCoeff at b
  rw [e,coef0] at b
  exact b rfl

variable [Fintype ι]

omit [Fintype ι] in
theorem linear_silent_at {M : Type*} [AddCommMonoid M] [Module K M]
    (c : ι → K) (L : (ι → K) →ₗ[K] M) (p : K[X]) (n : Nat)
    (hp : p.natDegree≤n) (quiet : ∀ j≤n, L (c^j)=0) :
    L (evalVector c p)=0 := by
  conv_lhs => rw [p.as_sum_support_C_mul_X_pow]
  rw [map_sum,map_sum]
  apply Finset.sum_eq_zero
  intro j hj
  have hj' := (le_natDegree_of_ne_zero (mem_support_iff.mp hj)).trans hp
  rw [at_C_mul_pow,map_smul,quiet _ hj',smul_zero]

theorem silent_at (c z : ι → K) (p : K[X]) (n : Nat)
    (hp : p.natDegree≤n) (quiet : ∀ j≤n, row z (c^j)=0) :
    row z (evalVector c p)=0 :=
  linear_silent_at c (row z) p n hp quiet

omit [Fintype ι] in
theorem linear_silent_reflected {M : Type*} [AddCommMonoid M] [Module K M]
    (c : ι → K) (L : (ι → K) →ₗ[K] M) (p : K[X]) (n : Nat)
    (hp : p.natDegree≤n) (quiet : ∀ j≤n, L (c^j)=0) :
    L (evalVector (1-c) p)=0 := by
  rw [← at_reflect]
  exact linear_silent_at c L _ n ((reflect_degree p).trans hp) quiet

theorem silent_reflected (c z : ι → K) (p : K[X]) (n : Nat)
    (hp : p.natDegree≤n) (quiet : ∀ j≤n, row z (c^j)=0) :
    row z (evalVector (1-c) p)=0 := by
  rw [← at_reflect]
  exact silent_at c z _ n ((reflect_degree p).trans hp) quiet

omit [Fintype ι] in
/-- A monic test pays the next power after all lower powers. The
coefficient of that one highest power is not guessed. -/
theorem power_from_top {M : Type*} [AddCommGroup M] [Module K M]
    (c : ι → K) (L : (ι → K) →ₗ[K] M) (n : Nat) (hn : 0<n)
    (p : K[X]) (monic : p.Monic) (degree : p.natDegree=n)
    (low : ∀ j<n, L (c^j)=0)
    (top : L (evalVector (1-c) p)=0) : L (c^n)=0 := by
  let q := ((1:K[X])-X)^n
  have hq : q.natDegree≤n := by
    change (((1:K[X])-X)^n).natDegree≤n
    rw [natDegree_pow]
    simpa using Nat.mul_le_mul_left n (reflection_degree (K:=K))
  have hr := cut_top hn hq monic degree
  have r := linear_silent_reflected c L (q-q.coeff n • p) (n-1)
      (by omega) (fun j hj => low j (by omega))
  rw [map_sub,map_smul,map_sub,map_smul,top,smul_zero,sub_zero] at r
  change L (evalVector (1-c) (((1:K[X])-X)^n))=0 at r
  rw [at_reflect_pow] at r
  exact r

theorem transpose_read (A : Matrix ι ι K) (z w : ι → K) :
    row z (mat A w)=row (mat A.transpose z) w := by
  rw [row_apply,row_apply,mat_apply,mat_apply,dotProduct_comm (A.transpose *ᵥ z),
    Matrix.dotProduct_transpose_mulVec]

theorem left_smul (a : K) (z w : ι → K) :
    row (a • z) w=a*row z w := by simp

theorem left_sub (a b w : ι → K) :
    row (a-b) w=row a w-row b w := by simp

theorem left_add (a b w : ι → K) :
    row (a+b) w=row a w+row b w := by simp

theorem clock_slide (Y z w : ι → K) :
    row (Y*z) w=row z (Y*w) := by
  simp only [row_apply,dotProduct,Pi.mul_apply]
  apply Finset.sum_congr rfl
  intro i _
  ring

end RKResearch.Certified.DIRK12MidpointProbes.Vector

#print axioms RKResearch.Certified.DIRK12MidpointProbes.Vector.cut_top
#print axioms RKResearch.Certified.DIRK12MidpointProbes.Vector.silent_reflected
