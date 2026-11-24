module

public import Mathlib.Algebra.Polynomial.BigOperators
public import Mathlib.Algebra.Polynomial.Roots

@[expose] public section

/-! # A generic finite Cauchy system, from Mathlib polynomial evaluation

Clearing the common denominator makes a polynomial of degree at most n−1.
It has n distinct roots from the tests, and evaluation at each pole then
detects the corresponding coefficient. This leaf has no tableau dependency.
-/
namespace RKResearch.Certified.Graded

open Polynomial
open scoped BigOperators

variable {K : Type*} [Field K]

theorem cauchy_kernel {n:ℕ} (x y a : Fin n→K)
    (hx:Function.Injective x) (hy:Function.Injective y)
    (hxy:∀ i j,x i+y j≠0)
    (test:∀ i,(∑ j : Fin n,a j/(x i+y j))=0) :
    ∀ j,a j=0 := by
  classical
  intro j
  let S := (Finset.univ : Finset (Fin n))
  let P : K[X] := ∑ l∈S,C (a l)*∏ k∈S.erase l,(X+C (y k))
  have hdeg : P.natDegree≤n-1 := by
    unfold P
    apply natDegree_sum_le_of_forall_le
    intro l hl
    apply (natDegree_C_mul_le _ _).trans
    apply (natDegree_prod_le _ _).trans
    calc
      _ ≤ ∑ k ∈ S.erase l, (1:ℕ) := Finset.sum_le_sum (fun k _ =>
        (natDegree_add_le _ _).trans (by simp))
      _ = n-1 := by rw [Finset.sum_const,nsmul_eq_mul,mul_one,Finset.card_erase_of_mem hl]; simp [S]
  have ev (v:K) :
      P.eval v=∑ l∈S,a l*∏ k∈S.erase l,(v+y k) := by
    simp only [P,eval_finsetSum,eval_mul,eval_C,eval_prod,eval_add,eval_X]
  have roots (i:Fin n) : P.eval (x i)=0 := by
    rw [ev]
    let M := ∏ k∈S,(x i+y k)
    have pull (l:Fin n) (_:l∈S) :
        a l*(∏ k∈S.erase l,(x i+y k))=M*(a l/(x i+y l)) := by
      have hm : (∏ k∈S.erase l,(x i+y k))*(x i+y l)=M :=
        Finset.prod_erase_mul S _ (show l∈S from Finset.mem_univ l)
      apply (mul_left_cancel₀ (hxy i l))
      rw [show (x i+y l)*(a l*(∏ k∈S.erase l,(x i+y k)))=M*a l by
        rw [←hm];ac_rfl]
      calc
        M*a l = M*((a l/(x i+y l))*(x i+y l)) := by rw [div_mul_cancel₀ _ (hxy i l)]
        _ = (x i+y l)*(M*(a l/(x i+y l))) := by ac_rfl
    rw [Finset.sum_congr rfl pull,←Finset.mul_sum]
    change M*(∑ l:Fin n,a l/(x i+y l))=0
    rw [test,mul_zero]
  have p0 : P=0 :=
    eq_zero_of_natDegree_lt_card_of_eval_eq_zero P hx roots (by
      rw [Fintype.card_fin]; have :=j.isLt; omega)
  have pole : P.eval (-y j)=a j*∏ k∈S.erase j,(-y j+y k) := by
    rw [ev]
    apply Finset.sum_eq_single_of_mem j (show j∈S from Finset.mem_univ j)
    intro l _ hl
    have h := Finset.mem_erase.mpr ⟨Ne.symm hl,show j∈S from Finset.mem_univ j⟩
    rw [Finset.prod_eq_zero h (neg_add_cancel (y j)),mul_zero]
  have nz : (∏ k∈S.erase j,(-y j+y k))≠0 := by
    apply Finset.prod_ne_zero_iff.mpr
    intro k hk
    rw [add_comm,←sub_eq_add_neg]
    exact sub_ne_zero.mpr (fun eq=>(Finset.mem_erase.mp hk).1 (hy eq))
  rw [p0,eval_zero] at pole
  exact (mul_eq_zero.mp pole.symm).resolve_right nz

end RKResearch.Certified.Graded
