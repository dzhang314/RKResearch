module

public import Mathlib.LinearAlgebra.Lagrange
import Mathlib.Tactic.Ring

@[expose] public section

/-! A literal positive-degree cardinal reader. The \(n\) nonzero
clock labels reconstruct \(X,\ldots,X^n\), not the constant polynomial. -/
namespace RKResearch.Certified.PositiveCardinalRead

open Polynomial
open scoped BigOperators Polynomial

variable {K : Type*} [Field K]

noncomputable def card {n : Nat} (c : Fin n → K) (i : Fin n) : K[X] :=
  C ((c i)⁻¹)*X*Lagrange.basis Finset.univ c i

noncomputable def read {n : Nat} (m : Fin n → K) : K[X] →ₗ[K] K :=
  ∑ j, m j • Polynomial.lcoeff K (j.val+1)

theorem read_power {n : Nat} (m : Fin n → K) (i : Fin n) :
    read m (X^(i.val+1))=m i := by
  classical
  simp only [read,LinearMap.sum_apply,LinearMap.smul_apply,smul_eq_mul,lcoeff_apply,coeff_X_pow]
  have h (j : Fin n) :
      m j*(if j.val+1=i.val+1 then (1:K) else 0) = if j=i then m j else 0 := by
    by_cases e : j=i
    · subst j
      simp
    · have q : j.val≠i.val := fun z => e (Fin.ext z)
      simp [e,q]
  simp_rw [h]
  simp

theorem expand_power {n : Nat} (c : Fin n → K) (hc : Function.Injective c)
    (hz : ∀ j, c j≠0) (m : Fin n) :
    (∑ i, (c i)^(m.val+1) • card c i)=(X:K[X])^(m.val+1) := by
  have hdeg : ((X:K[X])^m.val).degree < ((Finset.univ : Finset (Fin n)).card:WithBot ℕ) := by
    simpa only [degree_X_pow,Finset.card_univ,Fintype.card_fin,Nat.cast_withBot,WithBot.coe_lt_coe]
      using m.isLt
  have I := Lagrange.eq_interpolate (f:=((X:K[X])^m.val))
    (Set.injOn_of_injective hc) hdeg
  simp only [eval_pow,eval_X] at I
  calc
    _ = ∑ i : Fin n, (X:K[X])*(C ((c i)^m.val)*Lagrange.basis Finset.univ c i) := by
      apply Finset.sum_congr rfl
      intro i _
      rw [Polynomial.smul_eq_C_mul,card]
      calc
        _ = C ((c i)^(m.val+1)*(c i)⁻¹)*X*Lagrange.basis Finset.univ c i := by
          rw [map_mul]
          ring
        _ = _ := by
          have h : (c i)^(m.val+1)*(c i)⁻¹=(c i)^m.val := by
            rw [pow_succ,mul_assoc ((c i)^m.val) (c i) (c i)⁻¹,mul_inv_cancel₀ (hz i),mul_one]
          rw [h]
          ring
    _ = (X:K[X])*Lagrange.interpolate Finset.univ c (fun i => (c i)^m.val) := by
      rw [Lagrange.interpolate_apply,Finset.mul_sum]
    _ = _ := by rw [← I,pow_succ']

noncomputable def weights {n : Nat} (c : Fin n → K) (m : Fin n → K) (i : Fin n) : K :=
  read m (card c i)

theorem recovers {n : Nat} (c : Fin n → K) (hc : Function.Injective c)
    (hz : ∀ j, c j≠0) (m : Fin n → K) (j : Fin n) :
    (∑ i, weights c m i*(c i)^(j.val+1))=m j := by
  have h := congrArg (read m) (expand_power c hc hz j)
  rw [map_sum,read_power] at h
  simpa only [map_smul,smul_eq_mul,weights,mul_comm] using h

theorem literal_denominator_nonzero {n : Nat} (c : Fin n → K)
    (hc : Function.Injective c) (hz : ∀ j, c j≠0) (i : Fin n) :
    c i*(∏ j ∈ (Finset.univ : Finset (Fin n)).erase i, (c i-c j))≠0 := by
  refine mul_ne_zero (hz i) (Finset.prod_ne_zero_iff.mpr ?_)
  intro j hj
  exact sub_ne_zero.mpr (fun h => (Finset.mem_erase.mp hj).1 (hc h).symm)

theorem card_formula {n : Nat} (c : Fin n → K) (i : Fin n) :
    card c i = C ((c i)⁻¹*Lagrange.nodalWeight Finset.univ c i)*
      X*Lagrange.nodal (Finset.univ.erase i) c := by
  rw [card,Lagrange.basis_eq_prod_sub_inv_mul_nodal_div (Finset.mem_univ i),
    ← Lagrange.nodal_erase_eq_nodal_div (Finset.mem_univ i),map_mul]
  ring

theorem card_eval_zero {n : Nat} (c : Fin n → K) (i : Fin n) :
    (card c i).eval 0=0 := by simp [card]

theorem card_eval_node {n : Nat} (c : Fin n → K) (hc : Function.Injective c) (hz : ∀ j, c j≠0)
    (i j : Fin n) : (card c i).eval (c j) = if i=j then 1 else 0 := by
  rw [card,eval_mul,eval_mul,eval_C,eval_X]
  by_cases e : i=j
  · subst j
    rw [Lagrange.eval_basis_self (Set.injOn_of_injective hc) (Finset.mem_univ i),
      inv_mul_cancel₀ (hz i)]
    simp
  · rw [Lagrange.eval_basis_of_ne e (Finset.mem_univ j)]
    simp [e]

end RKResearch.Certified.PositiveCardinalRead

#print axioms RKResearch.Certified.PositiveCardinalRead.recovers
#print axioms RKResearch.Certified.PositiveCardinalRead.card_eval_node
