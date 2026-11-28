module

public import RKCert.ReviewedNative.DIRK12MidpointRealSupport
public import Mathlib.Data.Fin.Embedding
import Mathlib.Tactic.Ring
import Mathlib.Tactic.FieldSimp

@[expose] public section

/-! Two reusable scalar barycentric facts: one may remove the zero
node from a Lagrange weight, and the resulting weights annihilate
all polynomials below the top interpolation degree. -/
namespace RKResearch.Certified.DIRK12MidpointReverse.Bary

open Polynomial DIRK12MidpointRealInterval
open scoped BigOperators Polynomial

variable {K : Type*} [Field K]

theorem split_zero {n : Nat} (c : Fin (n+1) → K) (c0 : c 0=0) (j : Fin n) :
    Lagrange.nodalWeight Finset.univ c j.succ =
      (c j.succ)⁻¹*Lagrange.nodalWeight Finset.univ (fun i => c i.succ) j := by
  have e : (Finset.univ : Finset (Fin (n+1))).erase j.succ =
      insert 0 (((Finset.univ : Finset (Fin n)).erase j).map (Fin.succEmb n)) := by
    ext i
    refine Fin.cases ?_ (fun r => ?_) i
    · simp [Ne.symm (Fin.succ_ne_zero j)]
    · simp only [Finset.mem_erase,Finset.mem_univ,and_true,Finset.mem_insert,
        Fin.succ_ne_zero,false_or,Finset.mem_map,Fin.succEmb,Function.Embedding.coeFn_mk]
      constructor
      · intro h
        exact ⟨r, fun e => h (congrArg Fin.succ e),rfl⟩
      · rintro ⟨l,h,e⟩
        have q : l=r := Fin.succ_injective _ e
        subst l
        intro e
        exact h (Fin.succ_injective _ e)
  have nmem : (0:Fin (n+1))∉
      (((Finset.univ : Finset (Fin n)).erase j).map (Fin.succEmb n)) := by
    intro hh
    rcases Finset.mem_map.mp hh with ⟨r,_,e⟩
    exact Fin.succ_ne_zero _ e
  rw [Lagrange.nodalWeight,e,Finset.prod_insert nmem,Finset.prod_map,c0,sub_zero]
  rfl

theorem annihilate {n : Nat} (c : Fin (n+1) → K) (cd : Function.Injective c)
    (P : K[X]) (h : P.natDegree < n) :
    (∑ j, Lagrange.nodalWeight Finset.univ c j * P.eval (c j))=0 := by
  have g : P.degree < ((Finset.univ : Finset (Fin (n+1))).card : WithBot ℕ) := by
    apply lt_of_le_of_lt (degree_le_natDegree (p:=P))
    rw [Finset.card_univ,Fintype.card_fin]
    exact_mod_cast Nat.lt_succ_of_lt h
  have q := Lagrange.coeff_eq_sum (Set.injOn_of_injective cd) g
  rw [Finset.card_univ,Fintype.card_fin,Nat.add_sub_cancel,coeff_eq_zero_of_natDegree_lt h] at q
  simpa only [Lagrange.nodalWeight,← Finset.prod_inv_distrib,div_eq_mul_inv,mul_comm] using q.symm

theorem annihilate_reflected {n : Nat} (c : Fin (n+1) → K) (cd : Function.Injective c)
    (m : Nat) (hm : m < n) :
    (∑ j, Lagrange.nodalWeight Finset.univ c j * (1-c j)^m)=0 := by
  have hd : ((1:K[X])-X).natDegree≤1 := by
    have v := natDegree_sub_le (1:K[X]) X
    simpa using v
  have zm : (((1:K[X])-X)^m).natDegree < n := by
    rw [natDegree_pow]
    exact lt_of_le_of_lt (by simpa using Nat.mul_le_mul_left m hd) hm
  have q := annihilate c cd ((1-X)^m) zm
  simpa only [eval_pow,eval_sub,eval_one,eval_X] using q

variable [CharZero K]

/-- Integrating the hull times a monic quadratic needs exactly the
first three scalar hull moments. -/
theorem integral_two (rs : List K) (a b : K) :
    integral (hull (rs++[a,b])) =
      moment rs 2-(a+b)*moment rs 1+a*b*moment rs 0 := by
  rw [hull_append]
  have e : hull rs*hull [a,b] =
      (X:K[X])^2*hull rs - (a+b) • (X^1*hull rs) + (a*b) • (X^0*hull rs) := by
    rw [Polynomial.smul_eq_C_mul,Polynomial.smul_eq_C_mul,map_add,map_mul]
    simp only [hull,pow_one,pow_zero,mul_one,one_mul]
    ring
  rw [e,map_add,map_sub,map_smul,map_smul,smul_eq_mul,smul_eq_mul,
    integral_hull,integral_hull,integral_hull]

end RKResearch.Certified.DIRK12MidpointReverse.Bary

#print axioms RKResearch.Certified.DIRK12MidpointReverse.Bary.split_zero
#print axioms RKResearch.Certified.DIRK12MidpointReverse.Bary.annihilate
#print axioms RKResearch.Certified.DIRK12MidpointReverse.Bary.integral_two
