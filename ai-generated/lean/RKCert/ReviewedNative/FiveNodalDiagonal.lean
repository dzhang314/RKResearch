module

public import Mathlib.LinearAlgebra.Lagrange
import Mathlib.Tactic.FieldSimp
import Mathlib.Tactic.NormNum
import Mathlib.Tactic.Ring
import Lean.Elab.Tactic.Omega

@[expose] public section

namespace RKCert.ReviewedNative.FiveNodalDiagonal

open Polynomial
open scoped BigOperators

noncomputable section
variable {K : Type*} [Field K]

abbrev nodal (y : Fin 5→K) : K[X] := Lagrange.nodal Finset.univ y

def slope (y : Fin 5→K) (j : Fin 5) : K := (nodal y).derivative.eval (y j)

theorem slope_eq_prod (y : Fin 5→K) (j : Fin 5) :
    slope y j = ∏ k ∈ (Finset.univ : Finset (Fin 5)).erase j, (y j-y k) := by
  rw [slope,Lagrange.eval_nodal_derivative_eval_node_eq (Finset.mem_univ j),
    Lagrange.eval_nodal]

theorem slope_ne_zero {y : Fin 5→K} (inj : Function.Injective y) (j : Fin 5) :
    slope y j≠0 := by
  rw [slope_eq_prod]
  exact Finset.prod_ne_zero_iff.mpr fun k hk =>
    sub_ne_zero.mpr (fun e => (Finset.mem_erase.mp hk).1 (inj e.symm))

private theorem dropTop {G : K[X]} {d : ℕ}
    (bound : G.natDegree≤d+1) (z : G.coeff (d+1)=0) : G.natDegree≤d := by
  apply natDegree_le_iff_coeff_eq_zero.mpr
  intro n hn
  by_cases e : n=d+1
  · rwa [e]
  · exact coeff_eq_zero_of_natDegree_lt (bound.trans_lt (by omega))

/-- Interpolate the derivative-scaled row. The three vanishing
moments strip its top three coefficients one at a time. -/
theorem row_affine {y : Fin 5→K} (inj : Function.Injective y) {v : Fin 5→K}
    (mom : ∀ k : ℕ, k≤2 → ∑ j, v j*(y j)^k=0) :
    ∃ a b : K, ∀ j, v j*slope y j=a+b*y j := by
  classical
  let G := Lagrange.interpolate (Finset.univ : Finset (Fin 5)) y (fun j=>v j*slope y j)
  have ys : Set.InjOn y ((Finset.univ : Finset (Fin 5)) : Set (Fin 5)) := inj.injOn
  have val (j : Fin 5) : G.eval (y j)=v j*slope y j :=
    Lagrange.eval_interpolate_at_node _ ys (Finset.mem_univ j)
  have g4 : G.natDegree≤4 := by
    apply natDegree_le_of_degree_le
    simpa [G] using Lagrange.degree_interpolate_le (fun j=>v j*slope y j) ys
  have top (k : ℕ) (d : (G*X^k).natDegree≤4) :
      (G*X^k).coeff 4=∑ j, v j*(y j)^k := by
    have gd : (G*X^k).degree < ((Finset.univ : Finset (Fin 5)).card : WithBot ℕ) :=
      (degree_le_of_natDegree_le d).trans_lt (by decide)
    have rule := Lagrange.coeff_eq_sum ys gd
    rw [show (Finset.univ : Finset (Fin 5)).card-1=4 by decide] at rule
    rw [rule]
    apply Finset.sum_congr rfl
    intro j _
    rw [eval_mul,eval_pow,eval_X,val,←slope_eq_prod]
    field_simp [slope_ne_zero inj j] <;> ring
  have z4 : G.coeff 4=0 := by
    simpa only [pow_zero,mul_one] using
      (top 0 (by simpa only [pow_zero,mul_one] using g4)).trans (mom 0 (by decide))
  have g3 : G.natDegree≤3 := dropTop g4 z4
  have g31 : (G*X^1).natDegree≤4 := natDegree_mul_le_of_le (p:=G) (q:=X^1) g3 (by rw [natDegree_X_pow])
  have z3 : G.coeff 3=0 := (coeff_mul_X_pow G 1 3).symm.trans
    ((top 1 g31).trans (mom 1 (by decide)))
  have g2 : G.natDegree≤2 := dropTop g3 z3
  have g22 : (G*X^2).natDegree≤4 := natDegree_mul_le_of_le (p:=G) (q:=X^2) g2 (by rw [natDegree_X_pow])
  have z2 : G.coeff 2=0 := (coeff_mul_X_pow G 2 2).symm.trans
    ((top 2 g22).trans (mom 2 (by decide)))
  have g1 : G.natDegree≤1 := dropTop g2 z2
  have form : G=C (G.coeff 0)+C (G.coeff 1)*X := by
    calc
      G = ∑ i ∈ Finset.range 2, monomial i (G.coeff i) :=
        G.as_sum_range' 2 (by omega)
      _ = _ := by
        rw [Finset.sum_range_succ,Finset.sum_range_one,monomial_zero_left,
          ←C_mul_X_eq_monomial]
  refine ⟨G.coeff 0,G.coeff 1,fun j=>?_⟩
  rw [←val j]
  conv_lhs => rw [form]
  simp

/-- For a symmetric five-row matrix that kills all polynomial data
of degree at most two, its derivative-scaled diagonal is quadratic. -/
theorem exists_diagonal_quadratic {y : Fin 5→K} (inj : Function.Injective y)
    (T : Fin 5→Fin 5→K) (symm : ∀ i j, T i j=T j i) (a : Fin 5→K)
    (diag : ∀ i, T i i=-(a i)^2)
    (ker : ∀ i (k : ℕ), k≤2 → ∑ j, T i j*(y j)^k=0) :
    ∃ H : K[X], H.natDegree≤2 ∧
      ∀ i, H.eval (y i)=(a i*slope y i)^2 := by
  let S (i j : Fin 5) := slope y i*T i j*slope y j
  let δ := y 1-y 0
  have dn : δ≠0 := sub_ne_zero.mpr (fun e => (by decide : (1:Fin 5)≠0) (inj e))
  have sm (i j : Fin 5) : S i j=S j i := by
    dsimp [S]
    rw [symm i j]
    ring
  have rows (i j : Fin 5) :
      S i j=S i 0+(S i 1-S i 0)*((y j-y 0)/δ) := by
    obtain ⟨u,v,h⟩ := row_affine inj (ker i)
    have form (j : Fin 5) : S i j=slope y i*(u+v*y j) := by
      dsimp only [S]
      rw [mul_assoc,h j]
    rw [form j,form 0,form 1]
    field_simp [dn]
    dsimp only [δ]
    ring
  have cols (i j : Fin 5) :
      S i j=S 0 j+(S 1 j-S 0 j)*((y i-y 0)/δ) := by
    calc
      S i j=S j i := sm i j
      _ = S j 0+(S j 1-S j 0)*((y i-y 0)/δ) := rows j i
      _ = _ := by rw [sm j 0,sm j 1]
  let L : K[X] := C δ⁻¹*(X-C (y 0))
  let R (j : Fin 5) : K[X] := C (S 0 j)+C (S 1 j-S 0 j)*L
  have lD : L.natDegree≤1 :=
    (natDegree_C_mul_le _ _).trans (natDegree_X_sub_C (y 0)).le
  have rD (j : Fin 5) : (R j).natDegree≤1 := natDegree_add_le_of_degree_le (by simp)
    ((natDegree_C_mul_le _ _).trans lD)
  have lv (i : Fin 5) : L.eval (y i)=(y i-y 0)/δ := by
    simp only [L,eval_mul,eval_sub,eval_X,eval_C,div_eq_mul_inv]
    ring
  have rv (i j : Fin 5) : (R j).eval (y i)=S i j := by
    rw [cols i j]
    simp only [R,eval_add,eval_mul,eval_C,lv]
  refine ⟨-(R 0+(R 1-R 0)*L),?_,?_⟩
  · exact natDegree_neg_le_of_le (natDegree_add_le_of_degree_le ((rD 0).trans (by decide))
      (natDegree_mul_le_of_le (natDegree_sub_le_of_le (rD 1) (rD 0)) lD))
  · intro i
    simp only [eval_neg,eval_add,eval_sub,eval_mul,rv,lv]
    rw [←rows i i]
    dsimp only [S]
    rw [diag i]
    ring

end
end RKCert.ReviewedNative.FiveNodalDiagonal
