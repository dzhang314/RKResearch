module
public import Mathlib.LinearAlgebra.Lagrange
import Mathlib.Tactic.FieldSimp
import Mathlib.Tactic.Ring
import Lean.Elab.Tactic.Omega

@[expose] public section

namespace RKCert.ReviewedNative.NodalOddDiagonal

open Polynomial
open scoped BigOperators
noncomputable section

variable {K : Type*} [Field K] {d : ℕ}

abbrev nodal {n : ℕ} (y : Fin n→K) : K[X] := Lagrange.nodal Finset.univ y
def slope {n : ℕ} (y : Fin n→K) (i : Fin n) : K := (nodal y).derivative.eval (y i)

theorem slope_eq_prod {n : ℕ} (y : Fin n→K) (i : Fin n) :
    slope y i = ∏ j∈(Finset.univ : Finset (Fin n)).erase i, (y i-y j) := by
  rw [slope,Lagrange.eval_nodal_derivative_eval_node_eq (Finset.mem_univ i),
    Lagrange.eval_nodal]

theorem slope_ne_zero {n : ℕ} {y : Fin n→K} (inj : Function.Injective y) (i : Fin n) :
    slope y i≠0 := by
  rw [slope_eq_prod]
  exact Finset.prod_ne_zero_iff.mpr fun j hj =>
    sub_ne_zero.mpr (fun e=>(Finset.mem_erase.mp hj).1 (inj e.symm))

private theorem degree_drop {P : K[X]} {k : ℕ}
    (bound : P.natDegree≤k+1) (z : P.coeff (k+1)=0) : P.natDegree≤k := by
  apply natDegree_le_iff_coeff_eq_zero.mpr
  intro m hm
  by_cases e : m=k+1
  · rwa [e]
  · exact coeff_eq_zero_of_natDegree_lt (bound.trans_lt (by omega))

private theorem degree_for_nodes {P : K[X]} {n : ℕ} (le : P.natDegree<n) :
    P.degree<((Finset.univ : Finset (Fin n)).card : WithBot ℕ) := by
  rw [Finset.card_univ,Fintype.card_fin]
  exact P.degree_le_natDegree.trans_lt (WithBot.coe_lt_coe.mpr le)

private theorem top_lagrange {P : K[X]} {y : Fin (d+4)→K}
    (inj : Function.Injective y) (le : P.natDegree≤d+3) :
    P.coeff (d+3)=∑ i, P.eval (y i)/slope y i := by
  have ds : P.natDegree<d+4 := by omega
  have E := Lagrange.coeff_eq_sum (s:=Finset.univ) inj.injOn (degree_for_nodes ds)
  rw [Finset.card_univ,Fintype.card_fin,show (d+4)-1=d+3 by omega] at E
  simpa only [slope_eq_prod] using E

/-- A true symmetric matrix with the three paid kernel columns; one
additional isotropic column eliminates the top diagonal degree. -/
theorem exists_odd_diagonal (dp : 1≤d) {y : Fin (d+4)→K}
    (inj : Function.Injective y) (T : Fin (d+4)→Fin (d+4)→K)
    (symm : ∀ i j, T i j=T j i)
    (ker : ∀ i (k : ℕ), k≤2 → ∑ j,T i j*(y j)^k=0)
    (isotropic : (∑ i,(y i)^3*(∑ j,T i j*(y j)^3))=0) :
    ∃ H : K[X], H.natDegree≤2*d-1 ∧
      ∀ i,H.eval (y i)=-(slope y i*T i i*slope y i) := by
  classical
  let I : Finset (Fin (d+4)) := Finset.univ
  let S (i j : Fin (d+4)) := slope y i*T i j*slope y j
  let G (i : Fin (d+4)) := Lagrange.interpolate I y (S i)
  have ss (i j : Fin (d+4)) : S i j=S j i := by dsimp only [S];rw [symm i j];ring
  have gv (i j : Fin (d+4)) : (G i).eval (y j)=S i j :=
    Lagrange.eval_interpolate_at_node _ inj.injOn (Finset.mem_univ j)
  have gd₀ (i : Fin (d+4)) : (G i).natDegree≤d+3 := by
    have a := Lagrange.degree_interpolate_le (S i) (s:=I) inj.injOn
    apply natDegree_le_of_degree_le
    simpa only [I,Finset.card_univ,Fintype.card_fin,show (d+4)-1=d+3 by omega] using a
  have rowTop (i : Fin (d+4)) (k : ℕ) (le : (G i*X^k).natDegree≤d+3) :
      (G i*X^k).coeff (d+3)=slope y i*(∑ j,T i j*(y j)^k) := by
    rw [top_lagrange inj le,Finset.mul_sum]
    apply Finset.sum_congr rfl
    intro j _
    rw [eval_mul,eval_pow,eval_X,gv]
    dsimp only [S]
    field_simp [slope_ne_zero inj j] <;> ring
  have gd (i : Fin (d+4)) : (G i).natDegree≤d := by
    have z₀ : (G i).coeff (d+3)=0 := by
      have h := rowTop i 0 (by simpa only [pow_zero,mul_one] using gd₀ i)
      rw [ker i 0 (by decide),mul_zero,pow_zero,mul_one] at h
      exact h
    have d₂ : (G i).natDegree≤d+2 := degree_drop (gd₀ i) z₀
    have z₁ : (G i).coeff (d+2)=0 := by
      have q : (G i*X^1).natDegree≤d+3 := by simpa only [Nat.add_assoc] using (natDegree_mul_le_of_le d₂ (natDegree_X_pow_le (R := K) 1))
      exact (coeff_mul_X_pow (G i) 1 (d+2)).symm.trans
        ((rowTop i 1 q).trans (by rw [ker i 1 (by decide),mul_zero]))
    have d₁ : (G i).natDegree≤d+1 := degree_drop d₂ z₁
    have z₂ : (G i).coeff (d+1)=0 := by
      have q : (G i*X^2).natDegree≤d+3 := by simpa only [Nat.add_assoc] using (natDegree_mul_le_of_le d₁ (natDegree_X_pow_le (R := K) 2))
      exact (coeff_mul_X_pow (G i) 2 (d+1)).symm.trans
        ((rowTop i 2 q).trans (by rw [ker i 2 le_rfl,mul_zero]))
    exact degree_drop d₁ z₂
  have top3 (i : Fin (d+4)) :
      (G i).coeff d=slope y i*(∑ j,T i j*(y j)^3) := by
    have le : (G i*X^3).natDegree≤d+3 := natDegree_mul_le_of_le (gd i) (by simp)
    exact (coeff_mul_X_pow (G i) 3 d).symm.trans (rowTop i 3 le)
  let inc : Fin (d+1)→Fin (d+4) := Fin.castLE (by omega)
  let J := (Finset.univ : Finset (Fin (d+1))).image inc
  have injInc : Function.Injective inc := fun i j h=>Fin.ext (congrArg (fun j : Fin (d+4) => j.val) h)
  have cardJ : J.card=d+1 := by
    dsimp only [J]
    rw [Finset.card_image_of_injective _ injInc,
    Finset.card_univ,Fintype.card_fin]
  let l (j : Fin (d+4)) := Lagrange.basis J y j
  have ld (j : Fin (d+4)) (hj : j∈J) : (l j).natDegree≤d := by
    have a := Lagrange.natDegree_basis (s:=J) inj.injOn hj
    rw [cardJ,Nat.add_sub_cancel] at a
    exact a.le
  have reconstruct (i k : Fin (d+4)) :
      (∑ j∈J,(l j).eval (y i)*(G j).eval (y k))=(G k).eval (y i) := by
    have dg : (G k).degree<(J.card:WithBot ℕ) := by
      rw [cardJ]
      exact (degree_le_of_natDegree_le (gd k)).trans_lt (WithBot.coe_lt_coe.mpr (Nat.lt_succ_self d))
    have ev := congrArg (Polynomial.eval (y i)) (Lagrange.eq_interpolate (s:=J) inj.injOn dg)
    simp only [Lagrange.interpolate_apply,eval_finsetSum,eval_mul,eval_C] at ev
    rw [ev]
    apply Finset.sum_congr rfl
    intro j _
    rw [gv j k,gv k j,ss j k]
    dsimp only [l]
    ring
  let D : K[X] := ∑ j∈J,l j*G j
  let Cpoly : K[X] := Lagrange.interpolate J y (fun j=>(G j).coeff d)
  have back (i : Fin (d+4)) :
      (∑ j∈J,C ((l j).eval (y i))*G j)=G i := by
    have bd : (∑ j∈J,C ((l j).eval (y i))*G j).natDegree≤d :=
      natDegree_sum_le_of_forall_le _ _ (fun j _=>(natDegree_C_mul_le _ _).trans (gd j))
    apply eq_of_degrees_lt_of_eval_index_eq I inj.injOn
    · exact degree_for_nodes (bd.trans_lt (by omega))
    · exact degree_for_nodes ((gd i).trans_lt (by omega))
    · intro k _
      simp only [eval_finsetSum,eval_mul,eval_C]
      rw [reconstruct i k,gv k i,gv i k,ss k i]
  have Cv (i : Fin (d+4)) : Cpoly.eval (y i)=(G i).coeff d := by
    have q := congrArg (fun p : K[X]=>p.coeff d) (back i)
    simp only [finsetSum_coeff,coeff_C_mul] at q
    rw [←q]
    simp only [Cpoly,Lagrange.interpolate_apply,eval_finsetSum,eval_mul,eval_C,l]
    apply Finset.sum_congr rfl
    intro j _
    ring
  have Cd : Cpoly.natDegree≤d := by
    have h := Lagrange.degree_interpolate_le (fun j=>(G j).coeff d) (s:=J) inj.injOn
    rw [cardJ,Nat.add_sub_cancel] at h
    exact natDegree_le_of_degree_le h
  have Czero : Cpoly.coeff d=0 := by
    have le : (Cpoly*X^3).natDegree≤d+3 := natDegree_mul_le_of_le Cd (by simp)
    have E := (coeff_mul_X_pow Cpoly 3 d).symm.trans (top_lagrange inj le)
    rw [E,←isotropic]
    apply Finset.sum_congr rfl
    intro i _
    rw [eval_mul,Cv,eval_pow,eval_X,top3]
    field_simp [slope_ne_zero inj i] <;> ring
  have topD : D.coeff (d+d)=Cpoly.coeff d := by
    simp only [D,Cpoly,Lagrange.interpolate_apply,finsetSum_coeff,coeff_C_mul]
    apply Finset.sum_congr rfl
    intro j hj
    rw [coeff_mul_add_eq_of_natDegree_le (ld j hj) (gd j)]
    dsimp only [l]
    ring
  have Dd : D.natDegree≤d+d := natDegree_sum_le_of_forall_le _ _
    (fun j hj=>natDegree_mul_le_of_le (ld j hj) (gd j))
  have low : D.natDegree≤2*d-1 := by
    have eq : 2*d-1+1=d+d := by omega
    apply degree_drop (k:=2*d-1)
    · rwa [eq]
    · rw [eq,topD,Czero]
  refine ⟨-D,natDegree_neg_le_of_le low,?_⟩
  intro i
  simp only [D,eval_neg,eval_finsetSum,eval_mul]
  rw [reconstruct i i, gv]

end
end RKCert.ReviewedNative.NodalOddDiagonal
