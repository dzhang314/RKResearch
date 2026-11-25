module

public import RKCert.ReviewedNative.HankelAntiTriangularRank
public import Mathlib.RingTheory.Polynomial.Basic

import Lean.Elab.Tactic.Omega

@[expose] public section

/-! # Ordinary paid monic coefficient changes

No abstract rank engine: coefficient matrices have full rank by the
Mathlib triangular determinant. A residual polynomial uses only the
ordinary leading Hankel and its one next right-hand side. -/
namespace RKResearch.Certified.Graded.HankelPaidMonicBasis

open Matrix Polynomial Module
open scoped Matrix Polynomial BigOperators

noncomputable section
variable {K : Type*} [Field K]

def pairGram {m n : ℕ} (J : K[X] →ₗ[K] K) (P : Fin m → K[X]) (Q : Fin n → K[X]) :
    Matrix (Fin m) (Fin n) K := fun i j => J (P i * Q j)

def purePowers (n : ℕ) : Fin n → K[X] := fun i => X^i.val

def hankel (J : K[X] →ₗ[K] K) (n : ℕ) : Matrix (Fin n) (Fin n) K :=
  pairGram J (purePowers n) (purePowers n)

@[simp] theorem hankel_apply (J : K[X] →ₗ[K] K) (n : ℕ) (i j : Fin n) :
    hankel J n i j = J (X^(i.val+j.val)) := by
  change J (X^i.val * X^j.val) = _
  rw [pow_add]

private def coeffColumns {n : ℕ} (P : Fin n → K[X]) : Matrix (Fin n) (Fin n) K :=
  fun i j => (P j).coeff i.val

private theorem coeff_expansion {n : ℕ} {P : K[X]} (h : P.natDegree<n) :
    P=∑ k : Fin n, C (P.coeff k.val)*X^k.val := by
  rw [Fin.sum_univ_eq_sum_range (fun k : ℕ => C (P.coeff k) * (X : K[X])^k) n]
  exact P.as_sum_range_C_mul_X_pow' h

private theorem pairGram_mul_columns {m n : ℕ} (J : K[X] →ₗ[K] K)
    (P : Fin m → K[X]) (Q : Fin n → K[X]) (bound : ∀ j, (Q j).natDegree<n) :
    pairGram J P (purePowers n) * coeffColumns Q = pairGram J P Q := by
  ext i j
  rw [Matrix.mul_apply]
  change (∑ k : Fin n, J (P i*X^k.val)*(Q j).coeff k.val) = J (P i*Q j)
  calc
    _ = ∑ k : Fin n, J (P i * (C ((Q j).coeff k.val)*X^k.val)) := by
      apply Finset.sum_congr rfl
      intro k _
      have form : P i * (C ((Q j).coeff k.val)*X^k.val) =
          C ((Q j).coeff k.val)*(P i*X^k.val) := by ac_rfl
      rw [form,← Polynomial.smul_eq_C_mul,map_smul,smul_eq_mul]
      exact mul_comm _ _
    _ = _ := by rw [← map_sum,← Finset.mul_sum,← coeff_expansion (bound j)]

private theorem pairGram_transpose {m n : ℕ} (J : K[X] →ₗ[K] K)
    (P : Fin m → K[X]) (Q : Fin n → K[X]) :
    (pairGram J P Q)ᵀ = pairGram J Q P := by
  ext i j
  change J (P j*Q i) = J (Q i*P j)
  rw [mul_comm]

/-- A monic polynomial of each degree provides an honest basis change
with determinant a unit. The readout after it has precisely the same rank. -/
theorem rank_pairGram_of_monic_degrees {n : ℕ} (J : K[X] →ₗ[K] K)
    (P : Fin n → K[X]) (monic : ∀ i, (P i).Monic)
    (degree : ∀ i, (P i).natDegree=i.val) :
    (pairGram J P P).rank = (hankel J n).rank := by
  let U := coeffColumns P
  have cap (i : Fin n) : (P i).natDegree<n := (degree i).trans_lt i.isLt
  have tri : U.IsUpperTriangular := by
    intro i j ij
    change (j : ℕ) < (i : ℕ) at ij
    change (P j).coeff i.val=0
    apply coeff_eq_zero_of_natDegree_lt
    simpa only [degree] using ij
  have diag (i : Fin n) : U.diag i ≠ 0 := by
    change (P i).coeff i.val≠0
    rw [← degree i,coeff_natDegree,(monic i).leadingCoeff]
    exact one_ne_zero
  have nd : U.det ≠ 0 := (Matrix.IsUpperTriangular.det_ne_zero_iff tri).2 diag
  have ndt : Uᵀ.det ≠ 0 := by simpa only [Matrix.det_transpose] using nd
  have left : pairGram J P (purePowers n) = Uᵀ * hankel J n := by
    have h := congrArg Matrix.transpose (pairGram_mul_columns J (purePowers n) P cap)
    simpa only [Matrix.transpose_mul,pairGram_transpose,hankel,U] using h.symm
  have both : pairGram J P P = (Uᵀ*hankel J n)*U := by
    rw [← left]
    exact (pairGram_mul_columns J P P cap).symm
  rw [both,Matrix.rank_mul_eq_left_of_det_ne_zero U _ nd,
    Matrix.rank_mul_eq_right_of_det_ne_zero Uᵀ _ ndt]

/-- Solve only the paid ordinary leading block, with a prescribed monic
term X^r. At r=0 this is its empty-system interpretation. -/
theorem exists_monic_residual (J : K[X] →ₗ[K] K) {r : ℕ}
    (h : (hankel J r).det ≠ 0) :
    ∃ B : K[X], B.Monic ∧ B.natDegree=r ∧
      ∀ k<r, J (X^k*B)=0 := by
  have rank : (hankel J r).rank = Fintype.card (Fin r) :=
    Matrix.rank_of_det_ne_zero h
  obtain ⟨a,ha⟩ :=
    ((Matrix.mulVec_surjective_iff_rank_eq_card (M := hankel J r)).mpr rank) (fun i : Fin r => -J (X^(i.val+r)))
  let low : K[X] := ∑ j : Fin r, C (a j)*X^j.val
  have mem : low ∈ degreeLT K r := by
    apply (degreeLT K r).sum_mem
    intro i _
    simpa only [C_mul_X_pow_eq_monomial] using monomial_coe_mem_degreeLT i (a i)
  have ldeg : low.degree < (r : WithBot ℕ) := mem_degreeLT.mp mem
  have xm : ((X:K[X])^r).degree = (r : WithBot ℕ) := degree_X_pow r
  have bd : ((X:K[X])^r+low).degree=(r : WithBot ℕ) :=
    (degree_add_eq_left_of_degree_lt (lt_of_lt_of_eq ldeg xm.symm)).trans xm
  refine ⟨X^r+low,monic_X_pow_add ldeg,natDegree_eq_of_degree_eq_some bd,?_⟩
  intro k hk
  let i : Fin r := ⟨k,hk⟩
  have e : (∑ j : Fin r, J (X^k*(C (a j)*X^j.val))) = (hankel J r *ᵥ a) i := by
    rw [Matrix.mulVec, dotProduct]
    apply Finset.sum_congr rfl
    intro j _
    have form : (X:K[X])^k*(C (a j)*X^j.val) = C (a j)*X^(k+j.val) := by
      rw [pow_add]
      ac_rfl
    rw [form,← Polynomial.smul_eq_C_mul,map_smul,smul_eq_mul,hankel_apply]
    change a j * J (X^(k+j.val)) = J (X^(k+j.val))*a j
    exact mul_comm _ _
  rw [mul_add,map_add,show X^k*low = ∑ j : Fin r, (X:K[X])^k*(C (a j)*X^j.val) by
    simp only [low,Finset.mul_sum],map_sum,e,congrFun ha i,← pow_add]
  change J (X^(k+r)) + -J (X^(k+r))=0
  exact add_neg_cancel _

end
end RKResearch.Certified.Graded.HankelPaidMonicBasis
