module

public import RKCert.ReviewedNative.BufferedClockLeakage
public import Mathlib.Algebra.Polynomial.FieldDivision

public section

/-! # Paid clock polynomial quotient and rotated probe cancellation

Only native stage evaluation and ordinary probes are involved. The
formal polynomial division is subsequently tested at exactly one paid
probe whose shift reaches the first live moment of the numerator.
-/
namespace RKResearch.Certified.Graded

open RKResearch Polynomial
open scoped Matrix

variable {K : Type*} [Field K] {s : ℕ}
variable {A : Matrix (Fin (s+1)) (Fin (s+1)) K} {b : Fin (s+1) → K}

/-- Divide by a degree-q clock polynomial, then subtract the quotient's
value at one. The adjusted remainder still fits the full degree-q band. -/
theorem polynomial_degree_cut_at_one (F G : K[X]) {q n : ℕ}
    (qpos : 0<q) (fdeg : F.natDegree=q) (gdeg : G.natDegree≤q+n) :
    ∃ D : K[X], D.natDegree≤n ∧ D.eval 1=0 ∧ (G-F*D).natDegree≤q := by
  classical
  let L := G/F
  have f0 : F≠0 := by intro h; simp [h] at fdeg; omega
  have ld : L.natDegree≤n := by
    by_cases l0 : L=0
    · simp [l0]
    have g0 : G≠0 := by intro h; apply l0; simp [L,h]
    have fg : F.degree≤G.degree := le_of_not_gt (fun h => l0 ((Polynomial.div_eq_zero_iff f0).mpr h))
    have e := degree_add_div f0 fg
    change F.degree+L.degree=G.degree at e
    rw [degree_eq_natDegree f0,degree_eq_natDegree l0,degree_eq_natDegree g0,←Nat.cast_add] at e
    have t : F.natDegree+L.natDegree=G.natDegree := by exact_mod_cast e
    omega
  let D := L-C (L.eval 1)
  have dd : D.natDegree≤n :=
    (natDegree_sub_le _ _).trans (max_le ld (by simp))
  have d1 : D.eval 1=0 := by simp [D]
  have er : G-F*L=G%F := by
    apply (sub_eq_iff_eq_add).mpr
    simpa only [L,add_comm] using (EuclideanDomain.div_add_mod G F).symm
  have eq : G-F*D=G%F+F*C (L.eval 1) := by
    calc
      _ = (G-F*L)+F*C (L.eval 1) := by dsimp [D]; ring
      _ = _ := by rw [er]
  have mr : (G%F).natDegree≤q :=
    (natDegree_mod_lt G (by omega : F.natDegree≠0)).le.trans fdeg.le
  refine ⟨D,dd,d1,?_⟩
  rw [eq]
  exact (natDegree_add_le _ _).trans
    (max_le mr (natDegree_mul_le.trans (by rw [natDegree_C,fdeg,add_zero])))

/-- Probing the product of an actual stage polynomial and a bounded
clock polynomial is a finite convolution of the rotated probes. -/
theorem probe_mul_clock_polynomial (P Q : K[X]) (k n : ℕ) (dQ : Q.natDegree≤n) :
    probe A b k (evalNodes A (P*Q)) =
      ∑ j ∈ Finset.range (n+1), Q.coeff j*probe A b (k+j) (evalNodes A P) := by
  have shift (j k : ℕ) :
      probe A b k (evalNodes A (X^j*P))=probe A b (k+j) (evalNodes A P) := by
    induction j generalizing k with
    | zero => simp
    | succ j ih =>
      rw [pow_succ',mul_assoc,evalNodes_X_mul,probe_clock_shift,ih]
      rw [show k+1+j=k+(j+1) by omega]
  conv_lhs =>
    rw [Q.as_sum_range' (n+1) (by omega),Finset.mul_sum,map_sum,map_sum]
  apply Finset.sum_congr rfl
  intro j _
  rw [←C_mul_X_pow_eq_monomial]
  have mono : P*(C (Q.coeff j)*X^j)=(Q.coeff j) • (X^j*P) := by
    rw [Polynomial.smul_eq_C_mul]
    ring
  rw [mono,map_smul,map_smul,smul_eq_mul,shift]

/-- If the numerator's first live moment is m, a flat-denominator
quotient with value zero at one cannot absorb a multiplier of degree
at most m. This uses only the actual mth shifted row, no scalar table. -/
theorem rotated_probe_detects_quotient (G F Q D : K[X]) {m : ℕ} {a : K}
    (early : ∀ k<m, probe A b k (evalNodes A G)=0)
    (sharp : probe A b m (evalNodes A G)≠0)
    (flat : ∀ k≤m, probe A b k (evalNodes A F)=a)
    (qdeg : Q.natDegree≤m) (ddeg : D.natDegree≤Q.natDegree)
    (one : D.eval 1=0) (fit : G*Q=F*D) : Q=0 := by
  classical
  by_contra q0
  let n := Q.natDegree
  let k := m-n
  have kn : k+n=m := Nat.sub_add_cancel qdeg
  have GQ : probe A b k (evalNodes A (G*Q))=
      Q.coeff n*probe A b m (evalNodes A G) := by
    rw [probe_mul_clock_polynomial G Q k n le_rfl]
    rw [Finset.sum_eq_single n]
    · rw [kn]
    · intro j hj ne
      have jl : j<n := by have d := Finset.mem_range.mp hj; omega
      rw [early (k+j) (by omega),mul_zero]
    · intro bad
      exact (bad (Finset.mem_range.mpr (Nat.lt_succ_self _))).elim
  have FD : probe A b k (evalNodes A (F*D))=0 := by
    rw [probe_mul_clock_polynomial F D k n ddeg]
    have e : (∑ j ∈ Finset.range (n+1), D.coeff j*probe A b (k+j) (evalNodes A F))=
        (∑ j ∈ Finset.range (n+1),D.coeff j)*a := by
      rw [Finset.sum_mul]
      apply Finset.sum_congr rfl
      intro j hj
      have jl := Finset.mem_range.mp hj
      rw [flat (k+j) (by omega)]
    have sum : (∑ j ∈ Finset.range (n+1),D.coeff j)=D.eval 1 := by
      rw [eval_eq_sum_range' (n:=n+1) (by omega)]
      simp
    rw [e,sum,one,zero_mul]
  have top : Q.coeff n≠0 := leadingCoeff_ne_zero.mpr q0
  have eq := congrArg (fun P : K[X] => probe A b k (evalNodes A P)) fit
  change probe A b k (evalNodes A (G*Q))=probe A b k (evalNodes A (F*D)) at eq
  rw [GQ,FD] at eq
  exact mul_ne_zero top sharp eq

end RKResearch.Certified.Graded

