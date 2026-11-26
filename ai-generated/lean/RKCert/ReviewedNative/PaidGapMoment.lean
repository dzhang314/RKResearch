module

public import RKCert.ReviewedNative.GradedDefects
import Mathlib.Tactic.Ring
import Lean.Elab.Tactic.Omega

@[expose] public section

/-! Paid moments of the actual endpoint clock differences. The
uncompensated commutator uses C A minus A C, not the Volterra defect. -/
namespace RKResearch.Certified.Graded.PaidGapMoment

open RKResearch
open scoped Matrix BigOperators

noncomputable section

variable {ι K : Type*} [Fintype ι] [DecidableEq ι] [Field K]

/-- The uncompensated clock commutator on physical stage indices. -/
def clockComm (A : Matrix ι ι K) : Matrix ι ι K :=
  Matrix.diagonal (nodes A) * A - A * Matrix.diagonal (nodes A)

/-- The raw two-index gap moment. No regrouping of stage indices is used. -/
def gapMoment (A : Matrix ι ι K) (b : ι → K) (h q : ℕ) : K :=
  ∑ i : ι, ∑ j : ι, b i * (clockComm A ^ h) i j * (nodes A i - nodes A j) ^ q

private def adClock (A M : Matrix ι ι K) : Matrix ι ι K :=
  Matrix.diagonal (nodes A) * M - M * Matrix.diagonal (nodes A)

private def adClockIter (A : Matrix ι ι K) (h : ℕ) : ℕ → Matrix ι ι K
  | 0 => clockComm A ^ h
  | q + 1 => adClock A (adClockIter A h q)

private abbrev clockPower (A : Matrix ι ι K) (k : ℕ) : ι → K :=
  (nodes A) ^ k

private theorem clockPower_zero (A : Matrix ι ι K) : clockPower A 0 = 1 := pow_zero _

private theorem diag_clockPower (A : Matrix ι ι K) (k : ℕ) :
    diag (nodes A) (clockPower A k) = clockPower A (k + 1) := by
  funext i
  simp only [diag_apply, clockPower, Pi.pow_apply, pow_succ']

private theorem diagonal_mulVec_eq_diag (A : Matrix ι ι K) (v : ι → K) :
    Matrix.diagonal (nodes A) *ᵥ v = diag (nodes A) v := by
  funext i
  simp only [Matrix.mulVec_diagonal, diag_apply]

private theorem mat_adClock (A M : Matrix ι ι K) (v : ι → K) :
    mat (adClock A M) v =
      diag (nodes A) (mat M v) - mat M (diag (nodes A) v) := by
  simp only [adClock, mat_apply, Matrix.sub_mulVec, ← Matrix.mulVec_mulVec,
    diagonal_mulVec_eq_diag]

private theorem mat_clockComm (A : Matrix ι ι K) (v : ι → K) :
    mat (clockComm A) v =
      diag (nodes A) (mat A v) - mat A (diag (nodes A) v) :=
  mat_adClock A A v

private theorem mat_mul_apply (A M : Matrix ι ι K) (v : ι → K) :
    mat (A * M) v = mat A (mat M v) := by
  simp only [mat_apply, Matrix.mulVec_mulVec]

private theorem factorial_cast_succ (k : ℕ) :
    ((k + 1).factorial : K) = ((k + 1 : ℕ) : K) * (k.factorial : K) := by
  rw [show (k + 1).factorial = (k + 1) * k.factorial from Nat.factorial_succ k, Nat.cast_mul]

private theorem factorial_cast_two (k : ℕ) :
    ((k + 2).factorial : K) =
      (((k + 1 : ℕ) : K) * ((k + 2 : ℕ) : K)) * (k.factorial : K) := by
  calc
    _ = ((k + 2 : ℕ) : K) * ((k + 1).factorial : K) :=
      factorial_cast_succ (K := K) (k + 1)
    _ = _ := by rw [factorial_cast_succ (K := K) k]; ac_rfl

private def monomialError (A : Matrix ι ι K) (k : ℕ) : ι → K :=
  ((k + 1 : ℕ) : K) • mat A (clockPower A k) - clockPower A (k + 1)

private theorem monomialError_mem (A : Matrix ι ι K) (k : ℕ) :
    monomialError A k ∈ zeroSpace A (k + 1) := by
  have e : monomialError A k = monomialStageDefect A k := by
    funext i
    simp only [monomialError, monomialStageDefect, Pi.sub_apply, Pi.smul_apply,
      smul_eq_mul, mat_apply, clockPower, nodes, Pi.pow_apply]
  rw [e]
  exact monomialStageDefect_mem A k

private theorem scaled_comm_clockPower (A : Matrix ι ι K) (k : ℕ) :
    (((k + 1 : ℕ) : K) * ((k + 2 : ℕ) : K)) • mat (clockComm A) (clockPower A k) -
      clockPower A (k + 2) ∈ zeroSpace A (k + 2) := by
  have h₀ : diag (nodes A) (monomialError A k) ∈ zeroSpace A (k + 2) :=
    diag_zeroSpace A (k + 1) (monomialError_mem A k)
  have h₁ : monomialError A (k + 1) ∈ zeroSpace A (k + 2) :=
    monomialError_mem A (k + 1)
  have e :
      (((k + 1 : ℕ) : K) * ((k + 2 : ℕ) : K)) • mat (clockComm A) (clockPower A k) -
          clockPower A (k + 2) =
        ((k + 2 : ℕ) : K) • diag (nodes A) (monomialError A k) -
          ((k + 1 : ℕ) : K) • monomialError A (k + 1) := by
    funext i
    simp only [mat_clockComm, monomialError, map_sub, map_smul, diag_clockPower,
      Pi.sub_apply, Pi.smul_apply, smul_eq_mul, Nat.cast_add, Nat.cast_one, Nat.cast_ofNat]
    ring
  rw [e]
  exact (zeroSpace A (k + 2)).sub_mem
    ((zeroSpace A (k + 2)).smul_mem _ h₀) ((zeroSpace A (k + 2)).smul_mem _ h₁)

private theorem clockComm_zeroSpace {A : Matrix ι ι K} {b : ι → K} {p k : ℕ}
    (ho : HasOrder p A b) (pay : k + 2 ≤ p) {v : ι → K} (hv : v ∈ zeroSpace A k) :
    mat (clockComm A) v ∈ zeroSpace A (k + 2) := by
  rw [mat_clockComm]
  exact (zeroSpace A (k + 2)).sub_mem
    (diag_zeroSpace A (k + 1) (mat_zeroSpace ho k (by omega) hv))
    (mat_zeroSpace ho (k + 1) (by omega) (diag_zeroSpace A k hv))

/-- Internal factorial-scaled reference on every input monomial which fits
the remaining order window. No quotient or new stage space is used. -/
private def Calibrated (A M : Matrix ι ι K) (e : ℕ) (coeff : K) (p : ℕ) : Prop :=
  ∀ a : ℕ, a + e + 1 ≤ p →
    ((a + e).factorial : K) • mat M (clockPower A a) -
      (coeff * (a.factorial : K)) • clockPower A (a + e) ∈ zeroSpace A (a + e)

private theorem calibrated_clockComm_pow {A : Matrix ι ι K} {b : ι → K} {p : ℕ}
    (ho : HasOrder p A b) (h : ℕ) :
    Calibrated A (clockComm A ^ h) (2 * h) (1 : K) p := by
  induction h with
  | zero =>
    intro a _
    simp only [Nat.mul_zero, Nat.add_zero, pow_zero, mat_apply, Matrix.one_mulVec,
      one_mul, sub_self, Submodule.zero_mem]
  | succ h ih =>
    intro a pay
    let k := a + 2 * h
    have eind : a + 2 * (h + 1) = k + 2 := by dsimp only [k]; omega
    have kpay : k + 3 ≤ p := by
      change a + 2 * (h + 1) + 1 ≤ p at pay
      rw [eind] at pay
      omega
    let previous : ι → K :=
      (k.factorial : K) • mat (clockComm A ^ h) (clockPower A a) -
        (a.factorial : K) • clockPower A k
    let step : ι → K :=
      (((k + 1 : ℕ) : K) * ((k + 2 : ℕ) : K)) • mat (clockComm A) (clockPower A k) -
        clockPower A (k + 2)
    have previous_mem : previous ∈ zeroSpace A k := by
      simpa only [previous, k, one_mul] using ih a (by dsimp only [k] at kpay; omega)
    have pushed : mat (clockComm A) previous ∈ zeroSpace A (k + 2) :=
      clockComm_zeroSpace ho (by omega) previous_mem
    have step_mem : step ∈ zeroSpace A (k + 2) := scaled_comm_clockPower A k
    have e :
        ((k + 2).factorial : K) •
            mat (clockComm A) (mat (clockComm A ^ h) (clockPower A a)) -
          (a.factorial : K) • clockPower A (k + 2) =
        (((k + 1 : ℕ) : K) * ((k + 2 : ℕ) : K)) • mat (clockComm A) previous +
          (a.factorial : K) • step := by
      funext i
      simp only [previous, step, map_sub, map_smul, factorial_cast_two (K := K) k,
        Pi.sub_apply, Pi.add_apply, Pi.smul_apply, smul_eq_mul]
      ring
    rw [eind, pow_succ', mat_mul_apply, one_mul, e]
    exact (zeroSpace A (k + 2)).add_mem
      ((zeroSpace A (k + 2)).smul_mem _ pushed) ((zeroSpace A (k + 2)).smul_mem _ step_mem)

private theorem calibrated_adClock {A M : Matrix ι ι K} {e p : ℕ} {coeff : K}
    (hm : Calibrated A M e coeff p) :
    Calibrated A (adClock A M) (e + 1) ((e : K) * coeff) p := by
  intro a pay
  let k := a + e
  have e₀ : a + (e + 1) = k + 1 := by dsimp only [k]; omega
  have e₁ : (a + 1) + e = k + 1 := by dsimp only [k]; omega
  have kpay : k + 2 ≤ p := by rw [e₀] at pay; omega
  let leftRef : ι → K :=
    (k.factorial : K) • mat M (clockPower A a) -
      (coeff * (a.factorial : K)) • clockPower A k
  let rightRef : ι → K :=
    ((k + 1).factorial : K) • mat M (clockPower A (a + 1)) -
      (coeff * ((a + 1).factorial : K)) • clockPower A (k + 1)
  have left_in : leftRef ∈ zeroSpace A k := by
    have s : a + e + 1 ≤ p := by change k + 1 ≤ p; omega
    exact hm a s
  have right_in : rightRef ∈ zeroSpace A (k + 1) := by
    have s : (a + 1) + e + 1 ≤ p := by rw [e₁]; omega
    change ((k + 1).factorial : K) • mat M (clockPower A (a + 1)) -
      (coeff * ((a + 1).factorial : K)) • clockPower A (k + 1) ∈ zeroSpace A (k + 1)
    simpa only [e₁] using hm (a + 1) s
  have push_left : diag (nodes A) leftRef ∈ zeroSpace A (k + 1) :=
    diag_zeroSpace A k left_in
  have cast_step : ((k + 1 : ℕ) : K) = ((a + 1 : ℕ) : K) + (e : K) := by
    rw [← e₁, Nat.cast_add (a + 1) e]
  have eq :
      ((k + 1).factorial : K) • mat (adClock A M) (clockPower A a) -
          (((e : K) * coeff) * (a.factorial : K)) • clockPower A (k + 1) =
        ((k + 1 : ℕ) : K) • diag (nodes A) leftRef - rightRef := by
    funext i
    simp only [leftRef, rightRef, mat_adClock, diag_clockPower, map_sub, map_smul,
      factorial_cast_succ (K := K) k, factorial_cast_succ (K := K) a,
      Pi.sub_apply, Pi.smul_apply, smul_eq_mul, cast_step]
    ring
  rw [e₀, eq]
  exact (zeroSpace A (k + 1)).sub_mem ((zeroSpace A (k + 1)).smul_mem _ push_left) right_in

private theorem calibrated_adClockIter {A : Matrix ι ι K} {b : ι → K} {p : ℕ}
    (ho : HasOrder p A b) (h q : ℕ) :
    Calibrated A (adClockIter A h q) (2 * h + q) (((2 * h).ascFactorial q : ℕ) : K) p := by
  induction q with
  | zero =>
    simpa only [adClockIter, Nat.add_zero, Nat.ascFactorial_zero, Nat.cast_one] using
      calibrated_clockComm_pow ho h
  | succ q ih =>
    have length_eq : 2 * h + q.succ = (2 * h + q) + 1 := Nat.add_succ (2 * h) q
    have coeff_eq : (((2 * h).ascFactorial q.succ : ℕ) : K) =
        ((2 * h + q : ℕ) : K) * (((2 * h).ascFactorial q : ℕ) : K) :=
      (congrArg (fun n : ℕ => (n : K))
        (Nat.ascFactorial_succ (n := 2 * h) (k := q))).trans
        (Nat.cast_mul (2 * h + q) ((2 * h).ascFactorial q))
    change Calibrated A (adClock A (adClockIter A h q))
      (2 * h + q.succ) (((2 * h).ascFactorial q.succ : ℕ) : K) p
    rw [length_eq, coeff_eq]
    exact calibrated_adClock ih

private theorem probe_zero_clock_apply (A : Matrix ι ι K) (b v : ι → K) :
    probe A b 0 v = b ⬝ᵥ v := by
  change row (fun i => b i * (nodes A i) ^ 0) v = _
  simp only [row_apply, pow_zero, mul_one]

private theorem paid_adClockIter_readout {A : Matrix ι ι K} {b : ι → K} {p : ℕ}
    (ho : HasOrder p A b) (h q : ℕ) (pay : 2 * h + q + 1 ≤ p) :
    ((2 * h + q + 1).factorial : K) *
      (b ⬝ᵥ (adClockIter A h q *ᵥ (1 : ι → K))) = (((2 * h).ascFactorial q : ℕ) : K) := by
  let k := 2 * h + q
  let M := adClockIter A h q
  let coeff : K := (((2 * h).ascFactorial q : ℕ) : K)
  have in_span :
      (k.factorial : K) • mat M (1 : ι → K) -
        coeff • clockPower A k ∈ zeroSpace A k := by
    have e := calibrated_adClockIter ho h q 0 (by simpa only [Nat.zero_add] using pay)
    simpa only [M, k, coeff, Nat.zero_add, Nat.factorial_zero, Nat.cast_one,
      mul_one, clockPower_zero] using e
  have read_zero := probe_zeroSpace (j := k) (k := 0) ho
    (by simpa only [Nat.zero_add, k] using pay) in_span
  change probe A b 0 ((k.factorial : K) • mat M (1 : ι → K) -
    coeff • clockPower A k) = 0 at read_zero
  have compare : (k.factorial : K) * (b ⬝ᵥ (M *ᵥ (1 : ι → K))) =
      coeff * (b ⬝ᵥ clockPower A k) := by
    simpa only [map_sub, map_smul, smul_eq_mul, probe_zero_clock_apply,
      mat_apply, sub_eq_zero] using read_zero
  have bush : ((k + 1 : ℕ) : K) * (b ⬝ᵥ clockPower A k) = 1 :=
    by simpa only [stageMass, clockPower, nodes] using ho.bushy_moment k pay
  change ((k + 1).factorial : K) * (b ⬝ᵥ (M *ᵥ (1 : ι → K))) = coeff
  calc
    _ = ((k + 1 : ℕ) : K) * ((k.factorial : K) * (b ⬝ᵥ (M *ᵥ (1 : ι → K)))) := by
      rw [factorial_cast_succ (K := K) k, mul_assoc]
    _ = coeff * (((k + 1 : ℕ) : K) * (b ⬝ᵥ clockPower A k)) := by
      rw [compare]
      ac_rfl
    _ = coeff := by rw [bush, mul_one]

private theorem adClockIter_entry (A : Matrix ι ι K) (h q : ℕ) (i j : ι) :
    adClockIter A h q i j = (nodes A i - nodes A j) ^ q * (clockComm A ^ h) i j := by
  induction q with
  | zero => simp only [adClockIter, pow_zero, one_mul]
  | succ q ih =>
    simp only [adClockIter, adClock, Matrix.sub_apply, Matrix.diagonal_mul,
      Matrix.mul_diagonal, ih, pow_succ]
    ring

private theorem adClockIter_dot_eq_gap (A : Matrix ι ι K) (b : ι → K) (h q : ℕ) :
    b ⬝ᵥ (adClockIter A h q *ᵥ (1 : ι → K)) = gapMoment A b h q := by
  simp only [dotProduct, Matrix.mulVec_apply_eq_sum, Pi.one_apply, mul_one, gapMoment]
  apply Finset.sum_congr rfl
  intro i _
  rw [Finset.mul_sum]
  apply Finset.sum_congr rfl
  intro j _
  rw [adClockIter_entry]
  simp only [nodes, Matrix.mulVec_apply_eq_sum, Pi.one_apply, mul_one]
  ac_rfl

private theorem ascFactorial_paid_unit {A : Matrix ι ι K} {b : ι → K} {p d : ℕ}
    (ho : HasOrder p A b) (positive : 0 < d) (q : ℕ) (pay : d + q ≤ p) :
    IsUnit ((d.ascFactorial q : ℕ) : K) := by
  induction q with
  | zero => simp only [Nat.ascFactorial_zero, Nat.cast_one, isUnit_one]
  | succ q ih =>
    rw [Nat.ascFactorial_succ, Nat.cast_mul]
    exact (ho.natCast_isUnit (n := d + q) (by omega) (by omega)).mul (ih (by omega))

private theorem factor_paid_factorial (d q : ℕ) (positive : 0 < d) :
    ((d + q + 1).factorial : K) = ((d.ascFactorial q : ℕ) : K) *
      ((d - 1).factorial : K) * ((d + q : ℕ) : K) * ((d + q + 1 : ℕ) : K) := by
  have idx : d + q - 1 + 1 = d + q := by omega
  have split : (d + q).factorial = (d + q) * (d + q - 1).factorial := by
    simpa only [Nat.succ_eq_add_one, idx] using Nat.factorial_succ (d + q - 1)
  rw [show (d + q + 1).factorial = (d + q + 1) * (d + q).factorial from
    Nat.factorial_succ (d + q), split, ← Nat.factorial_mul_ascFactorial' d q positive]
  simp only [Nat.cast_mul]
  ac_rfl

/-- A positive power of the physical clock commutator has its exact
cleared gap moment through the paid order. No condition on support,
stage ordering, the diagonal, or the characteristic beyond payment. -/
theorem paid_gapMoment {A : Matrix ι ι K} {b : ι → K} {p h q : ℕ}
    (ho : HasOrder p A b) (positive : 0 < h) (pay : 2 * h + q + 1 ≤ p) :
    ((2 * h - 1).factorial : K) * ((2 * h + q : ℕ) : K) *
      ((2 * h + q + 1 : ℕ) : K) * gapMoment A b h q = 1 := by
  have dpos : 0 < 2 * h := by omega
  have u := ascFactorial_paid_unit ho dpos q (by omega : 2 * h + q ≤ p)
  have e := paid_adClockIter_readout ho h q pay
  rw [adClockIter_dot_eq_gap, factor_paid_factorial (K := K) (2 * h) q dpos] at e
  apply u.mul_left_cancel
  calc
    _ = (((2 * h).ascFactorial q : ℕ) : K) * ((2 * h - 1).factorial : K) *
        ((2 * h + q : ℕ) : K) * ((2 * h + q + 1 : ℕ) : K) * gapMoment A b h q := by ac_rfl
    _ = (((2 * h).ascFactorial q : ℕ) : K) := e
    _ = _ := (mul_one _).symm

end
end RKResearch.Certified.Graded.PaidGapMoment
