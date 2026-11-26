module
public import Mathlib.LinearAlgebra.Vandermonde
public import Mathlib.LinearAlgebra.Matrix.NonsingularInverse

@[expose] public section

/-! # Integer-node interpolation over a factorial-unit ring

A degree-<n polynomial is represented by its coefficients, not by its
function on the ring. Evaluation at 0, ..., n-1 recovers those coefficients.
Primitive readouts use inverses of actual scalar units; no ambient division
or domain hypothesis is used.
-/

namespace RKResearch.Certified.RingNodeInterpolation

open scoped Matrix BigOperators

variable {R : Type*} [CommRing R]
variable {n : ℕ} {ι : Type*}

private theorem isUnit_natCast_of_dvd {k q : ℕ} (hd : k ∣ q)
    (hq : IsUnit (q : R)) : IsUnit (k : R) := by
  obtain ⟨a, ha⟩ := hd
  have hdR : (k : R) ∣ (q : R) := ⟨(a : R), by rw [ha, Nat.cast_mul]⟩
  exact isUnit_of_dvd_unit hdR hq

/-- A paid factorial pays every smaller factorial over the same ring. -/
theorem factorialUnit_mono {m n : ℕ} (hmn : m ≤ n)
    (hn : IsUnit (n.factorial : R)) : IsUnit (m.factorial : R) :=
  isUnit_natCast_of_dvd (Nat.factorial_dvd_factorial hmn) hn

/-- Any positive integer at most n is a unit when n! is a unit. -/
theorem isUnit_natCast_of_factorial {k : ℕ} (hn : IsUnit (n.factorial : R))
    (hk : 0 < k) (hkn : k ≤ n) : IsUnit (k : R) :=
  isUnit_natCast_of_dvd (Nat.dvd_factorial hk hkn) hn

def integerNodes (n : ℕ) : Fin n → R :=
  fun i => (i.val : R)

def integerVandermonde (n : ℕ) : Matrix (Fin n) (Fin n) R :=
  Matrix.vandermonde (integerNodes n)

/-- Arbitrary nonzero divisors are not enough: every positive node
difference actually divides the paid factorial. -/
theorem isUnit_det_integerVandermonde (hn : IsUnit (n.factorial : R)) :
    IsUnit (integerVandermonde (R := R) n).det := by
  unfold integerVandermonde
  rw [Matrix.det_vandermonde]
  apply IsUnit.prod_univ_iff.mpr
  intro i
  apply IsUnit.prod_iff.mpr
  intro j hj
  have hij : i.val < j.val := (Finset.mem_Ioi (α := Fin n) (a := i) (x := j)).mp hj
  have hdiff : j.val - i.val ≤ n :=
    (Nat.sub_le _ _).trans (Nat.le_of_lt j.isLt)
  change IsUnit ((j.val : R) - (i.val : R))
  rw [← Nat.cast_sub (Nat.le_of_lt hij)]
  exact isUnit_natCast_of_factorial hn (Nat.sub_pos_of_lt hij) hdiff

theorem integerVandermonde_inv_mul (hn : IsUnit (n.factorial : R)) :
    (integerVandermonde (R := R) n)⁻¹ * integerVandermonde n = 1 :=
  Matrix.nonsing_inv_mul _ (isUnit_det_integerVandermonde hn)

theorem integerVandermonde_mul_inv (hn : IsUnit (n.factorial : R)) :
    integerVandermonde (R := R) n * (integerVandermonde n)⁻¹ = 1 :=
  Matrix.mul_nonsing_inv _ (isUnit_det_integerVandermonde hn)

/-- Evaluate a degree-<n coefficient vector on the integer grid. -/
def integerSamples (a : Fin n → R) : Fin n → R :=
  integerVandermonde n *ᵥ a

/-- The matrix nonsingular inverse is justified by the unit theorem above. -/
noncomputable def reconstruct (v : Fin n → R) : Fin n → R :=
  (integerVandermonde n)⁻¹ *ᵥ v

theorem reconstruct_samples (hn : IsUnit (n.factorial : R)) (a : Fin n → R) :
    reconstruct (integerSamples a) = a := by
  unfold reconstruct integerSamples
  rw [Matrix.mulVec_mulVec, integerVandermonde_inv_mul hn, Matrix.one_mulVec]

theorem samples_reconstruct (hn : IsUnit (n.factorial : R)) (v : Fin n → R) :
    integerSamples (reconstruct v) = v := by
  unfold reconstruct integerSamples
  rw [Matrix.mulVec_mulVec, integerVandermonde_mul_inv hn, Matrix.one_mulVec]

/-- A coefficient test matrix, transported to the integer sample coordinates. -/
noncomputable def sampleReadMap (M : Matrix ι (Fin n) R) : Matrix ι (Fin n) R :=
  M * (integerVandermonde n)⁻¹

theorem sampleReadMap_samples (hn : IsUnit (n.factorial : R))
    (M : Matrix ι (Fin n) R) (a : Fin n → R) :
    sampleReadMap M *ᵥ integerSamples a = M *ᵥ a := by
  unfold sampleReadMap
  rw [← Matrix.mulVec_mulVec]
  change M *ᵥ reconstruct (integerSamples a) = M *ᵥ a
  rw [reconstruct_samples hn]

def evaluationMatrix (n : ℕ) (nodes : ι → R) : Matrix ι (Fin n) R :=
  Matrix.of fun i j => nodes i ^ j.val

theorem evaluationMatrix_mulVec_apply (nodes : ι → R) (a : Fin n → R) (i : ι) :
    (evaluationMatrix n nodes *ᵥ a) i = ∑ j : Fin n, nodes i ^ j.val * a j :=
  rfl

noncomputable def resample (n : ℕ) (nodes : ι → R) : Matrix ι (Fin n) R :=
  sampleReadMap (evaluationMatrix n nodes)

theorem resample_samples (hn : IsUnit (n.factorial : R))
    (nodes : ι → R) (a : Fin n → R) :
    resample n nodes *ᵥ integerSamples a = evaluationMatrix n nodes *ᵥ a :=
  sampleReadMap_samples hn (evaluationMatrix n nodes) a

/-- One canonical element inverse from the unit (j+1), with no division on R. -/
noncomputable def reciprocalSucc (hn : IsUnit (n.factorial : R)) (j : Fin n) : R :=
  ↑((isUnit_natCast_of_factorial hn (Nat.zero_lt_succ j.val)
    (Nat.succ_le_of_lt j.isLt)).unit⁻¹)

theorem mul_reciprocalSucc (hn : IsUnit (n.factorial : R)) (j : Fin n) :
    ((j.val + 1 : ℕ) : R) * reciprocalSucc hn j = 1 :=
  (isUnit_natCast_of_factorial hn (Nat.zero_lt_succ j.val)
    (Nat.succ_le_of_lt j.isLt)).mul_val_inv

/-- Coefficient row for evaluation of the zero-constant primitive at x. -/
noncomputable def primitiveCoefficientRow (hn : IsUnit (n.factorial : R))
    (x : R) : Fin n → R :=
  fun j => reciprocalSucc hn j * x ^ (j.val + 1)

noncomputable def primitiveMatrix (hn : IsUnit (n.factorial : R))
    (nodes : ι → R) : Matrix ι (Fin n) R :=
  Matrix.of fun i => primitiveCoefficientRow hn (nodes i)

noncomputable def primitiveReadMap (hn : IsUnit (n.factorial : R))
    (nodes : ι → R) : Matrix ι (Fin n) R :=
  sampleReadMap (primitiveMatrix hn nodes)

theorem primitiveReadMap_samples (hn : IsUnit (n.factorial : R))
    (nodes : ι → R) (a : Fin n → R) :
    primitiveReadMap hn nodes *ᵥ integerSamples a = primitiveMatrix hn nodes *ᵥ a :=
  sampleReadMap_samples hn (primitiveMatrix hn nodes) a

/-- Read the zero-constant primitive at x directly from integer samples. -/
noncomputable def primitiveReadout (hn : IsUnit (n.factorial : R)) (x : R) : Fin n → R :=
  primitiveCoefficientRow hn x ᵥ* (integerVandermonde n)⁻¹

theorem primitiveReadout_samples (hn : IsUnit (n.factorial : R)) (x : R) (a : Fin n → R) :
    primitiveReadout hn x ⬝ᵥ integerSamples a = primitiveCoefficientRow hn x ⬝ᵥ a := by
  unfold primitiveReadout
  rw [← Matrix.dotProduct_mulVec]
  change primitiveCoefficientRow hn x ⬝ᵥ reconstruct (integerSamples a) = _
  rw [reconstruct_samples hn]

/-- Unit-interval primitive readout, i.e. the quadrature row. -/
noncomputable def quadratureWeights (hn : IsUnit (n.factorial : R)) : Fin n → R :=
  primitiveReadout hn 1

def sampledMonomial (j : Fin n) : Fin n → R :=
  fun i => integerNodes n i ^ j.val

theorem integerSamples_single (j : Fin n) :
    integerSamples (Pi.single j (1 : R)) = sampledMonomial j :=
  Matrix.mulVec_single_one (integerVandermonde n) j

theorem resample_monomial (hn : IsUnit (n.factorial : R)) (nodes : ι → R) (j : Fin n) :
    resample n nodes *ᵥ sampledMonomial j = fun i => nodes i ^ j.val := by
  rw [← integerSamples_single (R := R) j, resample_samples hn nodes]
  exact Matrix.mulVec_single_one (evaluationMatrix n nodes) j

theorem primitiveReadMap_monomial (hn : IsUnit (n.factorial : R))
    (nodes : ι → R) (j : Fin n) :
    primitiveReadMap hn nodes *ᵥ sampledMonomial j =
      fun i => primitiveCoefficientRow hn (nodes i) j := by
  rw [← integerSamples_single (R := R) j, primitiveReadMap_samples hn nodes]
  exact Matrix.mulVec_single_one (primitiveMatrix hn nodes) j

/-- The denominator-cleared primitive response on each sampled monomial. -/
theorem mul_primitiveReadMap_monomial (hn : IsUnit (n.factorial : R))
    (nodes : ι → R) (j : Fin n) (i : ι) :
    ((j.val + 1 : ℕ) : R) * (primitiveReadMap hn nodes *ᵥ sampledMonomial j) i =
      nodes i ^ (j.val + 1) := by
  rw [primitiveReadMap_monomial hn nodes j]
  change ((j.val + 1 : ℕ) : R) * (reciprocalSucc hn j * nodes i ^ (j.val + 1)) = _
  rw [← mul_assoc, mul_reciprocalSucc, one_mul]

theorem primitiveReadout_monomial (hn : IsUnit (n.factorial : R)) (x : R) (j : Fin n) :
    primitiveReadout hn x ⬝ᵥ sampledMonomial j = reciprocalSucc hn j * x ^ (j.val + 1) := by
  simp only [← integerSamples_single (R := R) j, primitiveReadout_samples hn x, dotProduct_single,
    mul_one, primitiveCoefficientRow]

/-- The denominator-cleared unit-interval quadrature moment. -/
theorem mul_quadratureWeights_monomial (hn : IsUnit (n.factorial : R)) (j : Fin n) :
    ((j.val + 1 : ℕ) : R) * (quadratureWeights hn ⬝ᵥ sampledMonomial j) = 1 := by
  unfold quadratureWeights
  rw [primitiveReadout_monomial, one_pow, mul_one, mul_reciprocalSucc]

end RKResearch.Certified.RingNodeInterpolation
