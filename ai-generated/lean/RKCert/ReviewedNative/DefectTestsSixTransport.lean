module

public import RKCert.ReviewedNative.DefectTestsSix

import Mathlib.LinearAlgebra.Matrix.DotProduct
@[expose] public section

/-! # Reuse the linear part of an order-six test across paired-clock charts -/
namespace RKResearch.Certified.Graded

open scoped Matrix

variable {ι κ R : Type*} [Fintype ι] [Fintype κ] [CommRing R]

/-- The operations that are actually shared by a pair-jump split of two
tableaux. This is only a linear equivalence, not an algebra equivalence:
the two quadratic pointwise products must still be tested physically. -/
structure DefectClockTransport
    (B : Matrix ι ι R) (b : ι → R) (D : Matrix κ κ R) (w : κ → R) where
  e : (ι → R) ≃ₗ[R] (κ → R)
  e_one : e 1 = 1
  e_mat : ∀ v, e (mat B v) = mat D (e v)
  e_clock : ∀ v, e (nodes B * v) = nodes D * e v
  e_row : ∀ v, row w (e v) = row b v

namespace DefectClockTransport

variable {B : Matrix ι ι R} {b : ι → R} {D : Matrix κ κ R} {w : κ → R}

/-- Build the transport from a common intermediate linear chart. In a
three-pair application `fB` and `fD` send each column to its head values
and rescaled pair jumps. The common chart's matrix and clocks can be
given by the fixed diagonal/block formulas, without choosing any basis
of the full nonlinear stage-column algebra. -/
def of_split {E : Type*} [AddCommMonoid E] [Module R E]
    (fB : (ι → R) ≃ₗ[R] E) (fD : (κ → R) ≃ₗ[R] E)
    (act clock : E → E) (out : E → R)
    (hone : fB 1 = fD 1)
    (hB : ∀ v, fB (mat B v) = act (fB v))
    (hD : ∀ v, fD (mat D v) = act (fD v))
    (hcB : ∀ v, fB (nodes B * v) = clock (fB v))
    (hcD : ∀ v, fD (nodes D * v) = clock (fD v))
    (hb : ∀ v, row b v = out (fB v))
    (hw : ∀ v, row w v = out (fD v)) :
    DefectClockTransport B b D w where
  e := fB.trans fD.symm
  e_one := by
    change fD.symm (fB 1) = 1
    rw [hone, fD.symm_apply_apply]
  e_mat := by
    intro v
    apply fD.injective
    change fD (fD.symm (fB (mat B v))) = fD (mat D (fD.symm (fB v)))
    simp only [LinearEquiv.apply_symm_apply, hB, hD]
  e_clock := by
    intro v
    apply fD.injective
    change fD (fD.symm (fB (nodes B * v))) = fD (nodes D * fD.symm (fB v))
    simp only [LinearEquiv.apply_symm_apply, hcB, hcD]
  e_row := by
    intro v
    change row w (fD.symm (fB v)) = row b v
    simp only [hw, hb, LinearEquiv.apply_symm_apply]

variable (T : DefectClockTransport B b D w)

theorem e_pow_mul (j : ℕ) (v : ι → R) :
    T.e ((nodes B) ^ j * v) = (nodes D) ^ j * T.e v := by
  induction j with
  | zero => simp
  | succ j ih =>
    simp only [Nat.succ_eq_add_one, pow_succ', mul_assoc, T.e_clock, ih]

theorem e_pow (j : ℕ) : T.e ((nodes B) ^ j) = (nodes D) ^ j := by
  simpa only [mul_one, T.e_one] using T.e_pow_mul j 1

theorem e_defect (j : ℕ) :
    T.e (monomialStageDefect B j) = monomialStageDefect D j := by
  simp only [monomialStageDefect_as_map, map_sub, map_smul, T.e_mat, T.e_pow]

theorem e_seed : T.e (quadraticSeed B) = quadraticSeed D := T.e_defect 1

theorem e_clockSeed : T.e (clockSeed B) = clockSeed D := by
  change T.e (nodes B * quadraticSeed B) = nodes D * quadraticSeed D
  rw [T.e_clock, T.e_seed]

theorem e_cubic {v : ι → R} (hv : v ∈ cubicDefects B) : T.e v ∈ cubicDefects D := by
  obtain ⟨a, d, h⟩ := Submodule.mem_span_pair.mp hv
  apply Submodule.mem_span_pair.mpr
  refine ⟨a, d, ?_⟩
  simpa only [map_add, map_smul, T.e_seed, T.e_clockSeed] using
    congrArg (fun v : ι → R => T.e v) h

private theorem probe_eq_row_pow {σ : Type*} [Fintype σ]
    (B : Matrix σ σ R) (b : σ → R) (j : ℕ) (v : σ → R) :
    probe B b j v = row b ((nodes B) ^ j * v) := by
  simp only [probe, row_apply, dotProduct, Pi.mul_apply, Pi.pow_apply, mul_assoc]

theorem e_probe (j : ℕ) (v : ι → R) :
    probe D w j (T.e v) = probe B b j v := by
  rw [probe_eq_row_pow D w j, ← T.e_pow_mul, T.e_row, ← probe_eq_row_pow B b j]

include T in
/-- All linear tests cross the common chart. The only new scalars are
the two genuine pointwise seed-square payments. -/
theorem transfer {z : R} (h : DefectTestsSix B b z)
    (h0 : probe D w 0 ((quadraticSeed D) ^ 2) = 0)
    (h1 : probe D w 1 ((quadraticSeed D) ^ 2) = 0) :
    DefectTestsSix D w z := by
  refine ⟨?_, ?_, ?_, h0, h1, ?_, ?_, ?_, ?_⟩
  · intro j hj
    rw [← T.e_pow j, T.e_row]
    exact h.quadrature j hj
  · apply dotProduct_eq _ _
    intro v
    obtain ⟨u, rfl⟩ := T.e.surjective v
    have eB : row b (mat B u) = z * row b u - probe B b 1 u := by
      simp only [row_apply, mat_apply, Matrix.dotProduct_mulVec, h.adjoint, sub_dotProduct,
        smul_dotProduct, smul_eq_mul, probe, pow_one]
      rfl
    have eD : row w (mat D (T.e u)) = z * row w (T.e u) - probe D w 1 (T.e u) := by
      simpa only [← T.e_mat, T.e_row, T.e_probe] using eB
    simp only [sub_dotProduct, smul_dotProduct, smul_eq_mul]
    rw [show w * nodes D = (fun i => w i * nodes D i) by rfl]
    simpa only [row_apply, mat_apply, Matrix.dotProduct_mulVec, probe, pow_one] using eD
  · intro j hj
    rw [← T.e_seed, T.e_probe]
    exact h.seed_moments j hj
  · rw [← T.e_seed, ← T.e_mat]
    exact T.e_cubic h.seed_advance
  · rw [← T.e_defect 2]
    exact T.e_cubic h.cubic
  · rw [← T.e_clockSeed, ← T.e_mat, T.e_probe]
    exact h.clock_seed_advance
  · rw [← T.e_defect 3, T.e_probe]
    exact h.quartic

end DefectClockTransport
end RKResearch.Certified.Graded
