module

public import RKCert.ReviewedNative.ERKTerminalDeformation
public import RKCert.ReviewedNative.RationalVandermondeMoments
import Mathlib.Tactic.Ring
import Lean.Elab.Tactic.Omega

@[expose] public section

/-! Source-only bridge from actual donor rows to a specified outgoing
quadratic-defect profile. No paired-grid or number-theory import. -/

namespace RKResearch.Certified.RationalTerminalMass

open RKResearch RKResearch.Certified.Graded
open RKResearch.Certified.Graded.TerminalDeformation RKResearch.Certified.RationalMoments
open scoped BigOperators Matrix

variable {ι σ : Type*} [Fintype ι] [Fintype σ] {p : ℕ}

/-- Extend the rational donor coordinates by zero, summing if the
indexing deliberately names the same physical column more than once. -/
noncomputable def liftDonorWeights {n : ℕ} (e : Fin n → ι) (w : Fin n → ℚ) : ι → ℚ := by
  classical
  exact fun i => ∑ j, if i = e j then w j else 0

theorem liftDonorWeights_action {n : ℕ} (e : Fin n → ι) (w : Fin n → ℚ) (v : ι → ℚ) :
    row (liftDonorWeights e w) v = ∑ j, w j * v (e j) := by
  classical
  simp only [row_apply, dotProduct, liftDonorWeights, Finset.sum_mul]
  rw [Finset.sum_comm]
  apply Finset.sum_congr rfl
  intro j _
  rw [Finset.sum_eq_single_of_mem (e j) (Finset.mem_univ (e j))]
  · simp
  · intro i _ ine
    simp [ine]

noncomputable def primitiveRows {n : ℕ} (e : Fin n → ι) (z : Fin n → ℚ) (c : σ → ℚ) :
    Matrix σ ι ℚ := fun x => liftDonorWeights e (primitiveWeights z (c x))

theorem primitiveRows_rowLaw {n : ℕ} {A : Matrix ι ι ℚ} {e : Fin n → ι}
    {z : Fin n → ℚ} (inj : Function.Injective z) (c : σ → ℚ) (bound : p ≤ n + 1)
    (pure : ∀ t, ord t < p → ∀ j, normTree A t (e j) = z j ^ (ord t - 1)) :
    RowLaw A (primitiveRows e z c) c p := by
  intro x t pay
  have pos : 0 < ord t := t.order.pos
  let k : Fin n := ⟨ord t - 1, by omega⟩
  have hk : k.val + 1 = ord t := by
    dsimp [k]
    omega
  have nz : (ord t : ℚ) ≠ 0 := Nat.cast_ne_zero.mpr (Nat.ne_of_gt pos)
  have action : row (primitiveRows e z c x) (normTree A t) =
      ∑ j, primitiveWeights z (c x) j * z j ^ (ord t - 1) := by
    rw [primitiveRows, liftDonorWeights_action]
    simp_rw [pure t pay]
  rw [action]
  change (ord t : ℚ) * (∑ j, primitiveWeights z (c x) j * z j ^ k.val) = _
  rw [primitiveWeights_spec inj (c x) k, hk, mul_comm (ord t : ℚ), div_mul_cancel₀ _ nz]

theorem primitiveRows_baseline_zero {n : ℕ} {e : Fin n → ι} {z : Fin n → ℚ}
    (c : σ → ℚ) (q : ι → ℚ) (kill : ∀ j, q (e j) = 0) (x : σ) :
    row (primitiveRows e z c x) q = 0 := by
  rw [primitiveRows, liftDonorWeights_action]
  simp [kill]

theorem primitiveWeights_quadrature {n : ℕ} {z : Fin n → ℚ} (inj : Function.Injective z)
    (cap : p ≤ n) (k : ℕ) (pay : k + 1 ≤ p) :
    ((k + 1 : ℕ) : ℚ) * powerMass z (primitiveWeights z 1) k = 1 := by
  have kn : k < n := by omega
  have nz : ((k + 1 : ℕ) : ℚ) ≠ 0 := Nat.cast_ne_zero.mpr (by omega)
  have moment : powerMass z (primitiveWeights z 1) k = 1 / ((k + 1 : ℕ) : ℚ) := by
    simpa [powerMass] using primitiveWeights_spec inj (1 : ℚ) ⟨k,kn⟩
  rw [moment, mul_comm ((k + 1 : ℕ) : ℚ), div_mul_cancel₀ _ nz]

def naturalSamples (p : ℕ) : Fin p → ℚ := fun k => k.val

theorem naturalSamples_injective (p : ℕ) : Function.Injective (naturalSamples p) := by
  intro i j h
  apply Fin.ext
  exact Rat.natCast_injective h

noncomputable def copyWeights (lam : Fin p → ℚ) (β a : σ → ℚ) : σ → Fin p → ℚ :=
  fun x => terminalCopyWeights lam (β x) (a x)

theorem copyWeights_spec {lam : Fin p → ℚ} (inj : Function.Injective lam) (β a : σ → ℚ) :
    CopyMoments lam (copyWeights lam β a) β a p := by
  intro x j hj
  exact terminalCopyWeights_spec inj (β x) (a x) ⟨j,hj⟩

theorem powerMass_div (c a : σ → ℚ) (g : ℚ) (k : ℕ) :
    powerMass c (fun x => a x / g) k = powerMass c a k * g⁻¹ := by
  unfold powerMass
  rw [Finset.sum_mul]
  apply Finset.sum_congr rfl
  intro _ _
  simp only [div_eq_mul_inv]
  ring

/-- The output masses on the actual grade-three column A(2Ac-c^2),
with all paid reviewed conditions. The input row law is on actual donor
trees; the baseline gain must vanish, not just be left unmeasured. -/
theorem realize_quadratic_outgoing_mass
    {A : Matrix ι ι ℚ} {D : Matrix σ ι ℚ} {c β ω : σ → ℚ}
    (p4 : 4 ≤ p) (law : RowLaw A D c p) {η : ι → ℚ} (quiet : Quiet A η 2)
    {lam : Fin p → ℚ} (inj : Function.Injective lam)
    (base : ∀ x, row (D x) (monomialStageDefect A 1) = 0)
    (gain : row η (monomialStageDefect A 1) ≠ 0)
    (ann : ∀ k, k + 4 ≤ p → powerMass c ω k = 0)
    (quad : ∀ k, k + 1 ≤ p → ((k + 1 : ℕ) : ℚ) * powerMass c β k = 1) :
    let a := fun x => ω x / row η (monomialStageDefect A 1)
    let M := terminalMatrix A D η lam
    let b := terminalWeight (ι := ι) (copyWeights lam β a)
    HasOrder p M b ∧
      ∀ z, clockMass M b (mat M (monomialStageDefect M 1)) z =
        ∑ x, if c x = z then ω x else 0 := by
  classical
  let a := fun x => ω x / row η (monomialStageDefect A 1)
  let w := copyWeights lam β a
  let M := terminalMatrix A D η lam
  have copy : CopyMoments lam w β a p := copyWeights_spec inj β a
  have a0 (k : ℕ) (pay : k + 2 + 2 ≤ p) : powerMass c a k = 0 := by
    dsimp only [a]
    rw [powerMass_div, ann k (by omega), zero_mul]
  change HasOrder p M (terminalWeight (ι := ι) w) ∧
    ∀ z, clockMass M (terminalWeight (ι := ι) w) (mat M (monomialStageDefect M 1)) z =
      ∑ x, if c x = z then ω x else 0
  refine ⟨terminal_hasOrder law quiet copy a0 quad, ?_⟩
  intro z
  have pre : monomialStageDefect M 1 ∘ Sum.inl = monomialStageDefect A 1 :=
    monomialStageDefect_attach_inl A _ 1
  rw [terminal_clockMass law quiet copy (by omega) (by decide), pre]
  apply Finset.sum_congr rfl
  intro x _
  by_cases eq : c x = z
  · have gain_x := div_mul_cancel₀ (ω x) gain
    simp [eq, base x, a]
    simpa only [row_apply] using gain_x
  · simp [eq]

end RKResearch.Certified.RationalTerminalMass
