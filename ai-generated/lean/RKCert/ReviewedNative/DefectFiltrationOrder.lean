module

public import RKCert.ReviewedNative.GradedColumns
public import RKCert.ReviewedNative.FiniteScaledOrderCheck

import Mathlib.Tactic.Abel
import Mathlib.Tactic.Ring

@[expose] public section

/-! # A sufficient defect filtration for the reviewed rooted-tree order -/
namespace RKResearch.Certified.Graded

open FiniteRootedTree
open scoped FiniteRootedTree Matrix

variable {ι R : Type*} [Fintype ι] [CommRing R]

/-- A finite budget of submodules which supports the normalized reviewed
tree recursion and whose output moments vanish. There is no order
hypothesis in this structure, and no monotonicity or rank premise. -/
structure DefectFiltration (B : Matrix ι ι R) (b : ι → R) (p : ℕ) where
  space : ℕ → Submodule R (ι → R)
  clock : ∀ j, j + 1 < p →
    space j ≤ (space (j + 1)).comap (diag (nodes B))
  advance : ∀ j, j + 1 < p →
    space j ≤ (space (j + 1)).comap (mat B)
  primitive : ∀ j, j + 1 < p → monomialStageDefect B j ∈ space (j + 1)
  product : ∀ j k, j + k < p → ∀ ⦃v w : ι → R⦄,
    v ∈ space j → w ∈ space k → v * w ∈ space (j + k)
  silent : ∀ j, j < p → space j ≤ (row b).ker

/-- The existing normalized monomial defect in linear-map notation. -/
theorem monomialStageDefect_as_map (B : Matrix ι ι R) (j : ℕ) :
    monomialStageDefect B j =
      ((j + 1 : ℕ) : R) • mat B ((nodes B) ^ j) - (nodes B) ^ (j + 1) := by
  ext i
  simp only [monomialStageDefect, mat_apply, Pi.smul_apply, smul_eq_mul,
    Pi.sub_apply, Pi.pow_apply]

private theorem normTree_attach_mul (B : Matrix ι ι R) (r t : FiniteRootedTree) :
    normTree B (r ◂ t) =
      normTree B r * (((t.order : ℕ) : R) • mat B (normTree B t)) := by
  ext i
  simp only [normTree, forestFactorial, PNat.mul_coe, Nat.cast_mul, Φ, mat_apply,
    Matrix.mulVec_smul, Pi.mul_apply, Pi.smul_apply, smul_eq_mul]
  ac_rfl

namespace DefectFiltration

variable {B : Matrix ι ι R} {b : ι → R} {p : ℕ}

private theorem pow_mul_mem (F : DefectFiltration B b p) {j : ℕ} {v : ι → R}
    (hv : v ∈ F.space j) (n : ℕ) (pay : j + n < p) :
    (nodes B) ^ n * v ∈ F.space (j + n) := by
  induction n with
  | zero => simpa only [pow_zero, one_mul, Nat.add_zero] using hv
  | succ n ih =>
    have h := F.clock (j + n) (by omega) (ih (by omega))
    change nodes B * ((nodes B) ^ n * v) ∈ F.space (j + n + 1) at h
    simpa only [Nat.succ_eq_add_one, Nat.add_assoc, pow_succ', mul_assoc] using h

/-- The normalized genuine tree column differs from its same-grade clock
monomial by an element of the supplied certified silent submodule. -/
theorem normTree_sub_pow_mem (F : DefectFiltration B b p) (t : FiniteRootedTree)
    (ht : (t.order : ℕ) ≤ p) :
    normTree B t - (nodes B) ^ ((t.order : ℕ) - 1) ∈
      F.space ((t.order : ℕ) - 1) := by
  induction t with
  | leaf => simp [order]
  | butcherProduct r t ihr iht =>
    let j := (r.order : ℕ) - 1
    let k := (t.order : ℕ) - 1
    let x := nodes B
    have hrpos := r.order.pos
    have htpos := t.order.pos
    have hsz : ((r ◂ t).order : ℕ) = (r.order : ℕ) + (t.order : ℕ) := by
      simp only [order, PNat.add_coe]
    have hrpay : (r.order : ℕ) ≤ p := by omega
    have htpay : (t.order : ℕ) ≤ p := by omega
    have hk : (t.order : ℕ) = k + 1 := by dsimp [k]; omega
    have hg : ((r ◂ t).order : ℕ) - 1 = j + (k + 1) := by
      dsimp [j, k]
      omega
    have hbud : j + (k + 1) < p := by omega
    have hstep : k + 1 < p := by omega
    let u := normTree B r - x ^ j
    let a := ((t.order : ℕ) : R) • mat B (normTree B t)
    let v := a - x ^ (k + 1)
    have hu : u ∈ F.space j := ihr hrpay
    have ht' : normTree B t - x ^ k ∈ F.space k := iht htpay
    have hv : v ∈ F.space (k + 1) := by
      have ev : v = ((k + 1 : ℕ) : R) • mat B (normTree B t - x ^ k) +
          monomialStageDefect B k := by
        dsimp only [v, a]
        rw [hk, monomialStageDefect_as_map, map_sub, smul_sub]
        abel
      rw [ev]
      exact (F.space (k + 1)).add_mem
        ((F.space (k + 1)).smul_mem _ (F.advance k hstep ht')) (F.primitive k hstep)
    have hvclock : x ^ j * v ∈ F.space (j + (k + 1)) := by
      rw [Nat.add_comm j (k + 1)]
      exact F.pow_mul_mem hv j (by omega)
    have huclock : x ^ (k + 1) * u ∈ F.space (j + (k + 1)) :=
      F.pow_mul_mem hu (k + 1) hbud
    have huv := F.product j (k + 1) hbud hu hv
    rw [hg, normTree_attach_mul]
    change normTree B r * a - x ^ (j + (k + 1)) ∈ F.space (j + (k + 1))
    have e : normTree B r * a - x ^ (j + (k + 1)) =
        u * v + x ^ j * v + x ^ (k + 1) * u := by
      dsimp only [u, v]
      rw [pow_add]
      ring
    rw [e]
    exact (F.space _).add_mem ((F.space _).add_mem huv hvclock) huclock

/-- A silent filtration and the pure clock moments imply every reviewed
denominator-cleared tree identity at the same budget. -/
theorem scaled_tree_moments (F : DefectFiltration B b p) (z : R)
    (quad : ∀ j, j < p → ((j + 1 : ℕ) : R) * row b ((nodes B) ^ j) = z ^ j) :
    ∀ t : FiniteRootedTree, (t.order : ℕ) ≤ p →
      (t.factorial : R) * (b ⬝ᵥ Φ t B) = z ^ ((t.order : ℕ) - 1) := by
  intro t ht
  let j := (t.order : ℕ) - 1
  have hpos := t.order.pos
  have hj : j < p := by dsimp [j]; omega
  have hj' : j + 1 = (t.order : ℕ) := by dsimp [j]; omega
  have hz := F.silent j hj (F.normTree_sub_pow_mem t ht)
  change row b (normTree B t - (nodes B) ^ j) = 0 at hz
  rw [map_sub, sub_eq_zero] at hz
  have hq := quad j hj
  have hrow : row b (normTree B t) =
      ((t.forestFactorial : ℕ) : R) * (b ⬝ᵥ Φ t B) := by
    rw [normTree, map_smul, smul_eq_mul, row_apply]
  rw [← hz, hrow, hj', ← mul_assoc] at hq
  simpa only [factorial, PNat.mul_coe, Nat.cast_mul] using hq

/-- Recover the original reviewed order by canceling only the chosen
regular normalization scale. No tree factorial is divided out. -/
theorem hasOrder_of_smul {A : Matrix ι ι R} {z : R}
    (F : DefectFiltration (z • A) b p) (hz : IsLeftRegular z)
    (quad : ∀ j, j < p → ((j + 1 : ℕ) : R) * row b ((nodes (z • A)) ^ j) = z ^ j) :
    HasOrder p A b := by
  intro t ht
  have he := F.scaled_tree_moments z quad t ht
  rw [Φ_matrix_smul, dotProduct_smul, smul_eq_mul] at he
  refine ((IsLeftRegular.pow ((t.order : ℕ) - 1) hz).mul_left_eq_self_iff).mp ?_
  calc
    z ^ ((t.order : ℕ) - 1) * ((t.factorial : R) * (b ⬝ᵥ Φ t A)) =
        (t.factorial : R) * (z ^ ((t.order : ℕ) - 1) * (b ⬝ᵥ Φ t A)) := by ac_rfl
    _ = _ := he

end DefectFiltration
end RKResearch.Certified.Graded
