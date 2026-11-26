module

public import RKCert.ReviewedNative.DiagonalTreeShiftHasOrder
public import Mathlib.Data.Nat.Choose.Basic
import Mathlib.Algebra.Module.Pi
import Mathlib.Data.Nat.Choose.Sum
import Mathlib.Tactic.Ring

@[expose] public section

/-! The characteristic-zero shifted exact-flow reference on tall trees.
The recurrence is polynomial in the shift; it never divides by the diagonal. -/
namespace RKResearch.DiagonalTreeShift

open RKResearch FiniteRootedTree
open scoped FiniteRootedTree Matrix BigOperators

noncomputable section

variable {K : Type*} [Field K]

private def binomialShift (a : K) (n : ℕ) : (ℕ → K) →ₗ[K] K :=
  ∑ k ∈ Finset.range (n + 1),
    ((n.choose k : K) * a ^ (n - k)) • (LinearMap.proj k : (ℕ → K) →ₗ[K] K)

private theorem binomialShift_apply (a : K) (n : ℕ) (f : ℕ → K) :
    binomialShift a n f =
      ∑ k ∈ Finset.range (n + 1), (n.choose k : K) * (a ^ (n - k) * f k) := by
  simp only [binomialShift, LinearMap.sum_apply, LinearMap.smul_apply,
    LinearMap.proj_apply, smul_eq_mul, mul_assoc]

private theorem binomialShift_succ (a : K) (n : ℕ) (f : ℕ → K) :
    binomialShift a (n + 1) f =
      a * binomialShift a n f + binomialShift a n (fun k => f (k + 1)) := by
  simp only [binomialShift_apply]
  rw [Finset.sum_choose_succ_mul (fun i j => a ^ j * f i) n, Finset.mul_sum]
  congr 1
  apply Finset.sum_congr rfl
  intro k hk
  have he : n + 1 - k = (n - k) + 1 := by
    have hkn := Finset.mem_range.mp hk
    omega
  rw [he, pow_succ]
  ac_rfl

private theorem binomialShift_balance (a : K) (n : ℕ) (v : ℕ → K) :
    binomialShift a n (fun k => ((n : K) - (k : K)) * v (k + 1)) =
      a * binomialShift a n (fun k => (k : K) * v k) := by
  let leftTerm (k : ℕ) := (n.choose k : K) *
    (a ^ (n - k) * (((n : K) - (k : K)) * v (k + 1)))
  let rightTerm (k : ℕ) := (n.choose k : K) * (a ^ (n - k) * ((k : K) * v k))
  have hl : leftTerm n = 0 := by simp [leftTerm]
  have hr : rightTerm 0 = 0 := by simp [rightTerm]
  simp only [binomialShift_apply]
  change (∑ k ∈ Finset.range (n + 1), leftTerm k) =
    a * (∑ k ∈ Finset.range (n + 1), rightTerm k)
  rw [Finset.sum_range_succ leftTerm n, Finset.sum_range_succ' rightTerm n]
  simp only [hl, hr, add_zero, Finset.mul_sum]
  apply Finset.sum_congr rfl
  intro k hk
  have hkn := Finset.mem_range.mp hk
  have hp : a ^ (n - k) = a ^ (n - (k + 1)) * a := by
    rw [show n - k = (n - (k + 1)) + 1 by omega, pow_succ]
  have hc : (n.choose k : K) * ((n : K) - (k : K)) =
      (n.choose (k + 1) : K) * ((k + 1 : ℕ) : K) := by
    rw [← Nat.cast_sub (Nat.le_of_lt hkn)]
    simpa only [Nat.cast_mul] using
      (congrArg (fun u : ℕ => (u : K)) (Nat.choose_succ_right_eq n k)).symm
  dsimp only [leftTerm, rightTerm]
  rw [hp]
  calc
    _ = ((n.choose k : K) * ((n : K) - (k : K))) *
        (a * (a ^ (n - (k + 1)) * v (k + 1))) := by ac_rfl
    _ = _ := by rw [hc]; ac_rfl

private theorem tallTree_succPNat_step (n : ℕ) :
    tallTree (n + 1).succPNat = .leaf ◂ tallTree n.succPNat := by
  have hs : (n + 1).succPNat = n.succPNat + 1 := by
    apply PNat.eq
    rfl
  calc
    _ = tallTree (n.succPNat + 1) := congrArg tallTree hs
    _ = _ := by
      simpa only [tallTree] using
        (@PNat.recOn_succ n.succPNat (fun _ => FiniteRootedTree)
          (.leaf : FiniteRootedTree) (fun _ t => .leaf ◂ t))

private theorem lift_unary_eq (f : FiniteRootedTree → K) (x : TreeCombination K) :
    lift K f (unary K x) = lift K (fun t => f (.leaf ◂ t)) x := by
  change ((lift K f).comp (unary K)) x = lift K (fun t => f (.leaf ◂ t)) x
  apply LinearMap.congr_fun
  apply hom_ext_atoms K
  intro t
  simp only [LinearMap.comp_apply, unary_atom, lift_atom]

private theorem transform_tall_aux (a : K) (n : ℕ) (f : FiniteRootedTree → K) :
    transform K a f (tallTree n.succPNat) =
      binomialShift a n (fun k => f (tallTree k.succPNat)) := by
  induction n generalizing f with
  | zero =>
    change transform K a f .leaf = _
    simp [transform, expand, binomialShift_apply] <;>
      exact (congrArg f (@PNat.recOn_one (fun _ => FiniteRootedTree)
        (.leaf : FiniteRootedTree) (fun _ t => .leaf ◂ t))).symm
  | succ n ih =>
    rw [tallTree_succPNat_step n, binomialShift_succ a n]
    change lift K f (expand K a (.leaf ◂ tallTree n.succPNat)) = _
    rw [expand_unary, map_add, map_smul, lift_unary_eq]
    change transform K a (fun t => f (.leaf ◂ t)) (tallTree n.succPNat) +
      a * transform K a f (tallTree n.succPNat) = _
    rw [ih (fun t => f (.leaf ◂ t)), ih f]
    simp only [tallTree_succPNat_step]
    exact add_comm _ _

/-- The published literal edge-contraction shift is the ordinary binomial
transform when restricted to the tall trees. The index is the edge count. -/
theorem transform_tallTree_eq_binomial (a : K) (n : ℕ) (f : FiniteRootedTree → K) :
    transform K a f (tallTree n.succPNat) =
      ∑ k ∈ Finset.range (n + 1), (n.choose k : K) * a ^ (n - k) *
        f (tallTree k.succPNat) := by
  simp only [transform_tall_aux, binomialShift_apply, mul_assoc]

private def exactTall (K : Type*) [Field K] (n : ℕ) : K :=
  ((n + 1).factorial : K)⁻¹

private theorem exactFlowOutput_tallTree (n : ℕ) :
    exactFlowOutput K (tallTree n.succPNat) = exactTall K n := by
  simp only [exactFlowOutput, factorial_tallTree, Nat.succPNat_coe, exactTall]

/-- The exact-flow target after scalar edge contraction, on the tall tree
with n edges. For a physical shift by γ I, use the reference at a = -γ. -/
def shiftedExactTall (a : K) (n : ℕ) : K :=
  transform K a (exactFlowOutput K) (tallTree n.succPNat)

private theorem shiftedExactTall_eq_shift (a : K) (n : ℕ) :
    shiftedExactTall a n = binomialShift a n (exactTall K) := by
  unfold shiftedExactTall
  rw [transform_tall_aux]
  exact congrArg (fun f : ℕ → K => binomialShift a n f)
    (funext (exactFlowOutput_tallTree (K := K)))

theorem shiftedExactTall_eq_sum (a : K) (n : ℕ) :
    shiftedExactTall a n =
      ∑ k ∈ Finset.range (n + 1), (n.choose k : K) * a ^ (n - k) /
        ((k + 1).factorial : K) := by
  simp only [shiftedExactTall_eq_shift, binomialShift_apply, exactTall, div_eq_mul_inv, mul_assoc]

@[simp] theorem shiftedExactTall_zero_index (a : K) : shiftedExactTall a 0 = 1 := by
  simp [shiftedExactTall_eq_sum]

@[simp] theorem shiftedExactTall_zero_shift (n : ℕ) :
    shiftedExactTall (0 : K) n = ((n + 1).factorial : K)⁻¹ := by
  unfold shiftedExactTall
  rw [transform_zero]
  exact exactFlowOutput_tallTree (K := K) n

private theorem exactTall_step [CharZero K] (k : ℕ) :
    ((k : K) + 2) * exactTall K (k + 1) = exactTall K k := by
  have hc : ((k + 1 + 1 : ℕ) : K) = (k : K) + 2 := by
    simp only [Nat.cast_add, Nat.cast_one]
    ring
  have hn : (k : K) + 2 ≠ 0 := by
    rw [← hc]
    exact Nat.cast_ne_zero.mpr (Nat.succ_ne_zero (k + 1))
  have hf : ((k + 1 + 1).factorial : K) =
      ((k : K) + 2) * ((k + 1).factorial : K) := by
    rw [show (k + 1 + 1).factorial = (k + 1 + 1) * (k + 1).factorial from
      Nat.factorial_succ (k + 1), Nat.cast_mul, hc]
  simp only [exactTall, hf, mul_inv_rev]
  calc
    _ = (((k : K) + 2) * ((k : K) + 2)⁻¹) * ((k + 1).factorial : K)⁻¹ := by ac_rfl
    _ = _ := by rw [mul_inv_cancel₀ hn, one_mul]

/-- Three-term recurrence, valid also for zero shift. -/
theorem shiftedExactTall_recurrence [CharZero K] (a : K) (n : ℕ) :
    ((n : K) + 3) * shiftedExactTall a (n + 2) =
      (1 + 2 * ((n : K) + 2) * a) * shiftedExactTall a (n + 1) -
        ((n : K) + 1) * a ^ 2 * shiftedExactTall a n := by
  let f := exactTall K
  let v : ℕ → K := fun k => f (k + 1)
  let w : ℕ → K := fun k => v (k + 1)
  let U := binomialShift a n f
  let V := binomialShift a n v
  let W := binomialShift a n w
  have hstep (k : ℕ) : ((k : K) + 2) * v k = f k :=
    exactTall_step k
  have hstep₂ (k : ℕ) : ((k : K) + 3) * w k = v k := by
    change ((k : K) + 3) * exactTall K ((k + 1) + 1) = exactTall K (k + 1)
    have hs : ((k + 1 : ℕ) : K) + 2 = (k : K) + 3 := by
      simp only [Nat.cast_add, Nat.cast_one]
      ring
    simpa only [hs] using exactTall_step (K := K) (k + 1)
  have hbal : ((n : K) + 3) * W - V = a * (U - 2 * V) := by
    calc
      _ = binomialShift a n (((n : K) + 3) • w - v) := by
        rw [map_sub, map_smul, smul_eq_mul]
      _ = binomialShift a n (fun k => ((n : K) - (k : K)) * v (k + 1)) := by
        apply congrArg (fun g : ℕ → K => binomialShift a n g)
        funext k
        change ((n : K) + 3) * w k - v k = ((n : K) - (k : K)) * w k
        rw [← hstep₂ k]
        ring
      _ = a * binomialShift a n (fun k => (k : K) * v k) :=
        binomialShift_balance a n v
      _ = a * binomialShift a n (f - (2 : K) • v) := by
        apply congrArg (fun g : ℕ → K => a * binomialShift a n g)
        funext k
        change (k : K) * v k = f k - 2 * v k
        rw [← hstep k]
        ring
      _ = _ := by rw [map_sub, map_smul, smul_eq_mul]
  have hu : binomialShift a (n + 1) f = a * U + V := binomialShift_succ a n f
  have hv : binomialShift a (n + 1) v = a * V + W := binomialShift_succ a n v
  have hu₂ : binomialShift a (n + 2) f = a * (a * U + V) + (a * V + W) := by
    rw [binomialShift_succ a (n + 1) f]
    change a * binomialShift a (n + 1) f + binomialShift a (n + 1) v = _
    rw [hu, hv]
  simp only [shiftedExactTall_eq_shift]
  change ((n : K) + 3) * binomialShift a (n + 2) f =
    (1 + 2 * ((n : K) + 2) * a) * binomialShift a (n + 1) f -
      ((n : K) + 1) * a ^ 2 * U
  rw [hu₂, hu]
  calc
    _ = ((n : K) + 3) * a ^ 2 * U + 2 * ((n : K) + 3) * a * V +
      ((n : K) + 3) * W := by ring
    _ = _ := by rw [sub_eq_iff_eq_add.mp hbal]; ring

/-- A vanishing shifted reference forces the next tall reference to be
nonzero. The zero shift is allowed and has no vanishing tall reference. -/
theorem shiftedExactTall_succ_ne_zero_of_eq_zero [CharZero K] (a : K) (n : ℕ) :
    shiftedExactTall a n = 0 → shiftedExactTall a (n + 1) ≠ 0 := by
  by_cases ha : a = 0
  · subst a
    intro h _
    have hf : ((n + 1).factorial : K) ≠ 0 :=
      Nat.cast_ne_zero.mpr (Nat.factorial_ne_zero (n + 1))
    exact (inv_ne_zero hf) ((shiftedExactTall_zero_shift (K := K) n).symm.trans h)
  · induction n with
    | zero =>
      intro h _
      exact one_ne_zero ((shiftedExactTall_zero_index a).symm.trans h)
    | succ n ih =>
      intro h h'
      have h₁ : shiftedExactTall a (n + 1) = 0 := h
      have h₂ : shiftedExactTall a (n + 2) = 0 := h'
      have e := shiftedExactTall_recurrence a n
      simp only [h₁, h₂, mul_zero, zero_sub] at e
      have hn : (n : K) + 1 ≠ 0 := by
        simpa only [Nat.cast_succ] using
          (Nat.cast_ne_zero.mpr (Nat.succ_ne_zero n) : ((n.succ : ℕ) : K) ≠ 0)
      have hmul : ((n : K) + 1) * a ^ 2 * shiftedExactTall a n = 0 :=
        neg_eq_zero.mp e.symm
      exact ih ((mul_eq_zero.mp hmul).resolve_left (mul_ne_zero hn (pow_ne_zero 2 ha))) h₁

theorem shiftedExactTall_nonzero_pair [CharZero K] (a : K) (n : ℕ) :
    shiftedExactTall a n ≠ 0 ∨ shiftedExactTall a (n + 1) ≠ 0 := by
  by_cases h : shiftedExactTall a n = 0
  · exact Or.inr (shiftedExactTall_succ_ne_zero_of_eq_zero a n h)
  · exact Or.inl h

/-- If the diagonal-shifted tableau pays both orders, its unshifted matrix
cannot have two consecutive vanishing tall scalar outputs. No stage-order,
triangular-support or diagonal-nonzero premise is needed here. -/
theorem paid_shifted_tall_nonzero_pair {ι : Type*} [Fintype ι] [DecidableEq ι]
    [CharZero K] {p n : ℕ} (B : Matrix ι ι K) (b : ι → K) (γ : K)
    (ho : RKResearch.HasOrder p (B + γ • (1 : Matrix ι ι K)) b) (pay : n + 2 ≤ p) :
    (b ⬝ᵥ Φ (tallTree n.succPNat) B ≠ 0) ∨
      (b ⬝ᵥ Φ (tallTree (n + 1).succPNat) B ≠ 0) := by
  have ha := (hasOrder_add_diagonal_iff p B b γ).mp ho
  have h (k : ℕ) (hk : k + 1 ≤ p) :
      b ⬝ᵥ Φ (tallTree k.succPNat) B = shiftedExactTall (-γ) k :=
    ha _ (by simpa only [order_tallTree, Nat.succPNat_coe] using hk)
  have pay₁ : n + 1 ≤ p := by omega
  rw [h n pay₁, h (n + 1) pay]
  exact shiftedExactTall_nonzero_pair (-γ) n

end
end RKResearch.DiagonalTreeShift
