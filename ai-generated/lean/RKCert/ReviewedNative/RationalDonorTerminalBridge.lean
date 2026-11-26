module

public import RKCert.ReviewedNative.RationalDonorChain
public import RKCert.ReviewedNative.RationalERKTerminalMass
import Lean.Elab.Tactic.Omega

@[expose] public section

/-! The paid baseline from actual final-bank donors. A quiet contrast with
nonzero gain is separate from final-bank purity. -/

namespace RKResearch.Certified.RationalDonorTerminalBridge

open RKResearch RKResearch.Certified.Graded
open RKResearch.Certified.Graded.TerminalDeformation
open RKResearch.Certified.RationalDonorChain
open RKResearch.Certified.RationalTerminalMass
open RKResearch.Certified.RationalMoments
open scoped BigOperators FiniteRootedTree Matrix

/-- The quadratic primitive defect is a difference of two actual
order-three normalized stage columns. -/
theorem quadratic_eq_native_difference {ι : Type*} [Fintype ι]
    (A : Matrix ι ι ℚ) :
    monomialStageDefect A 1 =
      normTree A (.leaf ◂ clockTree 1) - normTree A (clockTree 2) := by
  have hclock : normTree A (clockTree 1) = nodes A := by
    simpa only [pow_one] using (normTree_clockTree A 1)
  have htall : normTree A (.leaf ◂ clockTree 1) =
      ((1 + 1 : ℕ) : ℚ) • mat A (nodes A) := by
    simpa only [order_clockTree, hclock] using
      (normTree_unary A (clockTree 1))
  have hbush : normTree A (clockTree 2) = fun i => (nodes A i) ^ 2 :=
    normTree_clockTree A 2
  funext i
  simp only [htall, hbush, monomialStageDefect, Pi.sub_apply, Pi.smul_apply,
    smul_eq_mul, mat_apply, nodes, pow_one]

theorem quadratic_zero_of_native_pure_three {ι : Type*} [Fintype ι]
    (A : Matrix ι ι ℚ) (i : ι) (x : ℚ)
    (pure : ∀ t, ord t ≤ 3 → normTree A t i = x ^ (ord t - 1)) :
    monomialStageDefect A 1 i = 0 := by
  have ht : ord (.leaf ◂ clockTree 1) = 3 := by
    simp only [ord, FiniteRootedTree.order, PNat.add_coe, PNat.one_coe, order_clockTree]
  have hb : ord (clockTree 2) = 3 := order_clockTree 2
  have tall : normTree A (.leaf ◂ clockTree 1) i = x ^ 2 := by
    simpa only [ht] using (pure (.leaf ◂ clockTree 1) (by omega))
  have bush : normTree A (clockTree 2) i = x ^ 2 := by
    simpa only [hb] using (pure (clockTree 2) (by omega))
  simp only [quadratic_eq_native_difference, Pi.sub_apply, tall, bush, sub_self]

/-- A contrast need only be checked on the actual constant and clock
columns to establish quietness through two. Its gain is a separate test. -/
theorem quiet_two_of_row_moments {ι : Type*} [Fintype ι]
    (A : Matrix ι ι ℚ) (η : ι → ℚ)
    (mass : row η (1 : ι → ℚ) = 0) (clock : row η (nodes A) = 0) :
    Quiet A η 2 := by
  intro t paid
  cases t with
  | leaf =>
    simpa only [normTree_leaf] using mass
  | butcherProduct u v =>
    change ((u ◂ v).order : ℕ) ≤ 2 at paid
    simp only [FiniteRootedTree.order, PNat.add_coe] at paid
    have hu : 1 ≤ (u.order : ℕ) := u.order.pos
    have hv : 1 ≤ (v.order : ℕ) := v.order.pos
    have hule : (u.order : ℕ) ≤ 1 :=
      Nat.le_of_add_le_add_right ((Nat.add_le_add_left hv (u.order : ℕ)).trans paid)
    have hvle : (v.order : ℕ) ≤ 1 :=
      Nat.le_of_add_le_add_left ((Nat.add_le_add_right hu (v.order : ℕ)).trans paid)
    have eu : u = .leaf := (coe_order_eq_one_iff_leaf u).mp (le_antisymm hule hu)
    have ev : v = .leaf := (coe_order_eq_one_iff_leaf v).mp (le_antisymm hvle hv)
    have hc : normTree A (.leaf ◂ .leaf) = nodes A := by
      simp only [normTree_unary, normTree_leaf, FiniteRootedTree.order,
        PNat.one_coe, Nat.cast_one, one_smul, mat_apply, nodes]
    simpa only [eu, ev, hc] using clock

/-- Arbitrary physical donors suffice. Tree payment, moment interpolation
and the quadratic zero test have separate budgets. -/
theorem baseline_paid_of_native_donors {ι σ : Type*} [Fintype ι] [Fintype σ]
    {n p r : ℕ} {A : Matrix ι ι ℚ} {e : Fin n → ι} {z : Fin n → ℚ}
    (inj : Function.Injective z) (c : σ → ℚ)
    (momentCap : p ≤ n + 1) (donorPay : p ≤ r + 1) (quadPay : 3 ≤ r)
    (pure : ∀ t, ord t ≤ r → ∀ j, normTree A t (e j) = z j ^ (ord t - 1)) :
    RowLaw A (primitiveRows e z c) c p ∧
      ∀ x, row (primitiveRows e z c x) (monomialStageDefect A 1) = 0 := by
  have kill (j : Fin n) : monomialStageDefect A 1 (e j) = 0 :=
    quadratic_zero_of_native_pure_three A (e j) (z j)
      (fun t ht => pure t (ht.trans quadPay) j)
  refine ⟨primitiveRows_rowLaw (p := p) (e := e) inj c momentCap ?_, ?_⟩
  · intro t ht j
    exact pure t (by omega) j
  · intro x
    exact primitiveRows_baseline_zero (e := e) (z := z) c _ kill x

abbrev CoreIndex (s d n : ℕ) := Fin (s + (d + 1) * n)

/-- The last bank is selected at its actual chronological indices. -/
def lastBankIndex (s d n : ℕ) (j : Fin n) : CoreIndex s d n :=
  chronology s d n (Sum.inr ⟨Fin.last d, j⟩)

@[simp] theorem lastBankIndex_val (s d n : ℕ) (j : Fin n) :
    (lastBankIndex s d n j).val = s + (j.val + n * d) := rfl

theorem lastBankIndex_injective (s d n : ℕ) :
    Function.Injective (lastBankIndex s d n) := by
  intro i j eq
  apply Fin.ext
  have he : (lastBankIndex s d n i).val = (lastBankIndex s d n j).val :=
    congrArg Fin.val eq
  simp only [lastBankIndex_val] at he
  omega

variable {s d n r₀ p : ℕ}
variable {A₀ : Matrix (Fin s) (Fin s) ℚ} {D₀ : Matrix (Fin n) (Fin s) ℚ}
variable {z : Fin n → ℚ}

theorem actual_lastBank_pure (inj : Function.Injective z) (base₀ : RowLaw A₀ D₀ z r₀)
    (chainCap : r₀ + d ≤ n + 1) (t : FiniteRootedTree) (paid : ord t ≤ r₀ + d)
    (j : Fin n) :
    normTree (chainFin (d := d) A₀ D₀ z) t (lastBankIndex s d n j) =
      z j ^ (ord t - 1) :=
  chainFin_pure (d := d) inj base₀ chainCap ⟨Fin.last d, j⟩ t paid

/-- The measured chain discharges precisely the terminal baseline
RowLaw and the zero baseline action on the actual quadratic defect. -/
theorem chain_lastBank_baseline {σ : Type*} [Fintype σ]
    (inj : Function.Injective z) (base₀ : RowLaw A₀ D₀ z r₀) (c : σ → ℚ)
    (chainCap : r₀ + d ≤ n + 1) (momentCap : p ≤ n + 1)
    (donorPay : p ≤ r₀ + d + 1) (quadPay : 3 ≤ r₀ + d) :
    let A := chainFin (d := d) A₀ D₀ z
    let D := primitiveRows (lastBankIndex s d n) z c
    RowLaw A D c p ∧ ∀ x, row (D x) (monomialStageDefect A 1) = 0 :=
  baseline_paid_of_native_donors (p := p) (r := r₀ + d)
    (A := chainFin (d := d) A₀ D₀ z) (e := lastBankIndex s d n) inj c
    momentCap donorPay quadPay
    (fun t ht j => actual_lastBank_pure (d := d) inj base₀ chainCap t ht j)

/-- No contrast constructed solely by lifting weights from the pure last
bank can provide the required nonzero gain. -/
theorem lastBank_lift_has_zero_gain
    (inj : Function.Injective z) (base₀ : RowLaw A₀ D₀ z r₀)
    (chainCap : r₀ + d ≤ n + 1) (quadPay : 3 ≤ r₀ + d) (w : Fin n → ℚ) :
    let A := chainFin (d := d) A₀ D₀ z
    row (liftDonorWeights (lastBankIndex s d n) w) (monomialStageDefect A 1) = 0 := by
  let A := chainFin (d := d) A₀ D₀ z
  change row (liftDonorWeights (lastBankIndex s d n) w) (monomialStageDefect A 1) = 0
  rw [liftDonorWeights_action]
  apply Finset.sum_eq_zero
  intro j _
  have kill : monomialStageDefect A 1 (lastBankIndex s d n j) = 0 :=
    quadratic_zero_of_native_pure_three A (lastBankIndex s d n j) (z j)
      (fun t ht => actual_lastBank_pure (d := d) inj base₀ chainCap t (ht.trans quadPay) j)
  rw [kill, mul_zero]

/-- Conditional application of the measured terminal-mass theorem.
The actual quiet contrast, nonzero gain and paid target mass remain
inputs; no global strictness or order existence is inferred from purity. -/
theorem realize_with_lastBank {m : ℕ} {c : Fin m → ℚ}
    (p4 : 4 ≤ p) (inj : Function.Injective z) (base₀ : RowLaw A₀ D₀ z r₀)
    (chainCap : r₀ + d ≤ n + 1) (momentCap : p ≤ n + 1)
    (donorPay : p ≤ r₀ + d + 1) (outInj : Function.Injective c) (outCap : p ≤ m)
    (η : CoreIndex s d n → ℚ)
    (quiet : Quiet (chainFin (d := d) A₀ D₀ z) η 2)
    (gain : row η (monomialStageDefect (chainFin (d := d) A₀ D₀ z) 1) ≠ 0)
    (ω : Fin m → ℚ) (ann : ∀ k, k + 4 ≤ p → powerMass c ω k = 0) :
    let A := chainFin (d := d) A₀ D₀ z
    let D := primitiveRows (lastBankIndex s d n) z c
    let β := primitiveWeights c 1
    let lam := naturalSamples p
    let a := fun x => ω x / row η (monomialStageDefect A 1)
    let M := terminalMatrix A D η lam
    let b := terminalWeight (ι := CoreIndex s d n) (copyWeights lam β a)
    RKResearch.HasOrder p M b ∧
      ∀ x, clockMass M b (mat M (monomialStageDefect M 1)) x =
        ∑ j, if c j = x then ω j else 0 := by
  have quadPay : 3 ≤ r₀ + d := by omega
  have paid := chain_lastBank_baseline (d := d) (p := p) inj base₀ c
    chainCap momentCap donorPay quadPay
  have quadrature (k : ℕ) (hk : k + 1 ≤ p) :
      ((k + 1 : ℕ) : ℚ) * powerMass c (primitiveWeights c 1) k = 1 :=
    primitiveWeights_quadrature (p := p) outInj outCap k hk
  exact realize_quadratic_outgoing_mass (p := p) p4 paid.1 quiet (naturalSamples_injective p)
    paid.2 gain ann quadrature

end RKResearch.Certified.RationalDonorTerminalBridge
