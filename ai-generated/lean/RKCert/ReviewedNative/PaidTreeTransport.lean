module

public import RKCert.ReviewedNative.PaidShiftAdjoint
public import RKCert.ReviewedNative.CommonDiagonalHeight

import Lean.Elab.Tactic.Omega

@[expose] public section

/-! # Scalar transport through paid local polynomial reductions

In the literal tree recursion the base of a graft is part of the same
root. Reduce a branch's completed root before applying the shifted
primitive, not the base's partial product at the current root. Under
local paid scalar receipts, the terminal moment agrees with the
unreduced shifted model. No interpolating hull or row is chosen here.
-/

namespace RKResearch.ContextCompletion.PaidTree

open Polynomial
open RKResearch.FiniteSeries (treeGrade treeGrade_leaf treeGrade_succ treeGrade_unary
  treeGrade_rootedSum treeHeight)
open RKResearch.ContextCompletion.PaidShift (shift shift_natDegree_le adjoint adjoint_natDegree_le
  unitMoment_shift_byParts pureUnaryTest pureUnaryTest_zero pureUnaryTest_succ)
open scoped Polynomial FiniteRootedTree

noncomputable section

variable {K : Type*} [Field K]

/-- The partial product at this root, with only completed child roots reduced. -/
def raw (γ : K) (ρ : ℕ → K[X] → K[X]) : FiniteRootedTree → ℕ → K[X]
  | .leaf, _ => 1
  | .butcherProduct base branch, h =>
    raw γ ρ base h * shift γ (ρ (h - 1) (raw γ ρ branch (h - 1)))

/-- The reduced polynomial at a completed root. -/
def value (γ : K) (ρ : ℕ → K[X] → K[X]) (t : FiniteRootedTree) (h : ℕ) : K[X] :=
  ρ h (raw γ ρ t h)

/-- The unreduced abstract polynomial model with the same forward action. -/
def idealModel (γ : K) : Model K K[X] where
  act := shift γ
  readout := unitMoment

abbrev idealColumn (γ : K) (t : FiniteRootedTree) : K[X] := (idealModel γ).column t

/-- A local scalar receipt at ancestor distance `d`. At saturation only
 the paid pure unary test is required, not every test of the same degree. -/
def LocalCut (p : ℕ) (γ : K) (d : ℕ) (reduce : K[X] → K[X]) : Prop :=
  ∀ (g : ℕ) (F W : K[X]),
    F.natDegree ≤ g → d + g < p → W.natDegree + g < p →
    (d + g + 1 = p → W = pureUnaryTest γ d) →
    unitMoment (W * reduce F) = unitMoment (W * F)

private theorem grade_graft (v u : FiniteRootedTree) :
    treeGrade (v ◂ u) = treeGrade v + (treeGrade u + 1) := by
  change treeGrade (v # (.leaf ◂ u)) = _
  rw [treeGrade_rootedSum, treeGrade_unary]

private theorem eq_leaf_of_grade_zero {t : FiniteRootedTree} (hg : treeGrade t = 0) :
    t = .leaf := by
  cases t with
  | leaf => rfl
  | butcherProduct base branch =>
    rw [grade_graft] at hg
    exfalso
    omega

/-- A degree-nonincreasing layer family preserves the literal grade bound. -/
theorem raw_natDegree_le (γ : K) (ρ : ℕ → K[X] → K[X]) {D : ℕ}
    (nonincrease : ∀ h : ℕ, h ≤ D → ∀ F : K[X], (ρ h F).natDegree ≤ F.natDegree)
    (t : FiniteRootedTree) (h : ℕ) (bound : h ≤ D) :
    (raw γ ρ t h).natDegree ≤ treeGrade t := by
  induction t generalizing h with
  | leaf => simp only [raw, Polynomial.natDegree_one, treeGrade_leaf, le_refl]
  | butcherProduct base branch ihBase ihBranch =>
    have prevBound : h - 1 ≤ D := by omega
    have childDegree : (ρ (h - 1) (raw γ ρ branch (h - 1))).natDegree ≤ treeGrade branch :=
      (nonincrease _ prevBound _).trans (ihBranch (h - 1) prevBound)
    have shiftedDegree :
        (shift γ (ρ (h - 1) (raw γ ρ branch (h - 1)))).natDegree ≤ treeGrade branch + 1 :=
      (shift_natDegree_le γ _).trans (Nat.succ_le_succ childDegree)
    rw [raw, grade_graft]
    exact Polynomial.natDegree_mul_le_of_le (ihBase h bound) shiftedDegree

theorem value_natDegree_le (γ : K) (ρ : ℕ → K[X] → K[X]) {D : ℕ}
    (nonincrease : ∀ h : ℕ, h ≤ D → ∀ F : K[X], (ρ h F).natDegree ≤ F.natDegree)
    (t : FiniteRootedTree) (h : ℕ) (bound : h ≤ D) :
    (value γ ρ t h).natDegree ≤ treeGrade t := by
  change (ρ h (raw γ ρ t h)).natDegree ≤ treeGrade t
  exact (nonincrease h bound _).trans (raw_natDegree_le γ ρ nonincrease t h bound)

theorem idealColumn_natDegree_le (γ : K) (t : FiniteRootedTree) :
    (idealColumn γ t).natDegree ≤ treeGrade t := by
  induction t with
  | leaf =>
    change (1 : K[X]).natDegree ≤ treeGrade (.leaf : FiniteRootedTree)
    simp only [Polynomial.natDegree_one, treeGrade_leaf, le_refl]
  | butcherProduct base branch ihBase ihBranch =>
    rw [grade_graft]
    change (idealColumn γ base * shift γ (idealColumn γ branch)).natDegree ≤
      treeGrade base + (treeGrade branch + 1)
    exact Polynomial.natDegree_mul_le_of_le ihBase
      ((shift_natDegree_le γ _).trans (Nat.succ_le_succ ihBranch))

private theorem weighted_raw_and_value_eq {p D : ℕ} (units : PaidUnits K p)
    (γ : K) (ρ : ℕ → K[X] → K[X])
    (nonincrease : ∀ h : ℕ, h ≤ D → ∀ F : K[X], (ρ h F).natDegree ≤ F.natDegree)
    (fixesOne : ∀ h : ℕ, h ≤ D → ρ h 1 = 1)
    (cuts : ∀ h d : ℕ, h + d = D → 0 < h → LocalCut p γ d (ρ h))
    (t : FiniteRootedTree) (h d : ℕ) (W : K[X]) (layer : h + d = D)
    (height : treeHeight t ≤ h) (orderPay : d + treeGrade t < p)
    (testPay : W.natDegree + treeGrade t < p)
    (guard : d + treeGrade t + 1 = p → W = pureUnaryTest γ d) :
    unitMoment (W * raw γ ρ t h) = unitMoment (W * idealColumn γ t) ∧
      unitMoment (W * value γ ρ t h) = unitMoment (W * idealColumn γ t) := by
  induction t generalizing h d W with
  | leaf =>
    have hD : h ≤ D := by omega
    constructor
    · rfl
    · change unitMoment (W * ρ h 1) = unitMoment (W * 1)
      rw [fixesOne h hD]
  | butcherProduct base branch ihBase ihBranch =>
    have heights : max (treeHeight base) (treeHeight branch + 1) ≤ h := height
    have baseHeight := (max_le_iff.mp heights).1
    have branchStep := (max_le_iff.mp heights).2
    have hpos : 0 < h := by omega
    have hD : h ≤ D := by omega
    have prevD : h - 1 ≤ D := by omega
    have branchHeight : treeHeight branch ≤ h - 1 := by omega
    have branchLayer : (h - 1) + (d + 1) = D := by omega
    have grade := grade_graft base branch
    have baseOrder : d + treeGrade base < p := by omega
    have branchOrder : (d + 1) + treeGrade branch < p := by omega
    let B : K[X] := value γ ρ branch (h - 1)
    let V : K[X] := idealColumn γ base
    let A : K[X] := idealColumn γ branch
    have bDeg : B.natDegree ≤ treeGrade branch :=
      value_natDegree_le γ ρ nonincrease branch (h - 1) prevD
    have vDeg : V.natDegree ≤ treeGrade base := idealColumn_natDegree_le γ base
    have aDeg : A.natDegree ≤ treeGrade branch := idealColumn_natDegree_le γ branch
    have jDeg : (shift γ B).natDegree ≤ treeGrade branch + 1 :=
      (shift_natDegree_le γ B).trans (Nat.succ_le_succ bDeg)

    -- The same-root base is compared before replacing the branch value.
    let baseTest : K[X] := W * shift γ B
    have baseTestDeg : baseTest.natDegree ≤ W.natDegree + (treeGrade branch + 1) :=
      Polynomial.natDegree_mul_le_of_le (le_refl W.natDegree) jDeg
    have basePay : baseTest.natDegree + treeGrade base < p := by omega
    have baseGuard : d + treeGrade base + 1 = p → baseTest = pureUnaryTest γ d := by
      intro sat
      exfalso
      omega
    have baseEq := (ihBase h d baseTest layer baseHeight baseOrder basePay baseGuard).1

    -- The genuine child is compared after moving the shift to its test.
    let test : K[X] := W * V
    have testDeg : test.natDegree ≤ W.natDegree + treeGrade base :=
      Polynomial.natDegree_mul_le_of_le (le_refl W.natDegree) vDeg
    have branchTestDeg : (adjoint γ test).natDegree ≤ (W.natDegree + treeGrade base) + 1 :=
      (adjoint_natDegree_le γ test).trans (Nat.succ_le_succ testDeg)
    have branchPay : (adjoint γ test).natDegree + treeGrade branch < p := by omega
    have branchGuard : (d + 1) + treeGrade branch + 1 = p →
        adjoint γ test = pureUnaryTest γ (d + 1) := by
      intro sat
      have baseZero : treeGrade base = 0 := by omega
      have parentSat : d + treeGrade (base ◂ branch) + 1 = p := by omega
      have baseLeaf : base = .leaf := eq_leaf_of_grade_zero baseZero
      have vOne : V = 1 := by
        change idealColumn γ base = idealColumn γ .leaf
        exact congrArg (idealColumn γ) baseLeaf
      change adjoint γ (W * V) = pureUnaryTest γ (d + 1)
      rw [vOne, mul_one, guard parentSat, pureUnaryTest_succ]
    have branchEq := (ihBranch (h - 1) (d + 1) (adjoint γ test) branchLayer branchHeight
      branchOrder branchPay branchGuard).2
    have paidB : test.natDegree + B.natDegree + 1 < p := by omega
    have paidA : test.natDegree + A.natDegree + 1 < p := by omega

    have rawEq : unitMoment (W * raw γ ρ (base ◂ branch) h) =
        unitMoment (W * idealColumn γ (base ◂ branch)) := by
      change unitMoment (W * (raw γ ρ base h * shift γ B)) = unitMoment (W * (V * shift γ A))
      calc
        _ = unitMoment (baseTest * raw γ ρ base h) :=
          congrArg (fun F : K[X] => unitMoment F)
            ((mul_assoc W (raw γ ρ base h) (shift γ B)).symm.trans
              (mul_right_comm W (raw γ ρ base h) (shift γ B)))
        _ = unitMoment (baseTest * V) := baseEq
        _ = unitMoment (test * shift γ B) :=
          congrArg (fun F : K[X] => unitMoment F) (mul_right_comm W (shift γ B) V)
        _ = unitMoment (adjoint γ test * B) := unitMoment_shift_byParts units γ test B paidB
        _ = unitMoment (adjoint γ test * A) := branchEq
        _ = unitMoment (test * shift γ A) := (unitMoment_shift_byParts units γ test A paidA).symm
        _ = _ := congrArg (fun F : K[X] => unitMoment F) (mul_assoc W V (shift γ A))

    refine ⟨rawEq, ?_⟩
    change unitMoment (W * ρ h (raw γ ρ (base ◂ branch) h)) =
      unitMoment (W * idealColumn γ (base ◂ branch))
    have rawDeg := raw_natDegree_le γ ρ nonincrease (base ◂ branch) h hD
    exact (cuts h d layer hpos (treeGrade (base ◂ branch)) (raw γ ρ (base ◂ branch) h)
      W rawDeg orderPay testPay guard).trans rawEq

/-- All local cuts may act together. Only paid scalar terminal readouts
are compared; nothing asserts that the polynomial columns agree. -/
theorem terminal_unitMoment_eq_of_localCuts {p D : ℕ} (units : PaidUnits K p)
    (γ : K) (ρ : ℕ → K[X] → K[X])
    (nonincrease : ∀ h : ℕ, h ≤ D → ∀ F : K[X], (ρ h F).natDegree ≤ F.natDegree)
    (fixesOne : ∀ h : ℕ, h ≤ D → ρ h 1 = 1)
    (cuts : ∀ h d : ℕ, h + d = D → 0 < h → LocalCut p γ d (ρ h))
    (t : FiniteRootedTree) (height : treeHeight t ≤ D) (order : (t.order : ℕ) ≤ p) :
    unitMoment (raw γ ρ t D) = unitMoment (idealColumn γ t) ∧
      unitMoment (value γ ρ t D) = unitMoment (idealColumn γ t) := by
  have gOrder := treeGrade_succ t
  have pay : treeGrade t < p := by omega
  have rowPay : 0 + treeGrade t < p := by simpa only [Nat.zero_add] using pay
  have testPay : (1 : K[X]).natDegree + treeGrade t < p := by
    simpa only [Polynomial.natDegree_one, Nat.zero_add] using pay
  have guard : 0 + treeGrade t + 1 = p → (1 : K[X]) = pureUnaryTest γ 0 :=
    fun _ => (pureUnaryTest_zero γ).symm
  simpa only [one_mul] using
    weighted_raw_and_value_eq units γ ρ nonincrease fixesOne cuts t D 0 1
      (Nat.add_zero D) height rowPay testPay guard

end

end RKResearch.ContextCompletion.PaidTree
