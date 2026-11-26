module

import RKCert.ReviewedNative.PaidTreeTransport

open RKResearch Polynomial
open RKResearch.FiniteSeries (treeGrade treeHeight)
open RKResearch.ContextCompletion (PaidUnits unitMoment)
open RKResearch.ContextCompletion.PaidShift (shift pureUnaryTest)
open RKResearch.ContextCompletion.PaidTree
open scoped Polynomial FiniteRootedTree

/- Leaf and graft are the literal reviewed constructors. The base stays raw. -/
example {K : Type*} [Field K] (γ : K) (ρ : ℕ → K[X] → K[X])
    (base branch : FiniteRootedTree) (h : ℕ) :
    raw γ ρ .leaf h = 1 ∧
      raw γ ρ (base ◂ branch) h = raw γ ρ base h * shift γ (value γ ρ branch (h-1)) :=
  ⟨rfl, rfl⟩

/- The completed root reduces once; the unreduced model uses the same shift. -/
example {K : Type*} [Field K] (γ : K) (ρ : ℕ → K[X] → K[X])
    (t : FiniteRootedTree) (h : ℕ) :
    value γ ρ t h = ρ h (raw γ ρ t h) ∧
      (idealModel γ).act = shift γ ∧ (idealModel γ).readout = unitMoment :=
  ⟨rfl, rfl, rfl⟩

/- The three polynomial grade bounds have only the stated layer assumptions. -/
example {K : Type*} [Field K] (γ : K) (ρ : ℕ → K[X] → K[X]) {D : ℕ}
    (nonincrease : ∀ h : ℕ, h ≤ D → ∀ F : K[X], (ρ h F).natDegree ≤ F.natDegree)
    (t : FiniteRootedTree) (h : ℕ) (bound : h ≤ D) :
    (raw γ ρ t h).natDegree ≤ treeGrade t ∧
      (value γ ρ t h).natDegree ≤ treeGrade t ∧
      (idealColumn γ t).natDegree ≤ treeGrade t :=
  ⟨raw_natDegree_le γ ρ nonincrease t h bound, value_natDegree_le γ ρ nonincrease t h bound,
    idealColumn_natDegree_le γ t⟩

/- Consume the public weighted receipt on an actual layer and raw tree polynomial.
The saturation guard is the exact pure unary test, not an arbitrary same-degree one. -/
example {K : Type*} [Field K] {p D : ℕ} (γ : K) (ρ : ℕ → K[X] → K[X])
    (nonincrease : ∀ h : ℕ, h ≤ D → ∀ F : K[X], (ρ h F).natDegree ≤ F.natDegree)
    (t : FiniteRootedTree) (h d : ℕ) (W : K[X]) (bound : h ≤ D)
    (cut : LocalCut p γ d (ρ h)) (orderPay : d + treeGrade t < p)
    (testPay : W.natDegree + treeGrade t < p)
    (guard : d + treeGrade t + 1 = p → W = pureUnaryTest γ d) :
    unitMoment (W * value γ ρ t h) = unitMoment (W * raw γ ρ t h) :=
  cut (treeGrade t) (raw γ ρ t h) W (raw_natDegree_le γ ρ nonincrease t h bound)
    orderPay testPay guard

/- The terminal endpoint consumes all local receipts on the paid height/order band. -/
example {K : Type*} [Field K] {p D : ℕ} (units : PaidUnits K p)
    (γ : K) (ρ : ℕ → K[X] → K[X])
    (nonincrease : ∀ h : ℕ, h ≤ D → ∀ F : K[X], (ρ h F).natDegree ≤ F.natDegree)
    (fixesOne : ∀ h : ℕ, h ≤ D → ρ h 1 = 1)
    (cuts : ∀ h d : ℕ, h + d = D → 0 < h → LocalCut p γ d (ρ h))
    (t : FiniteRootedTree) (height : treeHeight t ≤ D) (order : (t.order : ℕ) ≤ p) :
    unitMoment (raw γ ρ t D) = (idealModel γ).output t ∧
      unitMoment (value γ ρ t D) = (idealModel γ).output t :=
  terminal_unitMoment_eq_of_localCuts units γ ρ nonincrease fixesOne cuts t height order

#print axioms RKResearch.ContextCompletion.PaidTree.raw
#print axioms RKResearch.ContextCompletion.PaidTree.value
#print axioms RKResearch.ContextCompletion.PaidTree.LocalCut
#print axioms RKResearch.ContextCompletion.PaidTree.raw_natDegree_le
#print axioms RKResearch.ContextCompletion.PaidTree.value_natDegree_le
#print axioms RKResearch.ContextCompletion.PaidTree.idealColumn_natDegree_le
#print axioms RKResearch.ContextCompletion.PaidTree.terminal_unitMoment_eq_of_localCuts
