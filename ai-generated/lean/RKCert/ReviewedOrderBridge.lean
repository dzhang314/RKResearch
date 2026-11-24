module

public import RKResearch.OrderConditions
public import RKCert.Tree

@[expose] public section

/-!
# Bridge between the reviewed RKResearch order predicate and RKCert

The trees have the same two constructors. The reviewed product takes its
base first; the older attachment takes its child first. Both order
predicates are denominator-cleared, so no field or characteristic-zero
assumption enters this bridge.
-/

namespace RKCert.ReviewedOrderBridge

open scoped Matrix

def toReviewed : RKCert.Tree → RKResearch.FiniteRootedTree
  | .leaf => .leaf
  | .attach c r => .butcherProduct (toReviewed r) (toReviewed c)

def ofReviewed : RKResearch.FiniteRootedTree → RKCert.Tree
  | .leaf => .leaf
  | .butcherProduct r c => .attach (ofReviewed c) (ofReviewed r)

theorem ofReviewed_toReviewed (t : RKCert.Tree) : ofReviewed (toReviewed t) = t := by
  induction t with
  | leaf => rfl
  | attach c r hc hr => simp only [toReviewed, ofReviewed, hc, hr]

theorem toReviewed_ofReviewed (t : RKResearch.FiniteRootedTree) :
    toReviewed (ofReviewed t) = t := by
  induction t with
  | leaf => rfl
  | butcherProduct r c hr hc => simp only [toReviewed, ofReviewed, hc, hr]

theorem order_toReviewed (t : RKCert.Tree) : ((toReviewed t).order : ℕ) = t.order := by
  induction t with
  | leaf => rfl
  | attach c r hc hr =>
      simp only [toReviewed, RKResearch.FiniteRootedTree.order, PNat.add_coe,
        RKCert.Tree.order, hc, hr]
      exact Nat.add_comm _ _

theorem forestFactorial_toReviewed (t : RKCert.Tree) :
    ((toReviewed t).forestFactorial : ℕ) = t.childDensityProduct := by
  induction t with
  | leaf => rfl
  | attach c r hc hr =>
      simp only [toReviewed, RKResearch.FiniteRootedTree.forestFactorial, PNat.mul_coe,
        order_toReviewed, RKCert.Tree.childDensityProduct, hc, hr]
      exact Nat.mul_comm _ _

theorem factorial_toReviewed (t : RKCert.Tree) :
    ((toReviewed t).factorial : ℕ) = t.density := by
  simp only [RKResearch.FiniteRootedTree.factorial, PNat.mul_coe, order_toReviewed,
    forestFactorial_toReviewed, RKCert.Tree.density]

section Weights

variable {R : Type*} [CommSemiring R] {s : ℕ}

theorem phi_toReviewed (A : Matrix (Fin s) (Fin s) R) (t : RKCert.Tree) :
    RKResearch.Φ (toReviewed t) A = RKCert.stageWeight A t := by
  induction t with
  | leaf => rfl
  | attach c r hc hr =>
      funext i
      simp only [toReviewed, RKResearch.Φ, RKCert.stageWeight, hc, hr,
        Pi.mul_apply, Matrix.mulVec_apply_eq_sum]
      exact mul_comm _ _

theorem weight_toReviewed (A : Matrix (Fin s) (Fin s) R) (b : Fin s → R) (t : RKCert.Tree) :
    b ⬝ᵥ RKResearch.Φ (toReviewed t) A = RKCert.weight A b t := by
  simp only [dotProduct, phi_toReviewed, RKCert.weight]

theorem orderIdentity_toReviewed (A : Matrix (Fin s) (Fin s) R) (b : Fin s → R)
    (t : RKCert.Tree) :
    (((toReviewed t).factorial : ℕ) : R) * (b ⬝ᵥ RKResearch.Φ (toReviewed t) A) =
      (t.density : R) * RKCert.weight A b t := by
  rw [factorial_toReviewed, weight_toReviewed]

/-- Reviewed and previous tree order agree for any commutative semiring and stage count. -/
theorem hasOrder_iff (A : Matrix (Fin s) (Fin s) R) (b : Fin s → R) (p : ℕ) :
    RKResearch.HasOrder p A b ↔ RKCert.HasTreeOrderAtLeast A b p := by
  constructor
  · intro h t ht
    have h' : ((toReviewed t).order : ℕ) ≤ p := by
      simpa only [order_toReviewed] using ht
    simpa only [orderIdentity_toReviewed] using h (toReviewed t) h'
  · intro h t ht
    have h' : (ofReviewed t).order ≤ p := by
      simpa only [← order_toReviewed (ofReviewed t), toReviewed_ofReviewed] using ht
    rw [← toReviewed_ofReviewed t]
    simpa only [orderIdentity_toReviewed] using h (ofReviewed t) h'

end Weights
end RKCert.ReviewedOrderBridge
