module

public import RKCert.ReviewedNative.RootMomentCuts
public import Mathlib.Algebra.Field.Basic

public section

/-! # The reviewed bushy trees as quadrature and mixed residual moments

The natural degree `k` is one less than the reviewed positive tree order.
All moments and residuals are first established in their division-free form. -/

namespace RKResearch

open FiniteRootedTree
open scoped Matrix

variable {ι R : Type*} [Fintype ι] [CommSemiring R]

/-- Raw scalar quadrature moment against an arbitrary stage vector. -/
@[expose] def stageMass (b c : ι → R) (k : ℕ) : R := b ⬝ᵥ c^k

namespace HasOrder

variable {A : Matrix ι ι R} {b : ι → R} {p : ℕ}

/-- The degree-`k` moment in the reviewed quadrature contract. -/
theorem bushy_moment (h : HasOrder p A b) (k : ℕ) (hk : k+1 ≤ p) :
    ((k+1 : ℕ) : R) * stageMass b (A *ᵥ 1) k = 1 :=
  h.hasQuadratureOrder k hk

/-- No separate characteristic hypothesis is required for paid integers. -/
theorem natCast_isUnit (h : HasOrder p A b) {n : ℕ} (hn : 0 < n) (hp : n ≤ p) :
    IsUnit (n : R) := by
  cases n with
  | zero => exact False.elim (Nat.lt_irrefl _ hn)
  | succ n => exact IsUnit.of_mul_eq_one _ (h.bushy_moment n hp)

end HasOrder

section Ring

variable {ι R : Type*} [Fintype ι] [CommRing R]

/-- The stage defect for an input monomial of degree `d`, scaled by
`d+1`; this definition is meaningful before any field is chosen. -/
@[expose] def monomialStageDefect (A : Matrix ι ι R) (d : ℕ) : ι → R :=
  fun i => ((d+1 : ℕ) : R) * (A *ᵥ (A *ᵥ (1 : ι → R))^d) i -
    (A *ᵥ (1 : ι → R)) i ^ (d+1)

namespace HasOrder

variable {A : Matrix ι ι R} {b : ι → R} {p : ℕ}

/-- A degree-`d` stage defect has zero moment against the first
`p-d-1` monomials, with no cancellation by regularity. -/
theorem monomialStageDefect_moment (h : HasOrder p A b) (d k : ℕ)
    (hp : d+1+(k+1) ≤ p) :
    stageMass (fun i => b i * monomialStageDefect A d i) (A *ᵥ 1) k = 0 := by
  have hz := h.rootStageResidual_pairing (bushyTree d.succPNat) (bushyTree k.succPNat)
    (by simpa only [order_bushyTree, Nat.succPNat_coe, Nat.succ_eq_add_one, add_comm] using hp)
  simp only [rootStageResidual, factorial_bushyTree, order_bushyTree, Φ_bushyTree,
    dotProduct, Pi.mul_apply, Pi.pow_apply, Nat.succPNat_coe, Nat.succ_eq_add_one,
    Nat.add_sub_cancel] at hz
  simpa only [stageMass, dotProduct, monomialStageDefect, Pi.pow_apply, mul_assoc] using hz

end HasOrder

end Ring

section Field

variable {ι K : Type*} [Fintype ι] [Field K]
variable {A : Matrix ι ι K} {b : ι → K} {p : ℕ}

/-- The reciprocal form is justified by the exact bushy tree itself. -/
theorem HasOrder.bushy_moment_div (h : HasOrder p A b) (k : ℕ) (hk : k+1 ≤ p) :
    stageMass b (A *ᵥ 1) k = 1 / ((k+1 : ℕ) : K) :=
  (eq_div_iff (h.natCast_isUnit (Nat.succ_pos k) hk).ne_zero).mpr
    (by simpa only [mul_comm] using h.bushy_moment k hk)

end Field

end RKResearch
