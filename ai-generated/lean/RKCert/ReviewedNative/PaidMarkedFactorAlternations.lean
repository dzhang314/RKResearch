module

public import RKCert.ReviewedNative.OneWeightOrderedSigns
public import RKCert.ReviewedNative.SquareFactorOrderedSigns
import Mathlib.Tactic.Ring
import Lean.Elab.Tactic.Omega

@[expose] public section

namespace RKCert.ReviewedNative.FiniteOrderedSigns

open Polynomial RKCert.ReviewedNative.PositiveRule19

noncomputable section
variable {K : Type*} [Field K] [LinearOrder K] [IsStrictOrderedRing K]

/-- A paid marked divisor is absorbed as a square on the finite grid.
The strict weight is independent of whether the divisor vanishes at a
grid point. The conclusion counts signs of the undoubled polynomial. -/
theorem alternations_of_paid_marked_factor {l r : K} {q D W : K[X]} {m : ℕ}
    (lr : l < r) (qn : q ≠ 0) (dn : D ≠ 0)
    (sample : q.natDegree + 2 * D.natDegree < 19)
    (budget : W.natDegree + q.natDegree + 2 * D.natDegree + (m - 1) ≤ 19)
    (positive : ∀ x ∈ Set.Ioo l r, 0 < W.eval x)
    (orth : ∀ R : K[X], R.natDegree ≤ D.natDegree + (m - 1) →
      integral l r (W * (q * D) * R) = 0) :
    HasAlternationsOn q (Set.Ioo l r) m := by
  let P := q * D^2
  have pn : P ≠ 0 := mul_ne_zero qn (pow_ne_zero 2 dn)
  have pd : P.natDegree ≤ q.natDegree + 2 * D.natDegree :=
    natDegree_mul_le_of_le le_rfl (natDegree_pow_le_of_le 2 le_rfl)
  have paid (i : Fin m) : integral l r (W * P * X^i.val) = 0 := by
    let R := D * X^i.val
    have deg : R.natDegree ≤ D.natDegree + i.val :=
      natDegree_mul_le_of_le le_rfl (natDegree_X_pow_le _)
    have rd : R.natDegree ≤ D.natDegree + (m - 1) := by
      have hi := i.isLt
      omega
    have eq : W * P * X^i.val = W * (q * D) * R := by
      dsimp only [P, R]
      ring
    rw [eq]
    exact orth R rd
  have h := grid_variation_of_positive_moments (U := W) (P := P) (m := m)
    lr pn (pd.trans_lt sample) (by omega) positive paid
  have alt : HasAlternationsOn (q * D^2) (Set.Ioo l r) m :=
    HasAlternationsOn.of_grid lr h
  exact alt.of_mul_sq

end
end RKCert.ReviewedNative.FiniteOrderedSigns
