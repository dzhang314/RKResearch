module

public import Mathlib.Algebra.Polynomial.Div

@[expose] public section

/-! # Scalar cancellation at a monic polynomial hull

Below the hull degree the remainder is unchanged. At the hull
degree the discarded part is a scalar multiple of the hull, so
any linear moment annihilating the hull ignores that part.
-/

namespace RKResearch.ContextCompletion.MonicHull

open Polynomial
open scoped Polynomial

variable {K : Type*} [Field K] {F H : K[X]}

/-- A strict polynomial degree cutoff leaves the input unchanged. -/
theorem modByMonic_eq_self_of_natDegree_lt (monic : H.Monic)
    (below : F.natDegree < H.natDegree) : F %ₘ H = F :=
  (Polynomial.modByMonic_eq_self_iff monic).mpr (Polynomial.degree_lt_degree below)

private theorem quotient_natDegree_zero (monic : H.Monic)
    (bound : F.natDegree ≤ H.natDegree) : (F /ₘ H).natDegree = 0 :=
  (Polynomial.natDegree_divByMonic F monic).trans (Nat.sub_eq_zero_of_le bound)

/-- Through the hull degree, the discarded remainder term stays on one
constant-multiple line, with its scalar read from the actual quotient. -/
theorem sub_modByMonic_eq_smul_of_natDegree_le (monic : H.Monic)
    (bound : F.natDegree ≤ H.natDegree) :
    F - F %ₘ H = ((F /ₘ H).coeff 0) • H := by
  have constant : F /ₘ H = Polynomial.C ((F /ₘ H).coeff 0) :=
    Polynomial.eq_C_of_natDegree_eq_zero (quotient_natDegree_zero monic bound)
  have decomp : H * (F /ₘ H) + F %ₘ H = F :=
    (add_comm (H * (F /ₘ H)) (F %ₘ H)).trans (Polynomial.modByMonic_add_div F H)
  calc
    F - F %ₘ H = H * (F /ₘ H) := (eq_sub_iff_add_eq.mpr decomp).symm
    _ = H * Polynomial.C ((F /ₘ H).coeff 0) :=
      congrArg (fun Q : K[X] => H * Q) constant
    _ = ((F /ₘ H).coeff 0) • H :=
      (mul_comm H (Polynomial.C ((F /ₘ H).coeff 0))).trans
        (Polynomial.smul_eq_C_mul (p := H) ((F /ₘ H).coeff 0)).symm

/-- A linear moment that kills the monic hull is unchanged by reduction
of any input whose natural degree is at most the hull degree. -/
theorem linearMoment_modByMonic_eq_of_natDegree_le
    {V : Type*} [AddCommGroup V] [Module K V] (m : K[X] →ₗ[K] V)
    (monic : H.Monic) (bound : F.natDegree ≤ H.natDegree) (kills : m H = 0) :
    m (F %ₘ H) = m F := by
  have zero : m (F - F %ₘ H) = 0 := by
    rw [sub_modByMonic_eq_smul_of_natDegree_le monic bound, map_smul, kills, smul_zero]
  rw [map_sub] at zero
  exact (sub_eq_zero.mp zero).symm

/-- Below the cutoff the actual error polynomial is zero, with no moment input. -/
example (monic : H.Monic) (below : F.natDegree < H.natDegree) :
    F - F %ₘ H = 0 := by
  rw [modByMonic_eq_self_of_natDegree_lt monic below, sub_self]

/-- At saturation a nonzero input has a nonzero constant multiplier,
but its linear moment is preserved when the hull is killed. -/
example (m : K[X] →ₗ[K] K) (monic : H.Monic) (nonzero : F ≠ 0)
    (sat : F.natDegree = H.natDegree) (kills : m H = 0) :
    F.leadingCoeff ≠ 0 ∧ F - F %ₘ H = F.leadingCoeff • H ∧
      m (F %ₘ H) = m F := by
  have degrees : H.degree = F.degree := by
    rw [Polynomial.degree_eq_natDegree monic.ne_zero, Polynomial.degree_eq_natDegree nonzero, sat]
  have qzero : (F /ₘ H).natDegree = 0 := quotient_natDegree_zero monic sat.le
  have scalar : (F /ₘ H).coeff 0 = F.leadingCoeff := by
    calc
      (F /ₘ H).coeff 0 = (F /ₘ H).leadingCoeff := by
        rw [Polynomial.leadingCoeff, qzero]
      _ = F.leadingCoeff := Polynomial.leadingCoeff_divByMonic_of_monic monic degrees.le
  refine ⟨Polynomial.leadingCoeff_ne_zero.mpr nonzero, ?_,
    linearMoment_modByMonic_eq_of_natDegree_le m monic sat.le kills⟩
  rw [sub_modByMonic_eq_smul_of_natDegree_le monic sat.le, scalar]

end RKResearch.ContextCompletion.MonicHull
