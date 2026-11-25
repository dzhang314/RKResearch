module

public import RKCert.ReviewedNative.OrderTwentyFourClockCounted28
public import RKCert.ReviewedNative.HankelPaidAffineBasis
public import RKCert.ReviewedNative.HankelLegendreScalarTransport

@[expose] public section

/-! # The genuine order-twenty conditional four-clock endpoint

Both formerly explicit centered-data fields are derived from the
actual HasOrder contract. The final remaining hypotheses are the
physical chronological cover on the indicated side, and zero kernel
intersection on the actually counted invariant side. -/
namespace RKResearch.Certified.Graded.HankelOrderTwentyCounted28

open Module Polynomial Matrix HankelPaidMonicBasis HankelPaidAffineBasis
open HankelCenteredAtom HankelQuarticLegendre
open scoped Polynomial Matrix BigOperators

noncomputable section

variable {K : Type*} [Field K] {s k : ℕ}
variable {A : Matrix (Fin s) (Fin s) K} {b : Fin s → K}

theorem centeredStageMoment_powers_of_hasOrder (ho : RKResearch.HasOrder 20 A b) :
    CenteredPower20 (centeredStageMoment A b) := by
  change CenteredPower20 (weightedStageMoment (fun t => 2*(A *ᵥ 1) t-1) b)
  exact centered_HasOrder_powers ho

private theorem center_is_affine : (fun x : K => 2*x-1) = affineClock 2 (-1) := by
  funext x
  exact sub_eq_add_neg _ _

/-- Independent of all order and cover conditions, beyond invertibility
of 2. The whole finite mask and the actual weights are unchanged. -/
theorem centered_rank_eq_nodal (two : (2 : K) ≠ 0) (U : Finset K) (q : ℕ) :
    (hankel (maskedMoment (centeredStageMoment A b) (centeredClockMask U)) (q+1)).rank =
      finrank K (nodalPaidHankel A b (cutNodalPolynomial U) q).range := by
  classical
  have mask_eq : centeredClockMask U = affineClockMask 2 (-1) U := by
    change cutNodalPolynomial (U.image (fun x : K => 2*x-1)) =
      cutNodalPolynomial (U.image (affineClock 2 (-1)))
    rw [center_is_affine]
  have func_eq : centeredStageMoment A b =
      weightedStageMoment (fun t => affineClock 2 (-1) (nodes A t)) b := by
    change weightedStageMoment (fun t => 2*nodes A t-1) b =
      weightedStageMoment (fun t => affineClock 2 (-1) (nodes A t)) b
    rw [show (fun t => 2*nodes A t-1) = (fun t => affineClock 2 (-1) (nodes A t)) from
      funext (fun t => congrFun center_is_affine (nodes A t))]
  rw [mask_eq, func_eq]
  exact rank_affine_hankel_eq_nodal A b (d := -1) two U q

theorem centeredReadout28_of_hasOrder (ho : RKResearch.HasOrder 20 A b) (U : Finset K) :
    CenteredReadout28 A b U where
  modes := paidLegendre28_of_centeredPower20 (centeredStageMoment_powers_of_hasOrder ho)
  rankEq q _ := centered_rank_eq_nodal (A := A) (b := b)
    ((ho.natCast_isUnit (n := 2) (by decide) (by decide)).ne_zero) U q

theorem actual_eight_width_credit_ge_28_of_hasOrder (ho : RKResearch.HasOrder 20 A b)
    (U : Finset K) (u4 : U.card=4) :
    28 ≤ eightCredit (fun q => finrank K (nodalPaidHankel A b (cutNodalPolynomial U) q).range) :=
  actual_eight_width_credit_ge_28 ho U u4 (centeredReadout28_of_hasOrder ho U)

/-- Four fixed discarded clocks and zero relevant side kernel imply
at least 28 stages on the opposite counted side, in either actual
chronological orientation. This is not an unrestricted stage bound. -/
theorem chronological_cuts_ge_28
    (ho : RKResearch.HasOrder 20 A b) (tri : A.IsLowerTriangular) (le : k≤s)
    (U : Finset K) (u4 : U.card=4) :
    ((∀ i∈chronologicalHead le, nodes A i∈U) →
      finrank K (cutZeroSpace K (chronologicalHead le) ⊓ (volterra A).ker : Submodule K (Fin s → K))=0 →
      28≤s-k) ∧
    ((∀ i∉chronologicalHead le, b i≠0 → nodes A i∈U) →
      finrank K ((cutZeroSpace K (chronologicalHead le)).dualAnnihilator ⊓ (volterra A).dualMap.ker :
        Submodule K (ClockCovector K s))=0 → 28≤k) :=
  chronological_cuts_ge_28_of_centered_readout ho tri le U u4 (centeredReadout28_of_hasOrder ho U)

end
end RKResearch.Certified.Graded.HankelOrderTwentyCounted28
