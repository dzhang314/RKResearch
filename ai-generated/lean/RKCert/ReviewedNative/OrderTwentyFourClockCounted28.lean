module

public import RKCert.ReviewedNative.HankelQuarticLegendreJoin
public import RKCert.ReviewedNative.PaidHankelFactorCorank

import Lean.Elab.Tactic.Omega
import Mathlib.Tactic.LinearCombination

@[expose] public section

/-! # Actual order-twenty causal spend of all eight quartic ranks

This source is receipt-conditional until the field data transport and
literal centered readout comparison are supplied. It uses the checked
factor corank and the checked causal geometry, not a full-rank premise.
No unrestricted order-twenty stage statement is made. -/
namespace RKResearch.Certified.Graded.HankelOrderTwentyCounted28

open Module Matrix Polynomial HankelPaidMonicBasis HankelPaidRestart
open HankelQuarticLegendre
open scoped Polynomial Matrix BigOperators

noncomputable section

variable {K : Type*} [Field K] {s k : ℕ}
variable {A : Matrix (Fin s) (Fin s) K} {b : Fin s → K}

def center (x : K) : K := 2*x-1

/-- The genuine signed quadrature functional on centered stage clocks. -/
def centeredStageMoment (A : Matrix (Fin s) (Fin s) K) (b : Fin s → K) : K[X] →ₗ[K] K :=
  ∑ t, b t • (Polynomial.aeval (center (nodes A t))).toLinearMap

/-- The actual monic quartic at the images of the specified fixed clocks. -/
def centeredClockMask (U : Finset K) : K[X] := by
  classical
  exact cutNodalPolynomial (U.image center)

private theorem centered_mask_monic (U : Finset K) : (centeredClockMask U).Monic := by
  classical
  unfold centeredClockMask cutNodalPolynomial
  exact monic_prod_of_monic _ _ (fun x _ => monic_X_sub_C x)

private theorem centered_mask_degree (U : Finset K) (two : (2:K)≠0) :
    (centeredClockMask U).natDegree=U.card := by
  classical
  have inj : Function.Injective (center (K := K)) := by
    intro x y e
    change (2:K)*x-1=(2:K)*y-1 at e
    apply mul_left_cancel₀ two
    linear_combination e
  unfold centeredClockMask
  rw [natDegree_cutNodalPolynomial,Finset.card_image_of_injective _ inj]

/-- The two precise field/coordinate bridges still to distill from
`HasOrder` and the integer data. Both refer to literal tableau clocks
and the literal fixed set, not to an arbitrary comparison matrix. -/
structure CenteredReadout28 (A : Matrix (Fin s) (Fin s) K) (b : Fin s → K) (U : Finset K) : Prop where
  modes : PaidLegendre28 (centeredStageMoment A b)
  rankEq : ∀ q≤7,
    (hankel (maskedMoment (centeredStageMoment A b) (centeredClockMask U)) (q+1)).rank =
      finrank K (nodalPaidHankel A b (cutNodalPolynomial U) q).range

def eightCredit (c : ℕ → ℕ) : ℕ := c 0+c 1+c 2+c 3+c 4+c 5+c 6+c 7

/-- Apply the generic Legendre exclusion to the actual eight readouts.
The bound on each corank is proved from the accepted factored theorem;
there is no assumed high rank or exclusion callback. -/
theorem actual_eight_width_credit_ge_28 (ho : RKResearch.HasOrder 20 A b)
    (U : Finset K) (u4 : U.card=4) (Cen : CenteredReadout28 A b U) :
    28 ≤ eightCredit (fun q => finrank K (nodalPaidHankel A b (cutNodalPolynomial U) q).range) := by
  let J := maskedMoment (centeredStageMoment A b) (centeredClockMask U)
  have cap : ∀ w≤8, nullity J w≤2 := by
    intro w hw
    cases w with
    | zero => simp only [nullity,Nat.zero_sub]; decide
    | succ q =>
      change q+1 - (hankel (maskedMoment (centeredStageMoment A b) (centeredClockMask U)) (q+1)).rank ≤ 2
      rw [Cen.rankEq q (by omega)]
      let F := nodalPaidHankel A b (cutNodalPolynomial U) q
      change q+1 - finrank K F.range ≤ 2
      letI : FiniteDimensional K (degreeLT K (q+1)) := (degreeLTEquiv K (q+1)).symm.finiteDimensional
      have h := F.finrank_range_add_finrank_ker
      have dim : finrank K (degreeLT K (q+1)) = q+1 :=
        (degreeLTEquiv K (q+1)).finrank_eq.trans (Module.finrank_fin_fun K)
      rw [dim] at h
      have hk := nodalPaidHankel_cutNodalPolynomial_corank_le (q := q) ho U (by omega)
      change finrank K F.ker ≤ (U.card+1)/2 at hk
      rw [u4] at hk
      omega
  have pd : (centeredClockMask U).natDegree=4 :=
    (centered_mask_degree U (Cen.modes.units 2 (by decide) (by decide))).trans u4
  have h := full_paid_rank_ge_28 Cen.modes (centered_mask_monic U) pd cap
  rw [Cen.rankEq 0 (by decide),Cen.rankEq 1 (by decide),Cen.rankEq 2 (by decide),Cen.rankEq 3 (by decide),
    Cen.rankEq 4 (by decide),Cen.rankEq 5 (by decide),Cen.rankEq 6 (by decide),Cen.rankEq 7 (by decide)] at h
  exact h

private theorem census_fourteen (c : ℕ → ℕ) : eightCredit c=paidMaskRankCensus 16 0 c 14 := by
  have h : paidMaskRankCensus 16 0 c 14 =
      c 1+(c 3+(c 5+(c 7+(c 6+(c 4+(c 2+c 0)))))) := by
    first | rfl | simp [paidMaskRankCensus, Nat.min_def]
  rw [h,eightCredit]
  omega

private theorem spend_on_invariant
    {V : Type*} [AddCommGroup V] [Module K V] [FiniteDimensional K V]
    {L : K[X] →ₗ[K] V} {T : V →ₗ[K] V} {E : ℕ → Submodule K V}
    {M : (q : ℕ) → V →ₗ[K] (Fin (q+1) → K)}
    (G : OneChargeMaskGeometry L T E M 20) (P : K[X]) (degree4 : P.natDegree=4)
    (W : Submodule K V) (inv : W.map T≤W)
    (seed : ∀ Q : K[X], L (P*Q)∈W) (ker0 : finrank K (W⊓T.ker : Submodule K V)=0)
    (c : ℕ → ℕ) (measured : ∀ q, 2*q+1≤16 → c q≤finrank K (oneChargeMaskReadout L P M q).range)
    (credit : 28≤eightCredit c) : 28≤finrank K W := by
  rw [census_fourteen] at credit
  have rank := paidMaskRankCensus_le_actual G P (m := 16) (z := 0) (by omega)
    W inv seed ker0.le c measured 14 (by decide)
  have sub := maskedParityPacket_le_invariant L T P 16 W inv seed 14
  exact credit.trans (rank.trans (Submodule.finrank_mono sub))

/-- Conditional 28 on the actual counted side. Prefix cover means
all discarded rows; suffix cover means all individually active rows.
The explicit `Cen` field/coordinate bridge is the remaining source
obligation, not an unverified hypothesis hidden in the rank compiler. -/
theorem chronological_cuts_ge_28_of_centered_readout
    (ho : RKResearch.HasOrder 20 A b) (tri : A.IsLowerTriangular) (le : k≤s)
    (U : Finset K) (u4 : U.card=4) (Cen : CenteredReadout28 A b U) :
    ((∀ i∈chronologicalHead le, nodes A i∈U) →
      finrank K (cutZeroSpace K (chronologicalHead le) ⊓ (volterra A).ker : Submodule K (Fin s → K))=0 →
      28≤s-k) ∧
    ((∀ i∉chronologicalHead le, b i≠0 → nodes A i∈U) →
      finrank K ((cutZeroSpace K (chronologicalHead le)).dualAnnihilator ⊓ (volterra A).dualMap.ker :
        Submodule K (ClockCovector K s))=0 → 28≤k) := by
  let S := chronologicalHead le
  let W := cutZeroSpace K S
  let P := cutNodalPolynomial U
  let c (q : ℕ) := finrank K (nodalPaidHankel A b P q).range
  have pd : P.natDegree=4 := (natDegree_cutNodalPolynomial U).trans u4
  have credit : 28≤eightCredit c := actual_eight_width_credit_ge_28 ho U u4 Cen
  have inv : W.map (volterra A)≤W := cutZeroSpace_volterra_le tri S (chronologicalHead_downward le)
  constructor
  · intro cover ker0
    have seed (Q : K[X]) : nodalColumn A (P*Q)∈W := by
      apply (mem_cutZeroSpace S _).mpr
      intro i hi
      have vanish : P.eval (nodes A i)=0 := cutNodalPolynomial_eval_zero (cover i hi)
      simp only [nodalColumn_apply,Polynomial.eval_mul,vanish,zero_mul]
    have res := spend_on_invariant (nodalColumn_oneChargeGeometry ho) P pd W inv seed ker0 c
      (fun q _ => Nat.le_refl (c q)) credit
    simpa only [W,S,finrank_cutZeroSpace,chronologicalHead_card] using res
  · intro cover ker0
    have invDual : W.dualAnnihilator.map (volterra A).dualMap≤W.dualAnnihilator := by
      rintro _ ⟨f,hf,rfl⟩
      apply (Submodule.mem_dualAnnihilator _).mpr
      intro v hv
      exact (Submodule.mem_dualAnnihilator _).mp hf _ (inv ⟨v,hv,rfl⟩)
    have seed (Q : K[X]) : nodalRow A b (P*Q)∈W.dualAnnihilator := by
      apply (Submodule.mem_dualAnnihilator _).mpr
      intro v hv
      rw [nodalRow_apply]
      apply Finset.sum_eq_zero
      intro i _
      by_cases hi : i∈S
      · rw [(mem_cutZeroSpace S _).mp hv i hi,mul_zero]
      · by_cases hb : b i=0
        · simp only [hb,zero_mul]
        · have root : P.eval (nodes A i)=0 := cutNodalPolynomial_eval_zero (cover i hi hb)
          simp only [Polynomial.eval_mul,root,zero_mul,mul_zero]
    have measured (q : ℕ) (_ : 2*q+1≤16) :
        c q≤finrank K (oneChargeMaskReadout (nodalRow A b) P (nodalHankelRowTests A) q).range := by
      rw [nodalRow_hankel_eq]
    have res := spend_on_invariant (nodalRow_oneChargeGeometry ho) P pd W.dualAnnihilator
      invDual seed ker0 c measured credit
    simpa only [W,S,finrank_cutZeroSpace_annihilator,chronologicalHead_card] using res

end
end RKResearch.Certified.Graded.HankelOrderTwentyCounted28
