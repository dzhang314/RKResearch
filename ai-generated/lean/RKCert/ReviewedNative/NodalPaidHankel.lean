module

public import RKCert.ReviewedNative.PaidMaskOneCharge
public import RKCert.ReviewedNative.MixedNodalCut

@[expose] public section

/-! # Actual paid Hankel tests of reviewed stage columns and covectors

The two measurements are the same square map on the masked coefficients.
The right-side flag used to prove silence is the ordinary annihilator
of the complementary actual defect grade. It need not equal the narrower,
unmasked dual census at the shifted degree.
-/

namespace RKResearch.Certified.Graded

open Module Polynomial FiniteRootedTree
open scoped BigOperators Matrix Polynomial

noncomputable section

variable {K : Type*} [Field K] {s p z : ℕ}
variable {A : Matrix (Fin s) (Fin s) K} {b : Fin s → K}

/-- Ordinary weighted tests through degree q; no mask is paid on their side. -/
def nodalHankelColumnTests (A : Matrix (Fin s) (Fin s) K) (b : Fin s → K) (q : ℕ) :
    (Fin s → K) →ₗ[K] (Fin (q+1) → K) :=
  LinearMap.pi (fun i : Fin (q+1) => probe A b i.val)

/-- Ordinary stage-column tests on the actual weighted measured covectors. -/
def nodalHankelRowTests (A : Matrix (Fin s) (Fin s) K) (q : ℕ) :
    ClockCovector K s →ₗ[K] (Fin (q+1) → K) :=
  LinearMap.pi (fun i : Fin (q+1) => Module.Dual.eval K (Fin s → K) (normTree A (clockTree i.val)))

/-- The square paid mask Hankel map in monomial coefficient coordinates
(`degreeLTEquiv`); its entries are the actual order moments with one mask. -/
abbrev nodalPaidHankel (A : Matrix (Fin s) (Fin s) K) (b : Fin s → K)
    (P : K[X]) (q : ℕ) : degreeLT K (q+1) →ₗ[K] (Fin (q+1) → K) :=
  oneChargeMaskReadout (nodalColumn A) P (nodalHankelColumnTests A b) q

/-- All square widths paid at one charge have full rank. -/
def NodalPaidHankelFull (A : Matrix (Fin s) (Fin s) K) (b : Fin s → K)
    (P : K[X]) (p : ℕ) : Prop :=
  ∀ q, P.natDegree+2*q+1 ≤ p → Function.Injective (nodalPaidHankel A b P q)

theorem nodalPaidHankel_apply (P : K[X]) (q : ℕ) (Q : degreeLT K (q+1)) (i : Fin (q+1)) :
    nodalPaidHankel A b P q Q i = probe A b i.val (nodalColumn A (P*(Q : K[X]))) := rfl

/-- A matrix entry of the actual Hankel, in ordinary coefficient coordinates. -/
theorem nodalPaidHankel_monomial (P : K[X]) (q : ℕ) (i j : Fin (q+1)) :
    nodalPaidHankel A b P q
        (⟨monomial j.val 1,monomial_coe_mem_degreeLT j 1⟩ : degreeLT K (q+1)) i =
      ∑ t, b t * P.eval (nodes A t) * (nodes A t)^(i.val+j.val) := by
  rw [nodalPaidHankel_apply]
  simp only [probe,row_apply,dotProduct,nodalColumn_apply,Polynomial.eval_mul,
    Polynomial.eval_monomial,one_mul,pow_add]
  apply Finset.sum_congr rfl
  intro t _
  ac_rfl

private theorem nodalRow_nodalColumn_test (Q : K[X]) (k : ℕ) :
    nodalRow A b Q (normTree A (clockTree k)) = probe A b k (nodalColumn A Q) := by
  simp only [nodalRow_apply,normTree_clockTree,probe,row_apply,dotProduct,nodalColumn_apply]
  apply Finset.sum_congr rfl
  intro i _
  ac_rfl

theorem nodalRow_hankel_eq (A : Matrix (Fin s) (Fin s) K) (b : Fin s → K)
    (P : K[X]) (q : ℕ) :
    oneChargeMaskReadout (nodalRow A b) P (nodalHankelRowTests A) q =
      nodalPaidHankel A b P q := by
  apply LinearMap.ext
  intro Q
  funext i
  change nodalRow A b (P*(Q : K[X])) (normTree A (clockTree i.val)) =
    probe A b i.val (nodalColumn A (P*(Q : K[X])))
  exact nodalRow_nodalColumn_test _ _

theorem nodalColumn_oneChargeGeometry (ho : RKResearch.HasOrder p A b) :
    OneChargeMaskGeometry (nodalColumn A) (volterra A) (treeSpace A) (nodalHankelColumnTests A b) p where
  band_le j q hq _ := by
    rw [polyClockBand_nodalColumn]
    rintro _ ⟨a,rfl⟩
    exact treeSpace_mono A hq (coeffEval_mem_treeSpace A q a)
  step_le j hj := (nodalColumn_paidGeometry ho).step_le j hj
  step_silent j q hpay := by
    rintro _ ⟨v,hv,rfl⟩
    apply LinearMap.mem_ker.mpr
    funext i
    have hi := i.isLt
    change probe A b i.val (volterra A v) = 0
    exact probe_zeroSpace ho (by omega) (volterra_treeSpace ho j (by omega) hv)

/-- The complementary actual defect constraint at a paid nominal dual grade. -/
def oneChargeDualGrade (A : Matrix (Fin s) (Fin s) K) (p j : ℕ) :
    Submodule K (ClockCovector K s) :=
  (zeroSpace A (p-1-j)).dualAnnihilator

theorem nodalRow_oneChargeGeometry (ho : RKResearch.HasOrder p A b) :
    OneChargeMaskGeometry (nodalRow A b) (volterra A).dualMap
      (oneChargeDualGrade A p) (nodalHankelRowTests A) p where
  band_le j q hq hj := by
    rw [polyClockBand_nodalRow]
    rintro _ ⟨a,rfl⟩
    change covClock A b q a ∈ (zeroSpace A (p-1-j)).dualAnnihilator
    apply (Submodule.mem_dualAnnihilator _).mpr
    intro v hv
    change (∑ i : Fin (q+1), a i • probe A b i.val) v = 0
    rw [LinearMap.sum_apply]
    apply Finset.sum_eq_zero
    intro i _
    have hi := i.isLt
    have e : probe A b i.val v = 0 := probe_zeroSpace ho (by omega) hv
    rw [LinearMap.smul_apply,e,smul_zero]
  step_le j hp := by
    rintro _ ⟨f,hf,rfl⟩
    change f ∈ (zeroSpace A (p-1-j)).dualAnnihilator at hf
    change (volterra A).dualMap f ∈ (zeroSpace A (p-1-(j+2))).dualAnnihilator
    apply (Submodule.mem_dualAnnihilator _).mpr
    intro v hv
    change v ∈ zeroSpace A (p-1-(j+2)) at hv
    have hv' : volterra A v ∈ zeroSpace A ((p-1-(j+2))+2) :=
      volterra_treeSpace ho _ (by omega) (zeroSpace_le_treeSpace A _ hv)
    rw [show (p-1-(j+2))+2 = p-1-j by omega] at hv'
    change f (volterra A v) = 0
    exact (Submodule.mem_dualAnnihilator _).mp hf _ hv'
  step_silent j q hpay := by
    rintro _ ⟨f,hf,rfl⟩
    change f ∈ (zeroSpace A (p-1-j)).dualAnnihilator at hf
    apply LinearMap.mem_ker.mpr
    funext i
    have hcol : normTree A (clockTree i.val) ∈ treeSpace A q := by
      rw [← coeffEval_single A q i]
      exact coeffEval_mem_treeSpace A q _
    have hR := volterra_treeSpace ho q (by omega) hcol
    have hR' : volterra A (normTree A (clockTree i.val)) ∈ zeroSpace A (p-1-j) :=
      zeroSpace_mono A (by omega : q+2 ≤ p-1-j) hR
    change f (volterra A (normTree A (clockTree i.val))) = 0
    exact (Submodule.mem_dualAnnihilator _).mp hf _ hR'

/-- The one-charge lower bound for actual stage columns on an invariant
target, with an exact local (rather than global) kernel premise. -/
theorem nodalColumn_oneCharge_cut (ho : RKResearch.HasOrder p A b)
    (P : K[X]) (hpos : P.natDegree < p) (hH : NodalPaidHankelFull A b P p)
    (U : Submodule K (Fin s → K)) (hU : U.map (volterra A) ≤ U)
    (hseed : ∀ Q : K[X], nodalColumn A (P*Q) ∈ U)
    (hz : finrank K (U ⊓ (volterra A).ker : Submodule K (Fin s → K)) ≤ z) :
    localNullityCutFloor (p-P.natDegree) z ≤ finrank K U :=
  maskedParityPacket_oneCharge_cut_floor (nodalColumn_oneChargeGeometry ho) P
    (m := p-P.natDegree) (by omega) (by omega) (fun q hq => hH q (by omega)) U hU hseed hz

/-- The same Hankel certificates apply to the actual weighted output
covectors in any invariant target in the honest dual. -/
theorem nodalRow_oneCharge_cut (ho : RKResearch.HasOrder p A b)
    (P : K[X]) (hpos : P.natDegree < p) (hH : NodalPaidHankelFull A b P p)
    (U : Submodule K (ClockCovector K s)) (hU : U.map (volterra A).dualMap ≤ U)
    (hseed : ∀ Q : K[X], nodalRow A b (P*Q) ∈ U)
    (hz : finrank K (U ⊓ (volterra A).dualMap.ker : Submodule K (ClockCovector K s)) ≤ z) :
    localNullityCutFloor (p-P.natDegree) z ≤ finrank K U := by
  apply maskedParityPacket_oneCharge_cut_floor (nodalRow_oneChargeGeometry ho) P
    (m := p-P.natDegree) (by omega) (by omega) _ U hU hseed hz
  intro q hq
  rw [nodalRow_hankel_eq]
  exact hH q (by omega)

end
end RKResearch.Certified.Graded
