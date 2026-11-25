module

public import RKCert.ReviewedNative.NodalMaskNullity

@[expose] public section

/-! # A one-charge polynomial mask, with possibly singular readouts

Only the unmasked test width is charged on the opposite side. A measured
rank, even if it is not the full width, is added to the old Volterra image
because the latter is in the test kernel. The Volterra kernel loss itself
is exactly the same local loss as for the two-charge packet.
-/

namespace RKResearch.Certified.Graded

open Module Polynomial
open scoped Polynomial

noncomputable section

variable {K : Type*} [Field K]
variable {V : Type*} [AddCommGroup V] [Module K V]

/-- Tests are indexed by their maximum degree. The grade of the new band
uses the degree of its masked polynomial, but the annihilation budget
uses only the degree of the tests. -/
structure OneChargeMaskGeometry (L : K[X] →ₗ[K] V) (T : V →ₗ[K] V)
    (E : ℕ → Submodule K V) (M : (q : ℕ) → V →ₗ[K] (Fin (q+1) → K)) (p : ℕ) : Prop where
  band_le : ∀ j q, q ≤ j → j+1 ≤ p → polyClockBand L q ≤ E j
  step_le : ∀ j, j+3 ≤ p → (E j).map T ≤ E (j+2)
  step_silent : ∀ j q, q+j+3 ≤ p → (E j).map T ≤ (M q).ker

/-- The actual masked coefficient-to-stage map through degree q. -/
def oneChargeMaskSeed (L : K[X] →ₗ[K] V) (P : K[X]) (q : ℕ) :
    degreeLT K (q+1) →ₗ[K] V :=
  (L.comp (LinearMap.mulLeft K P)).comp (degreeLT K (q+1)).subtype

/-- The square readout on the masked band, tested only through degree q. -/
def oneChargeMaskReadout (L : K[X] →ₗ[K] V) (P : K[X])
    (M : (q : ℕ) → V →ₗ[K] (Fin (q+1) → K)) (q : ℕ) :
    degreeLT K (q+1) →ₗ[K] (Fin (q+1) → K) :=
  (M q).comp (oneChargeMaskSeed L P q)

theorem oneChargeMaskSeed_range (L : K[X] →ₗ[K] V) (P : K[X]) (q : ℕ) :
    (oneChargeMaskSeed L P q).range = maskedPolyClockBand L P q := by
  rw [oneChargeMaskSeed,LinearMap.range_comp,Submodule.range_subtype] <;> rfl

theorem oneChargeMaskReadout_range (L : K[X] →ₗ[K] V) (P : K[X])
    (M : (q : ℕ) → V →ₗ[K] (Fin (q+1) → K)) (q : ℕ) :
    (oneChargeMaskReadout L P M q).range = (maskedPolyClockBand L P q).map (M q) := by
  rw [oneChargeMaskReadout,LinearMap.range_comp,oneChargeMaskSeed_range]

private theorem packetBlock_le_oneChargeGrade
    {L : K[X] →ₗ[K] V} {T : V →ₗ[K] V} {E : ℕ → Submodule K V}
    {M : (q : ℕ) → V →ₗ[K] (Fin (q+1) → K)} {p : ℕ}
    (h : OneChargeMaskGeometry L T E M p) (P : K[X])
    {m r : ℕ} (hm : m+P.natDegree ≤ p) (hr : r+1 ≤ m) :
    maskedPolyClockBand L P (min r (m-1-r)) ≤ E (r+P.natDegree) :=
  (maskedPolyClockBand_le L P _).trans
    (h.band_le (r+P.natDegree) (min r (m-1-r)+P.natDegree)
      (Nat.add_le_add_right (Nat.min_le_left _ _) _) (by omega))

theorem maskedParityPacket_le_oneChargeGrade
    {L : K[X] →ₗ[K] V} {T : V →ₗ[K] V} {E : ℕ → Submodule K V}
    {M : (q : ℕ) → V →ₗ[K] (Fin (q+1) → K)} {p : ℕ}
    (h : OneChargeMaskGeometry L T E M p) (P : K[X]) {m : ℕ} (hm : m+P.natDegree ≤ p) :
    ∀ r, r+1 ≤ m → maskedParityPacket L T P m r ≤ E (r+P.natDegree)
  | 0, hr => by
      simpa only [maskedParityPacket,Nat.zero_min] using
        packetBlock_le_oneChargeGrade h P hm (r := 0) hr
  | 1, hr => by
      have he : m-1-1 = m-2 := by omega
      simpa only [maskedParityPacket,he] using packetBlock_le_oneChargeGrade h P hm (r := 1) hr
  | r+2, hr => by
      have hb := packetBlock_le_oneChargeGrade h P hm (r := r+2) hr
      have hW := maskedParityPacket_le_oneChargeGrade h P hm r (by omega)
      have hs := h.step_le (r+P.natDegree) (by omega)
      rw [show r+P.natDegree+2 = r+2+P.natDegree by omega] at hs
      exact sup_le hb ((Submodule.map_mono hW).trans hs)

variable [FiniteDimensional K V]

/-- A separating measurement need not be injective on the fresh summand:
its measured rank can be added to any summand killed by the measurement. -/
theorem finrank_measured_left_add_le_sup {Y : Type*} [AddCommGroup Y] [Module K Y]
    [FiniteDimensional K Y] (F : V →ₗ[K] Y) (B D : Submodule K V) (hD : D ≤ F.ker) :
    finrank K (B.map F) + finrank K D ≤ finrank K (B ⊔ D : Submodule K V) := by
  have hB := Submodule.finrank_mono (Submodule.map_mono (f := F) (le_sup_left : B ≤ B ⊔ D))
  have hK := Submodule.finrank_mono (le_inf (le_sup_right : D ≤ B ⊔ D) hD)
  let W := B ⊔ D
  let F' := F.comp W.subtype
  have hr : F'.range = W.map F := by
    dsimp only [F']
    rw [LinearMap.range_comp,Submodule.range_subtype]
  have hk : F'.ker.map W.subtype = W ⊓ F.ker := by
    dsimp only [F']
    rw [LinearMap.ker_comp,Submodule.map_comap_subtype]
  have h := F'.finrank_range_add_finrank_ker
  rw [hr,← Submodule.finrank_map_subtype_eq W F'.ker,hk] at h
  change finrank K (B.map F) ≤ finrank K (W.map F) at hB
  change finrank K D ≤ finrank K (W ⊓ F.ker : Submodule K V) at hK
  change finrank K (B.map F) + finrank K D ≤ finrank K W
  omega

/-- One paid rank step for arbitrary, possibly singular, masks. The
credit is the actual Hankel rank, not the nominal number of tests. -/
theorem maskedParityPacket_oneCharge_rankStep
    {L : K[X] →ₗ[K] V} {T : V →ₗ[K] V} {E : ℕ → Submodule K V}
    {M : (q : ℕ) → V →ₗ[K] (Fin (q+1) → K)} {p : ℕ}
    (h : OneChargeMaskGeometry L T E M p) (P : K[X])
    {m r : ℕ} (hm : m+P.natDegree ≤ p) (hr : r+3 ≤ m) :
    finrank K (oneChargeMaskReadout L P M (min (r+2) (m-1-(r+2)))).range +
      finrank K (maskedParityPacket L T P m r) ≤
      finrank K (maskedParityPacket L T P m (r+2)) +
      finrank K (maskedParityPacket L T P m r ⊓ T.ker : Submodule K V) := by
  let q := min (r+2) (m-1-(r+2))
  let W := maskedParityPacket L T P m r
  have hq : q ≤ m-1-(r+2) := Nat.min_le_right _ _
  have hW : W ≤ E (r+P.natDegree) := maskedParityPacket_le_oneChargeGrade h P hm r (by omega)
  have hs : W.map T ≤ (M q).ker :=
    (Submodule.map_mono hW).trans (h.step_silent (r+P.natDegree) q (by omega))
  have hM := finrank_measured_left_add_le_sup (M q) (maskedPolyClockBand L P q) (W.map T) hs
  rw [← oneChargeMaskReadout_range L P M q] at hM
  have hT := finrank_map_add_localKer T W
  change finrank K (oneChargeMaskReadout L P M q).range + finrank K W ≤
    finrank K (maskedPolyClockBand L P q ⊔ W.map T : Submodule K V) + finrank K (W ⊓ T.ker : Submodule K V)
  omega

private theorem oneCharge_finrank_readout_of_injective
    {L : K[X] →ₗ[K] V} {P : K[X]} {M : (q : ℕ) → V →ₗ[K] (Fin (q+1) → K)} {q : ℕ}
    (h : Function.Injective (oneChargeMaskReadout L P M q)) :
    finrank K (oneChargeMaskReadout L P M q).range = q+1 := by
  rw [LinearMap.finrank_range_of_inj h]
  exact (degreeLTEquiv K (q+1)).finrank_eq.trans (Module.finrank_fin_fun K)

/-- Full paid readout makes the mixed local-loss recurrence exact. -/
theorem maskedParityPacket_oneCharge_exact_loss
    {L : K[X] →ₗ[K] V} {T : V →ₗ[K] V} {E : ℕ → Submodule K V}
    {M : (q : ℕ) → V →ₗ[K] (Fin (q+1) → K)} {p : ℕ}
    (h : OneChargeMaskGeometry L T E M p) (P : K[X])
    {m r : ℕ} (hm : m+P.natDegree ≤ p) (hr : r+3 ≤ m)
    (hfull : Function.Injective (oneChargeMaskReadout L P M (min (r+2) (m-1-(r+2))))) :
    finrank K (maskedParityPacket L T P m (r+2)) +
      finrank K (maskedParityPacket L T P m r ⊓ T.ker : Submodule K V) =
      paidMaskWidth m (r+2) + finrank K (maskedParityPacket L T P m r) := by
  let q := min (r+2) (m-1-(r+2))
  let W := maskedParityPacket L T P m r
  let B := maskedPolyClockBand L P q
  have hins : Function.Injective (oneChargeMaskSeed L P q) := by
    intro a b e
    exact hfull (congrArg (M q) e)
  have hB : finrank K B = q+1 := by
    change finrank K (maskedPolyClockBand L P q) = q+1
    rw [← oneChargeMaskSeed_range L P q,LinearMap.finrank_range_of_inj hins]
    exact (degreeLTEquiv K (q+1)).finrank_eq.trans (Module.finrank_fin_fun K)
  have hlo := maskedParityPacket_oneCharge_rankStep h P hm hr
  rw [oneCharge_finrank_readout_of_injective hfull] at hlo
  have hsup := Submodule.finrank_sup_add_finrank_inf_eq B (W.map T)
  rw [hB] at hsup
  have hT := finrank_map_add_localKer T W
  change q+1+finrank K W ≤
    finrank K (B ⊔ W.map T : Submodule K V) + finrank K (W ⊓ T.ker : Submodule K V) at hlo
  change finrank K (B ⊔ W.map T : Submodule K V) + finrank K (W ⊓ T.ker : Submodule K V) =
    q+1+finrank K W
  omega

/-- Rank receipts indexed by the largest exponent of each paid test
block. This reduces to the uniform local census for full readouts. -/
def paidMaskRankCensus (m z : ℕ) (ranks : ℕ → ℕ) : ℕ → ℕ
  | 0 => ranks 0
  | 1 => ranks (min 1 (m-2))
  | r+2 => ranks (min (r+2) (m-1-(r+2))) + (paidMaskRankCensus m z ranks r-z)

theorem paidMaskRankCensus_le_actual
    {L : K[X] →ₗ[K] V} {T : V →ₗ[K] V} {E : ℕ → Submodule K V}
    {M : (q : ℕ) → V →ₗ[K] (Fin (q+1) → K)} {p : ℕ}
    (h : OneChargeMaskGeometry L T E M p) (P : K[X]) {m z : ℕ}
    (hm : m+P.natDegree ≤ p) (U : Submodule K V) (hU : U.map T ≤ U)
    (hseed : ∀ Q : K[X], L (P*Q) ∈ U)
    (hz : finrank K (U ⊓ T.ker : Submodule K V) ≤ z) (ranks : ℕ → ℕ)
    (hcredit : ∀ q, 2*q+1 ≤ m → ranks q ≤ finrank K (oneChargeMaskReadout L P M q).range) :
    ∀ r, r+1 ≤ m → paidMaskRankCensus m z ranks r ≤ finrank K (maskedParityPacket L T P m r)
  | 0, hr => by
      have hc := hcredit 0 (by omega)
      rw [oneChargeMaskReadout_range] at hc
      exact hc.trans (Submodule.finrank_map_le _ _)
  | 1, hr => by
      let q := min 1 (m-2)
      have hq₁ : q ≤ 1 := Nat.min_le_left _ _
      have hq₂ : q ≤ m-2 := Nat.min_le_right _ _
      have hc := hcredit q (by omega)
      rw [oneChargeMaskReadout_range] at hc
      exact hc.trans (Submodule.finrank_map_le _ _)
  | r+2, hr => by
      let q := min (r+2) (m-1-(r+2))
      let W := maskedParityPacket L T P m r
      have hq₁ : q ≤ r+2 := Nat.min_le_left _ _
      have hq₂ : q ≤ m-1-(r+2) := Nat.min_le_right _ _
      have hc := hcredit q (by omega)
      have hlo := paidMaskRankCensus_le_actual h P hm U hU hseed hz ranks hcredit r (by omega)
      have hW := maskedParityPacket_le_invariant L T P m U hU hseed r
      have hK := (Submodule.finrank_mono (inf_le_inf hW (le_refl T.ker))).trans hz
      have hT := finrank_map_add_localKer T W
      have hs := maskedParityPacket_oneCharge_rankStep h P hm hr
      change finrank K (W ⊓ T.ker : Submodule K V) ≤ z at hK
      change paidMaskRankCensus m z ranks r ≤ finrank K W at hlo
      change finrank K (oneChargeMaskReadout L P M q).range + finrank K W ≤
        finrank K (maskedParityPacket L T P m (r+2)) + finrank K (W ⊓ T.ker : Submodule K V) at hs
      change ranks q + (paidMaskRankCensus m z ranks r-z) ≤ finrank K (maskedParityPacket L T P m (r+2))
      omega

private theorem paidMaskRankCensus_full (m z : ℕ) :
    ∀ r, paidMaskRankCensus m z (fun q => q+1) r = localNullityCensus m z r
  | 0 => rfl
  | 1 => rfl
  | r+2 => by
      simp only [paidMaskRankCensus,localNullityCensus,paidMaskWidth,paidMaskRankCensus_full m z r]

/-- Numeric part of the local-nullity floor. It is exposed here without
changing the original two-charge leaf, whose private optimization was
coupled to that particular packet. -/
theorem localNullityCutFloor_of_census {m z N : ℕ} (hm : 0 < m)
    (count : ∀ r, r+1 ≤ m → localNullityCensus m z r ≤ N) :
    localNullityCutFloor m z ≤ N := by
  have hw (r : ℕ) : paidMaskWidth m r ≤ localNullityCensus m z r := by
    cases r with
    | zero => simpa only [paidMaskWidth,Nat.zero_min,zero_add,localNullityCensus] using (le_refl 1)
    | succ r =>
      cases r with
      | zero =>
        change min 1 (m-1-1)+1 ≤ min 1 (m-2)+1
        rw [show m-1-1 = m-2 by omega]
      | succ r =>
        change paidMaskWidth m (r+2) ≤ paidMaskWidth m (r+2) + (localNullityCensus m z r-z)
        omega
  by_cases hcut : 2*z < m
  · let u := m-2*z
    have hu : 0 < u := by dsimp [u]; omega
    have hshift (r : ℕ) (hr : r+1 ≤ u) : paidMaskWidth m (r+z) = z+paidMaskWidth u r := by
      change min (r+z) (m-1-(r+z))+1 = z+(min r (u-1-r)+1)
      dsimp [u] at hr ⊢
      omega
    have hinner : ∀ r, r+1 ≤ u → z+parityCensus u r ≤ localNullityCensus m z (r+z) := by
      intro r
      induction r using Nat.twoStepInduction with
      | zero =>
        intro hr
        have e := (hshift 0 hr).symm.le.trans (hw (0+z))
        simpa only [paidMaskWidth,Nat.zero_min,zero_add,parityCensus] using e
      | one =>
        intro hr
        have e := (hshift 1 hr).symm.le.trans (hw (1+z))
        have he : u-1-1 = u-2 := by omega
        simpa only [paidMaskWidth,he,parityCensus] using e
      | more r ih _ =>
        intro hr
        have hb := ih (by omega)
        rw [show r+2+z = (r+z)+2 by omega,localNullityCensus,
          show (r+z)+2 = r+2+z by omega,hshift (r+2) hr]
        have he : parityCensus u (r+2) = paidMaskWidth u (r+2)+parityCensus u r := rfl
        omega
    have bounds (r : ℕ) (hr : r+1 ≤ u) : z+parityCensus u r ≤ N :=
      (hinner r hr).trans (count (r+z) (by dsimp [u] at hr; omega))
    rw [localNullityCutFloor,if_pos hcut]
    change z + max (parityCensus u (u-1)) (parityCensus u (u-2)) ≤ N
    cases le_total (parityCensus u (u-2)) (parityCensus u (u-1)) with
    | inl h => rw [max_eq_left h]; exact bounds _ (by omega)
    | inr h => rw [max_eq_right h]; exact bounds _ (by omega)
  · let j := (m-1)/2
    have hj := (hw j).trans (count j (by dsimp [j]; omega))
    change min j (m-1-j)+1 ≤ N at hj
    rw [localNullityCutFloor,if_neg hcut]
    dsimp [j] at hj
    omega

/-- Full Hankel injection through each paid width gives the closed
local-nullity floor for the one-charge effective order. -/
theorem maskedParityPacket_oneCharge_cut_floor
    {L : K[X] →ₗ[K] V} {T : V →ₗ[K] V} {E : ℕ → Submodule K V}
    {M : (q : ℕ) → V →ₗ[K] (Fin (q+1) → K)} {p : ℕ}
    (h : OneChargeMaskGeometry L T E M p) (P : K[X]) {m z : ℕ}
    (hm : m+P.natDegree ≤ p) (hpos : 0 < m)
    (hfull : ∀ q, 2*q+1 ≤ m → Function.Injective (oneChargeMaskReadout L P M q))
    (U : Submodule K V) (hU : U.map T ≤ U) (hseed : ∀ Q : K[X], L (P*Q) ∈ U)
    (hz : finrank K (U ⊓ T.ker : Submodule K V) ≤ z) :
    localNullityCutFloor m z ≤ finrank K U := by
  apply localNullityCutFloor_of_census hpos
  intro r hr
  rw [← paidMaskRankCensus_full m z r]
  exact (paidMaskRankCensus_le_actual h P hm U hU hseed hz (fun q => q+1)
    (fun q hq => (oneCharge_finrank_readout_of_injective (hfull q hq)).ge) r hr).trans
    (Submodule.finrank_mono (maskedParityPacket_le_invariant L T P m U hU hseed r))

end
end RKResearch.Certified.Graded
