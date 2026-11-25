module

public import RKCert.ReviewedNative.NodalMaskParity

@[expose] public section

/-! # Exact local kernel loss in the actual nodal packet -/

namespace RKResearch.Certified.Graded

open Module Polynomial
open scoped Polynomial

noncomputable section

variable {K : Type*} [Field K]
variable {V : Type*} [AddCommGroup V] [Module K V]

/-- Only the paid grade geometry is retained. The step is allowed to be
singular globally, and its local kernel is charged by rank-nullity. -/
structure PaidMaskGeometry (L : K[X] →ₗ[K] V) (T : V →ₗ[K] V)
    (E : ℕ → Submodule K V) (p : ℕ) : Prop where
  band_injective : ∀ q, 2*q+1 ≤ p → Function.Injective (L.comp (degreeLT K (q+1)).subtype)
  band_le : ∀ j q, q ≤ j → q+j+1 ≤ p → polyClockBand L q ≤ E j
  step_le : ∀ j, j+3 ≤ p → (E j).map T ≤ E (j+2)
  separated : ∀ j q, q ≤ j+2 → q+j+3 ≤ p → polyClockBand L q ⊓ (E j).map T = ⊥

theorem PaidPolyClockSystem.toPaidMaskGeometry {L : K[X] →ₗ[K] V} {T : V →ₗ[K] V}
    {E : ℕ → Submodule K V} {p : ℕ} (h : PaidPolyClockSystem L T E p) :
    PaidMaskGeometry L T E p :=
  ⟨h.band_injective,h.band_le,h.step_le,h.separated⟩

/-- Width of an affordable full shifted clock block. -/
abbrev paidMaskWidth (m r : ℕ) := min r (m-1-r)+1

/-- Grade-by-grade lower rank under a uniform upper bound on the
kernel intersection. Natural subtraction is the exact clipping. -/
def localNullityCensus (m z : ℕ) : ℕ → ℕ
  | 0 => 1
  | 1 => min 1 (m-2)+1
  | r+2 => paidMaskWidth m (r+2) + (localNullityCensus m z r-z)

/-- Closed optimized uniform loss bound, at positive effective m. -/
def localNullityCutFloor (m z : ℕ) : ℕ :=
  if 2*z < m then z+nonsingularStageFloor (m-2*z) else (m+1)/2

theorem localNullityCutFloor_zero {m : ℕ} (hm : 0 < m) :
    localNullityCutFloor m 0 = nonsingularStageFloor m := by
  simp [localNullityCutFloor,hm]

private theorem maskedBlock_receipt {L : K[X] →ₗ[K] V} {T : V →ₗ[K] V}
    {E : ℕ → Submodule K V} {p : ℕ} (h : PaidMaskGeometry L T E p)
    (P : K[X]) (hP : P ≠ 0) {m r : ℕ} (hm : p = m+2*P.natDegree) (hr : r+1 ≤ m) :
    finrank K (maskedPolyClockBand L P (min r (m-1-r))) = paidMaskWidth m r ∧
      maskedPolyClockBand L P (min r (m-1-r)) ≤ E (r+P.natDegree) := by
  have h₁ : min r (m-1-r) ≤ r := Nat.min_le_left _ _
  have h₂ : min r (m-1-r) ≤ m-1-r := Nat.min_le_right _ _
  exact ⟨finrank_maskedPolyClockBand L P hP _ (h.band_injective _ (by omega)),
    (maskedPolyClockBand_le L P _).trans (h.band_le _ _ (by omega) (by omega))⟩

theorem maskedParityPacket_le_paidGrade {L : K[X] →ₗ[K] V} {T : V →ₗ[K] V}
    {E : ℕ → Submodule K V} {p : ℕ} (h : PaidMaskGeometry L T E p)
    (P : K[X]) (hP : P ≠ 0) {m : ℕ} (hm : p = m+2*P.natDegree) :
    ∀ r, r+1 ≤ m → maskedParityPacket L T P m r ≤ E (r+P.natDegree)
  | 0, hr => by
      have hb := (maskedBlock_receipt h P hP hm (r := 0) hr).2
      rw [Nat.zero_min] at hb
      exact hb
  | 1, hr => by
      have hb := (maskedBlock_receipt h P hP hm (r := 1) hr).2
      rw [show m-1-1 = m-2 by omega] at hb
      exact hb
  | r+2, hr => by
      have hb := (maskedBlock_receipt h P hP hm (r := r+2) hr).2
      have hW := maskedParityPacket_le_paidGrade h P hP hm r (by omega)
      have hstep := h.step_le (r+P.natDegree) (by omega)
      have hp' : (r+P.natDegree)+2 = (r+2)+P.natDegree := by omega
      rw [hp'] at hstep
      exact sup_le hb ((Submodule.map_mono hW).trans hstep)

variable [FiniteDimensional K V]

/-- Rank-nullity on a selected domain, with the kernel left in the
original coordinates. This is independent of invariance. -/
theorem finrank_map_add_localKer (T : V →ₗ[K] V) (W : Submodule K V) :
    finrank K (W.map T) + finrank K (W ⊓ T.ker : Submodule K V) = finrank K W := by
  let f := T.comp W.subtype
  have hr : f.range = W.map T := by
    dsimp only [f]
    rw [LinearMap.range_comp,Submodule.range_subtype]
  have hk : f.ker.map W.subtype = W ⊓ T.ker := by
    dsimp only [f]
    rw [LinearMap.ker_comp,Submodule.map_comap_subtype]
  have hd := f.finrank_range_add_finrank_ker
  rw [hr] at hd
  rw [← hk,Submodule.finrank_map_subtype_eq]
  exact hd

/-- The exact old-image rank is debited only by the actual local
kernel. The direct paid split does not depend on injectivity. -/
theorem maskedParityPacket_exact_local_loss
    {L : K[X] →ₗ[K] V} {T : V →ₗ[K] V} {E : ℕ → Submodule K V} {p : ℕ}
    (h : PaidMaskGeometry L T E p) (P : K[X]) (hP : P ≠ 0)
    {m r : ℕ} (hm : p = m+2*P.natDegree) (hr : r+3 ≤ m) :
    finrank K (maskedParityPacket L T P m (r+2)) +
      finrank K (maskedParityPacket L T P m r ⊓ T.ker : Submodule K V) =
      paidMaskWidth m (r+2) + finrank K (maskedParityPacket L T P m r) := by
  let q := min (r+2) (m-1-(r+2))
  let d := P.natDegree
  let B := maskedPolyClockBand L P q
  let W := maskedParityPacket L T P m r
  have hq : q ≤ r+2 := Nat.min_le_left _ _
  have hw : q ≤ m-1-(r+2) := Nat.min_le_right _ _
  have hp' : q+d+(r+d)+3 ≤ p := by
    change p = m+2*d at hm
    omega
  have hB : B ≤ polyClockBand L (q+d) := maskedPolyClockBand_le L P q
  have hW : W ≤ E (r+d) := maskedParityPacket_le_paidGrade h P hP hm r (by omega)
  have hsep : B ⊓ W.map T = ⊥ := by
    have hpaid := h.separated (r+d) (q+d) (by omega) hp'
    exact le_antisymm ((inf_le_inf hB (Submodule.map_mono hW)).trans hpaid.le) bot_le
  have hdim := Submodule.finrank_sup_add_finrank_inf_eq B (W.map T)
  have hwidth : finrank K B = paidMaskWidth m (r+2) :=
    (maskedBlock_receipt h P hP hm (r := r+2) hr).1
  rw [hsep,finrank_bot,add_zero,hwidth] at hdim
  have hker := finrank_map_add_localKer T W
  change finrank K (↥(B ⊔ W.map T : Submodule K V)) +
    finrank K (W ⊓ T.ker : Submodule K V) = paidMaskWidth m (r+2) + finrank K W
  omega

theorem localNullityCensus_le_maskedRank
    {L : K[X] →ₗ[K] V} {T : V →ₗ[K] V} {E : ℕ → Submodule K V} {p : ℕ}
    (h : PaidMaskGeometry L T E p) (P : K[X]) (hP : P ≠ 0)
    {m z : ℕ} (hm : p = m+2*P.natDegree)
    (U : Submodule K V) (hU : U.map T ≤ U) (hseed : ∀ Q : K[X], L (P*Q) ∈ U)
    (hz : finrank K (U ⊓ T.ker : Submodule K V) ≤ z) :
    ∀ r, r+1 ≤ m → localNullityCensus m z r ≤ finrank K (maskedParityPacket L T P m r)
  | 0, hr => by
      have h₀ := (maskedBlock_receipt h P hP hm (r := 0) hr).1
      change finrank K (maskedPolyClockBand L P (min 0 (m-1-0))) = min 0 (m-1-0) + 1 at h₀
      rw [Nat.zero_min] at h₀
      exact h₀.ge
  | 1, hr => by
      have h₁ := (maskedBlock_receipt h P hP hm (r := 1) hr).1
      have he : m-1-1 = m-2 := by omega
      change finrank K (maskedPolyClockBand L P (min 1 (m-1-1))) = min 1 (m-1-1) + 1 at h₁
      rw [he] at h₁
      exact h₁.ge
  | r+2, hr => by
      have hlo := localNullityCensus_le_maskedRank h P hP hm U hU hseed hz r (by omega)
      have hW := maskedParityPacket_le_invariant L T P m U hU hseed r
      have hk := (Submodule.finrank_mono (inf_le_inf hW (le_refl T.ker))).trans hz
      have hstep := maskedParityPacket_exact_local_loss h P hP hm (r := r) hr
      have hker := finrank_map_add_localKer T (maskedParityPacket L T P m r)
      change paidMaskWidth m (r+2) + (localNullityCensus m z r-z) ≤ _
      omega

private theorem width_le_localNullityCensus (m z r : ℕ) :
    paidMaskWidth m r ≤ localNullityCensus m z r := by
  cases r with
  | zero => simp only [paidMaskWidth,Nat.zero_min,zero_add,localNullityCensus,le_rfl]
  | succ r =>
    cases r with
    | zero =>
      change min 1 (m-1-1)+1 ≤ min 1 (m-2)+1
      rw [show m-1-1 = m-2 by omega]
    | succ r =>
      change paidMaskWidth m (r+2) ≤
        paidMaskWidth m (r+2) + (localNullityCensus m z r-z)
      omega

private theorem maskWidth_shift (m z r : ℕ) (hr : r+1 ≤ m-2*z) :
    paidMaskWidth m (r+z) = z+paidMaskWidth (m-2*z) r := by
  change min (r+z) (m-1-(r+z))+1 = z+(min r (m-2*z-1-r)+1)
  omega

private theorem localNullityCensus_inner (m z : ℕ) :
    ∀ r, r+1 ≤ m-2*z →
      z+parityCensus (m-2*z) r ≤ localNullityCensus m z (r+z)
  | 0, hr => by
      have h := width_le_localNullityCensus m z (0+z)
      rw [maskWidth_shift m z 0 hr] at h
      simpa only [paidMaskWidth,Nat.zero_min,zero_add,parityCensus] using h
  | 1, hr => by
      have h := width_le_localNullityCensus m z (1+z)
      rw [maskWidth_shift m z 1 hr] at h
      have he : m-2*z-1-1 = m-2*z-2 := by omega
      simpa only [paidMaskWidth,he,parityCensus] using h
  | r+2, hr => by
      have h := localNullityCensus_inner m z r (by omega)
      rw [show r+2+z = (r+z)+2 by omega,localNullityCensus,
        show (r+z)+2 = r+2+z by omega,maskWidth_shift m z (r+2) hr]
      have he : parityCensus (m-2*z) (r+2) =
        paidMaskWidth (m-2*z) (r+2)+parityCensus (m-2*z) r := rfl
      omega

/-- The closed local-nullity floor follows by choosing an affordable
grade, without assuming that the maximum lies at an outer endpoint. -/
theorem maskedParityPacket_localNullity_cut_floor
    {L : K[X] →ₗ[K] V} {T : V →ₗ[K] V} {E : ℕ → Submodule K V} {p : ℕ}
    (h : PaidMaskGeometry L T E p) (P : K[X]) (hP : P ≠ 0)
    {m z : ℕ} (hm : p = m+2*P.natDegree) (hpos : 0 < m)
    (U : Submodule K V) (hU : U.map T ≤ U) (hseed : ∀ Q : K[X], L (P*Q) ∈ U)
    (hz : finrank K (U ⊓ T.ker : Submodule K V) ≤ z) :
    localNullityCutFloor m z ≤ finrank K U := by
  have count (r : ℕ) (hr : r+1 ≤ m) : localNullityCensus m z r ≤ finrank K U :=
    (localNullityCensus_le_maskedRank h P hP hm U hU hseed hz r hr).trans
      (Submodule.finrank_mono (maskedParityPacket_le_invariant L T P m U hU hseed r))
  by_cases hcut : 2*z < m
  · let u := m-2*z
    have hu : 0 < u := by dsimp [u]; omega
    have h₁ := (localNullityCensus_inner m z (u-1) (by omega)).trans
      (count (u-1+z) (by dsimp [u]; omega))
    have h₂ := (localNullityCensus_inner m z (u-2) (by omega)).trans
      (count (u-2+z) (by dsimp [u]; omega))
    rw [localNullityCutFloor,if_pos hcut]
    change z + max (parityCensus u (u-1)) (parityCensus u (u-2)) ≤ _
    rcases le_total (parityCensus u (u-2)) (parityCensus u (u-1)) with hh | hh
    · rw [max_eq_left hh]
      exact h₁
    · rw [max_eq_right hh]
      exact h₂
  · let j := (m-1)/2
    have hJ := (width_le_localNullityCensus m z j).trans (count j (by dsimp [j]; omega))
    rw [localNullityCutFloor,if_neg hcut]
    change min j (m-1-j)+1 ≤ _ at hJ
    dsimp [j] at hJ
    omega

end
end RKResearch.Certified.Graded
