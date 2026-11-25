module

public import RKCert.ReviewedNative.SDIRK118SubfieldAssembly

import Mathlib.Tactic.FinCases

@[expose] public section

noncomputable section

namespace RKResearch.Certified.PaidDefectBridge.SDIRK118.Subfield

open ClaimPin ScalarBindings LiteralAssembly
open RKResearch.Certified.PaidDefectBridge.ForwardChart
open RKResearch.Certified.PaidDefectBridge.ReverseChart (shiftAt shiftAt_apply lastNormRow)
open RKResearch.Certified.DiagonalTwin (contractMatrix)
open RKResearch.Certified.Graded (mergeCoefficient)
open scoped BigOperators Matrix

variable (F : IntermediateField ℚ ℝ)

private theorem two : (2 : ℝ) ∈ F := ofNat_mem F 2
private theorem three : (3 : ℝ) ∈ F := ofNat_mem F 3
private theorem half : (1/2 : ℝ) ∈ F := F.div_mem F.one_mem (two F)

theorem aAt_mem {s : ℝ} (hs : s ∈ F) : aAt s ∈ F :=
  F.div_mem (F.add_mem F.one_mem hs) (two F)

theorem zAt_mem {s : ℝ} (hs : s ∈ F) : zAt s ∈ F :=
  F.add_mem (aAt_mem F hs) hs

private theorem hAt_mem {s : ℝ} (hs : s ∈ F) : hAt s ∈ F :=
  F.sub_mem (aAt_mem F hs) F.one_mem

private theorem g1At_mem {s : ℝ} (hs : s ∈ F) : g1At s ∈ F :=
  F.sub_mem (F.add_mem (half F) (hAt_mem F hs))
    (F.div_mem (pow_mem (hAt_mem F hs) 2) (two F))

private theorem etaAt_mem {s : ℝ} (hs : s ∈ F) : etaAt s ∈ F :=
  F.mul_mem (two F) (g1At_mem F hs)

private theorem Bs_mem {s : ℝ} (hs : s ∈ F) : Bs s ∈ F :=
  F.mul_mem (F.sub_mem F.one_mem hs) (F.sub_mem (three F) hs)

private theorem qSeed_mem {s T : ℝ} (hs : s ∈ F) (hT : T ∈ F) : qSeed s T ∈ F :=
  F.add_mem (F.sub_mem (pow_mem hT 2) (F.mul_mem (F.add_mem hs (three F)) hT)) hs

private theorem Ld_mem {s η T : ℝ} (hs : s ∈ F) (hη : η ∈ F) (hT : T ∈ F) :
    Ld s η T ∈ F :=
  F.sub_mem (F.mul_mem (F.sub_mem (Bs_mem F hs) F.one_mem) (F.sub_mem hT F.one_mem))
    (F.mul_mem hη (F.sub_mem (F.add_mem hT F.one_mem) (F.mul_mem (two F) hs)))

private theorem gdAt_mem {s η d : ℝ} (hs : s ∈ F) (hη : η ∈ F) (hd : d ∈ F) :
    gdAt s η d ∈ F :=
  F.div_mem (F.mul_mem (F.mul_mem (F.div_mem hη (two F)) (F.sub_mem hd hs))
    (qSeed_mem F hs hd)) (Ld_mem F hs hη hd)

private theorem Ud_mem {d gd : ℝ} (hd : d ∈ F) (hg : gd ∈ F) :
    Ud d gd ∈ F :=
  F.add_mem (F.sub_mem hg hd) (F.div_mem (pow_mem hd 2) (two F))

private theorem Vd_mem {d η gd : ℝ} (hd : d ∈ F) (hη : η ∈ F) (hg : gd ∈ F) :
    Vd d η gd ∈ F := by
  have hi : 1+d+(d-1)/η ∈ F :=
    F.add_mem (F.add_mem F.one_mem hd) (F.div_mem (F.sub_mem hd F.one_mem) hη)
  exact F.add_mem
    (F.sub_mem (F.mul_mem (F.mul_mem (F.div_mem (two F) (three F)) hi) hg) (pow_mem hd 2))
    (F.div_mem (pow_mem hd 3) (three F))

theorem linearFactor_coeffs {x : ℝ} (hx : x ∈ F) : CoeffsIn F (linearFactor x) :=
  coeffs_sub F (coeffs_X F) (coeffs_C F hx)

theorem cubic_coeffs {u v w : ℝ} (hu : u ∈ F) (hv : v ∈ F) (hw : w ∈ F) :
    CoeffsIn F (cubic u v w) :=
  coeffs_mul F (coeffs_mul F (linearFactor_coeffs F hu) (linearFactor_coeffs F hv))
    (linearFactor_coeffs F hw)

private theorem Jpoly_coeffs {s t : ℝ} (hs : s ∈ F) (ht : t ∈ F) :
    CoeffsIn F (Jpoly s t) :=
  cubic_coeffs F hs ht F.one_mem

private theorem Zpoly_coeffs {s t : ℝ} (hs : s ∈ F) (ht : t ∈ F) :
    CoeffsIn F (Zpoly s t) :=
  coeffs_mul F (linearFactor_coeffs F (aAt_mem F hs)) (Jpoly_coeffs F hs ht)

theorem mu_mem (M : MonomialBasis) (hm : standardPowers M)
    {s t : ℝ} (hs : s ∈ F) (ht : t ∈ F) (j : ℕ) : μ M s t j ∈ F :=
  avg_mem F M hm (zAt_mem F hs)
    (coeffs_mul F (coeffs_pow F (coeffs_X F) j) (Zpoly_coeffs F hs ht))

theorem momentDet_mem (M : MonomialBasis) (hm : standardPowers M)
    {s t : ℝ} (hs : s ∈ F) (ht : t ∈ F) : momentDet M s t ∈ F :=
  F.sub_mem (F.mul_mem (mu_mem F M hm hs ht 0) (mu_mem F M hm hs ht 2))
    (pow_mem (mu_mem F M hm hs ht 1) 2)

theorem beta0_mem (M : MonomialBasis) (hm : standardPowers M)
    {s t : ℝ} (hs : s ∈ F) (ht : t ∈ F) : beta0 M s t ∈ F := by
  have h := mu_mem F M hm hs ht
  exact F.div_mem (F.sub_mem (F.mul_mem (h 1) (h 3)) (pow_mem (h 2) 2))
    (momentDet_mem F M hm hs ht)

theorem beta1_mem (M : MonomialBasis) (hm : standardPowers M)
    {s t : ℝ} (hs : s ∈ F) (ht : t ∈ F) : beta1 M s t ∈ F := by
  have h := mu_mem F M hm hs ht
  exact F.div_mem (F.sub_mem (F.mul_mem (h 1) (h 2)) (F.mul_mem (h 0) (h 3)))
    (momentDet_mem F M hm hs ht)

private theorem bStar_mem (M : MonomialBasis) (hm : standardPowers M)
    {s t c : ℝ} (hs : s ∈ F) (ht : t ∈ F) (hc : c ∈ F) : bStar M s t c ∈ F :=
  F.sub_mem (F.neg_mem (beta1_mem F M hm hs ht)) hc

private theorem ellAvg_mem (M : MonomialBasis) (hm : standardPowers M)
    {s t c : ℝ} (hs : s ∈ F) (ht : t ∈ F) (hc : c ∈ F) (j : ℕ) :
    ellAvg M s t c j ∈ F := by
  have hJ := Jpoly_coeffs F hs ht
  have h1 := coeffs_mul F (coeffs_pow F (coeffs_X F) j) (linearFactor_coeffs F (aAt_mem F hs))
  have h2 := coeffs_mul F h1 (linearFactor_coeffs F hc)
  exact avg_mem F M hm (zAt_mem F hs)
    (coeffs_mul F h2 (coeffs_sub F (primitive_coeffs F M hm hJ) hJ))

private theorem selectorQuadAt_mem (M : MonomialBasis) (hm : standardPowers M)
    {s t c T : ℝ} (hs : s ∈ F) (ht : t ∈ F) (hc : c ∈ F) (hT : T ∈ F) :
    selectorQuadAt M s t c T ∈ F := by
  have hz := zAt_mem F hs
  have h := ellAvg_mem F M hm hs ht hc
  exact F.mul_mem (F.add_mem (F.sub_mem hT hz) hc)
    (F.sub_mem (F.mul_mem (h 0) (F.sub_mem hz hT)) (h 1))

theorem affineAt_mem (M : MonomialBasis) (hm : standardPowers M)
    {s t c T : ℝ} (hs : s ∈ F) (ht : t ∈ F) (hc : c ∈ F) (hT : T ∈ F) :
    affineAt M s t c T ∈ F := by
  let a := aAt s
  let r := s/3
  let η := etaAt s
  let j := selectorQuadAt M s t c
  have ha : a ∈ F := aAt_mem F hs
  have hr : r ∈ F := F.div_mem hs (three F)
  have hη : η ∈ F := etaAt_mem F hs
  have hj : ∀ x : ℝ, x ∈ F → j x ∈ F := fun _ hx => selectorQuadAt_mem F M hm hs ht hc hx
  have h1r := F.sub_mem F.one_mem hr
  have har := F.sub_mem ha hr
  have h1a := F.sub_mem F.one_mem ha
  have hμ : η*Bs s-3*(Bs s-1-η) ∈ F :=
    F.sub_mem (F.mul_mem hη (Bs_mem F hs))
      (F.mul_mem (three F) (F.sub_mem (F.sub_mem (Bs_mem F hs) F.one_mem) hη))
  have hA : ((T-a)*j 1/(1-r)-(T-1)*j a/(a-r))/(1-a) ∈ F :=
    F.div_mem (F.sub_mem (F.div_mem (F.mul_mem (F.sub_mem hT ha) (hj 1 F.one_mem)) h1r)
      (F.div_mem (F.mul_mem (F.sub_mem hT F.one_mem) (hj a ha)) har)) h1a
  exact F.sub_mem (F.div_mem (F.mul_mem (Ld_mem F hs hη hT) (hj r hr)) (F.mul_mem h1r har))
    (F.mul_mem (F.div_mem hμ (three F)) hA)

theorem dAt_mem (M : MonomialBasis) (hm : standardPowers M)
    {s t c : ℝ} (hs : s ∈ F) (ht : t ∈ F) (hc : c ∈ F) : dAt M s t c ∈ F := by
  have h0 := affineAt_mem F M hm hs ht hc F.zero_mem
  have h1 := affineAt_mem F M hm hs ht hc F.one_mem
  exact F.div_mem (F.neg_mem h0) (F.sub_mem h1 h0)

theorem atOne_coeffs (M : MonomialBasis) (hm : standardPowers M)
    {x : ℝ} (hx : x ∈ F) {P : Polynomial ℝ} (hP : CoeffsIn F P) :
    CoeffsIn F (atOne M x P) :=
  coeffs_smul F (F.inv_mem (evalAt_mem F M hm hx hP)) hP

theorem card6_coeffs {y : Fin 6 → ℝ} (hy : VecIn F y) (i : Fin 6) :
    CoeffsIn F (card6 y i) := by
  unfold card6
  apply coeffs_smul F
  · apply F.inv_mem
    exact F.prod_mem fun j _ => F.sub_mem (hy i) (hy j)
  · apply coeffs_prod F
    intro j _
    exact linearFactor_coeffs F (hy j)

theorem scalarWeights_mem (M : MonomialBasis) (hm : standardPowers M)
    {y : Fin 6 → ℝ} (hy : VecIn F y) : VecIn F (scalarWeights M y) :=
  fun i => mean_mem F M hm (card6_coeffs F hy i)

theorem yAt_mem (M : MonomialBasis) (hm : standardPowers M)
    {s t c : ℝ} (hs : s ∈ F) (ht : t ∈ F) (hc : c ∈ F) : VecIn F (yAt M s t c) := by
  have hz := zAt_mem F hs
  intro i
  fin_cases i
  · exact F.div_mem F.one_mem hz
  · exact F.div_mem (aAt_mem F hs) hz
  · exact F.div_mem hs hz
  · exact F.div_mem ht hz
  · exact F.div_mem (bStar_mem F M hm hs ht hc) hz
  · exact F.div_mem hc hz

private theorem uAt_mem {s d : ℝ} (hs : s ∈ F) (hd : d ∈ F) : VecIn F (uAt s d) := by
  intro i
  fin_cases i
  · exact F.one_mem
  · exact aAt_mem F hs
  · exact hs
  · exact hd

private theorem gAt_mem {s g3 : ℝ} (hs : s ∈ F) (hg : g3 ∈ F) : VecIn F (gAt s g3) := by
  intro i
  fin_cases i
  · exact half F
  · exact g1At_mem F hs
  · exact F.zero_mem
  · exact hg

abbrev QuadIn (q : Quad ℝ) : Prop := q.1 ∈ F ∧ q.2.1 ∈ F ∧ q.2.2 ∈ F

private theorem quad_add {p q : Quad ℝ} (hp : QuadIn F p) (hq : QuadIn F q) :
    QuadIn F (p + q) :=
  ⟨F.add_mem hp.1 hq.1, F.add_mem hp.2.1 hq.2.1, F.add_mem hp.2.2 hq.2.2⟩

private theorem quad_sub {p q : Quad ℝ} (hp : QuadIn F p) (hq : QuadIn F q) :
    QuadIn F (p - q) :=
  ⟨F.sub_mem hp.1 hq.1, F.sub_mem hp.2.1 hq.2.1, F.sub_mem hp.2.2 hq.2.2⟩

private theorem quad_smul {a : ℝ} {q : Quad ℝ} (ha : a ∈ F) (hq : QuadIn F q) :
    QuadIn F (a • q) :=
  ⟨F.mul_mem ha hq.1, F.mul_mem ha hq.2.1, F.mul_mem ha hq.2.2⟩

private theorem ell_mem {u v w : ℝ} (hu : u ∈ F) (hv : v ∈ F) (hw : w ∈ F) :
    QuadIn F (ell u v w) := by
  have hd := F.mul_mem (F.sub_mem hu hv) (F.sub_mem hu hw)
  exact ⟨F.div_mem (F.mul_mem hv hw) hd, F.div_mem (F.neg_mem (F.add_mem hv hw)) hd, F.inv_mem hd⟩

private theorem interp_mem {u v : V ℝ} (hu : VecIn F u) (hv : VecIn F v) :
    QuadIn F (interp u v) := by
  rw [interp_apply]
  exact quad_add F (quad_add F
    (quad_smul F (hv 0) (ell_mem F (hu 0) (hu 1) (hu 2)))
    (quad_smul F (hv 1) (ell_mem F (hu 1) (hu 0) (hu 2))))
    (quad_smul F (hv 2) (ell_mem F (hu 2) (hu 0) (hu 1)))

private theorem ev_mem {x : ℝ} {q : Quad ℝ} (hx : x ∈ F) (hq : QuadIn F q) : ev x q ∈ F := by
  rw [ev_apply]
  exact F.add_mem (F.add_mem hq.1 (F.mul_mem hq.2.1 hx)) (F.mul_mem hq.2.2 (pow_mem hx 2))

private theorem prim_mem {x : ℝ} {q : Quad ℝ} (hx : x ∈ F) (hq : QuadIn F q) :
    prim x q ∈ F :=
  F.add_mem (F.add_mem (F.mul_mem hq.1 hx) (F.mul_mem hq.2.1 (F.div_mem (pow_mem hx 2) (two F))))
    (F.mul_mem hq.2.2 (F.div_mem (pow_mem hx 3) (three F)))

private theorem project_mem {u g v : V ℝ} (hu : VecIn F u) (hg : VecIn F g) (hv : VecIn F v) :
    QuadIn F (project u g v) := by
  rw [project_apply, defectCoef_apply]
  have hG := interp_mem F hu hg
  have hV := interp_mem F hu hv
  have hP : pivot u g ∈ F := F.sub_mem (hg 3) (ev_mem F (hu 3) hG)
  exact quad_sub F hV (quad_smul F
    (F.div_mem (F.sub_mem (hv 3) (ev_mem F (hu 3) hV)) hP) hG)

theorem polyProject_coeffs {u g v : V ℝ} (hu : VecIn F u) (hg : VecIn F g) (hv : VecIn F v) :
    CoeffsIn F (polyProject u g v) := by
  change CoeffsIn F (toPoly (project u g v))
  rw [toPoly_apply]
  have h := project_mem F hu hg hv
  exact coeffs_add F (coeffs_add F (coeffs_smul F h.1 (coeffs_one F))
    (coeffs_smul F h.2.1 (coeffs_X F))) (coeffs_smul F h.2.2 (coeffs_pow F (coeffs_X F) 2))

private theorem moments_mem {a b c : ℝ} {q : Quad ℝ}
    (ha : a ∈ F) (hb : b ∈ F) (hc : c ∈ F) (hq : QuadIn F q) : moments a b c q ∈ F := by
  rw [moments_apply]
  exact F.add_mem (F.add_mem (F.mul_mem hq.1 ha) (F.mul_mem hq.2.1 hb)) (F.mul_mem hq.2.2 hc)

private theorem normalizedRows_mem {h k : ℝ} {last : V ℝ →ₗ[ℝ] ℝ} {v : V ℝ}
    (hh : h ∈ F) (hk : k ∈ F) (hL : ∀ w, VecIn F w → last w ∈ F) (hv : VecIn F v) :
    VecIn F (normalizedRows h k last v) := by
  intro i
  fin_cases i
  · exact hv 0
  · exact F.add_mem (F.mul_mem hh (hv 0)) (hv 1)
  · exact F.add_mem
      (F.add_mem (F.mul_mem (F.sub_mem (F.mul_mem (two F) hh) hk) (hv 0)) (F.mul_mem hk (hv 1))) (hv 2)
  · exact hL v hv

private theorem forwardNormalized_mem {s d : ℝ} (hs : s ∈ F) (hd : d ∈ F) :
    MatIn F (forwardNormalized s d) := by
  let gd := gdAt s (etaAt s) d
  have hη := etaAt_mem F hs
  have hgd : gd ∈ F := gdAt_mem F hs hη hd
  have hh := hAt_mem F hs
  change MatIn F (matrixOf (normalizedRows (hAt s) (2/(hAt s-2))
    (forwardLast (uAt s d) (d-1) (Ud d gd) (Vd d (etaAt s) gd))))
  apply matrixOf_mem F
  intro v hv
  apply normalizedRows_mem F hh (F.div_mem (two F) (F.sub_mem hh (two F))) _ hv
  intro w hw
  change moments (d-1) (Ud d gd) (Vd d (etaAt s) gd) (interp (uAt s d) w) + w 3 ∈ F
  exact F.add_mem (moments_mem F (F.sub_mem hd F.one_mem) (Ud_mem F hd hgd) (Vd_mem F hd hη hgd)
    (interp_mem F (uAt_mem F hs hd) hw)) (hw 3)

private theorem reverseNormalized_mem {s t : ℝ} (hs : s ∈ F) (ht : t ∈ F) :
    MatIn F (reverseNormalized s t) := by
  have hh := hAt_mem F hs
  change MatIn F (matrixOf (normalizedRows (hAt s) (2/(hAt s-2)) (lastNormRow (uAt s t) t)))
  apply matrixOf_mem F
  intro v hv
  apply normalizedRows_mem F hh (F.div_mem (two F) (F.sub_mem hh (two F))) _ hv
  intro w hw
  have hQ := interp_mem F (uAt_mem F hs ht) hw
  change shiftAt t (interp (uAt s t) w) + w 3 ∈ F
  rw [shiftAt_apply]
  exact F.add_mem (F.sub_mem (prim_mem F ht hQ) (ev_mem F ht hQ)) (hw 3)

/-- Literal source geometry only. No admissible-root, numeric,
 or order hypothesis is needed for field membership. -/
theorem literal_geometry_in (M : MonomialBasis) (hm : standardPowers M)
    {s t c : ℝ} (hs : s ∈ F) (ht : t ∈ F) (hc : c ∈ F) :
    GeometryIn F (geometry M s t c) := by
  let γ := (zAt s)⁻¹
  let d := dAt M s t c
  let gd := gdAt s (etaAt s) d
  let x := xAt M s t c
  let y := yAt M s t c
  let ru := cubic (x 1) (x 4) (x 5)
  let A0 := tiltA (aAt s) d (1/2) gd
  let B0 := tiltB (aAt s) d (g1At s) gd
  let clean := A0 • evalAt M γ + B0 • evalAt M (γ * aAt s) + evalAt M (γ * d)
  let straighten := fun H : Polynomial ℝ => H - (clean H / clean ru) • ru
  have ha := aAt_mem F hs
  have hγ : γ ∈ F := F.inv_mem (zAt_mem F hs)
  have hd : d ∈ F := dAt_mem F M hm hs ht hc
  have hgd : gd ∈ F := gdAt_mem F hs (etaAt_mem F hs) hd
  have hy : VecIn F y := yAt_mem F M hm hs ht hc
  have hx : VecIn F x := fun i => F.sub_mem F.one_mem (hy i)
  have hru : CoeffsIn F ru := cubic_coeffs F (hx 1) (hx 4) (hx 5)
  have hA : A0 ∈ F := F.div_mem (F.mul_mem (F.sub_mem hd ha) hgd)
    (F.mul_mem (F.sub_mem ha F.one_mem) (half F))
  have hB : B0 ∈ F := F.div_mem (F.neg_mem (F.mul_mem (F.sub_mem hd F.one_mem) hgd))
    (F.mul_mem (F.sub_mem ha F.one_mem) (g1At_mem F hs))
  have hclean (P : Polynomial ℝ) (hP : CoeffsIn F P) : clean P ∈ F := by
    change A0 * evalAt M γ P + B0 * evalAt M (γ * aAt s) P + evalAt M (γ * d) P ∈ F
    exact F.add_mem (F.add_mem (F.mul_mem hA (evalAt_mem F M hm hγ hP))
      (F.mul_mem hB (evalAt_mem F M hm (F.mul_mem hγ ha) hP)))
      (evalAt_mem F M hm (F.mul_mem hγ hd) hP)
  have hStraight (P : Polynomial ℝ) (hP : CoeffsIn F P) : CoeffsIn F (straighten P) :=
    coeffs_sub F hP (coeffs_smul F (F.div_mem (hclean P hP) (hclean ru hru)) hru)
  refine {
    G := mat_smul F hγ (forwardNormalized_mem F hs hd)
    R := mat_smul F hγ (reverseNormalized_mem F hs ht)
    W := scalarWeights_mem F M hm hy
    gamma := hγ
    Ex := fun _ hP => evalSites_mem F M hm hx hP
    Ey := fun _ hP => evalSites_mem F M hm hy hP
    primitive := fun _ hP => primitive_coeffs F M hm hP
    forward := fun _ hv => polyProject_coeffs F (vec_smul F hγ (uAt_mem F hs hd))
      (vec_smul F (pow_mem hγ 2) (gAt_mem F hs hgd)) hv
    reverse := fun _ hv => polyProject_coeffs F (vec_smul F hγ (uAt_mem F hs ht))
      (vec_smul F (pow_mem hγ 2) (gAt_mem F hs F.zero_mem)) hv
    HF := ?_
    KR := ?_ }
  · intro i
    fin_cases i
    · exact hStraight _ (atOne_coeffs F M hm (hx 4)
        (coeffs_mul F (linearFactor_coeffs F (hx 1)) (linearFactor_coeffs F (hx 5))))
    · exact hStraight _ (atOne_coeffs F M hm (hx 5)
        (coeffs_mul F (linearFactor_coeffs F (hx 1)) (linearFactor_coeffs F (hx 4))))
  · intro i
    fin_cases i
    · exact atOne_coeffs F M hm (hy 0) (cubic_coeffs F (hy 2) (hy 3) (hy 4))
    · exact atOne_coeffs F M hm (hy 4) (cubic_coeffs F (hy 2) (hy 3) (hy 0))

theorem literal_coefficients_mem (M : MonomialBasis) (hm : standardPowers M)
    (e : (Fin 4 ⊕ Fin 8) ≃ Fin 12)
    {s t c : ℝ} (hs : s ∈ F) (ht : t ∈ F) (hc : c ∈ F) :
    let g := geometry M s t c
    let A12 := g.A.submatrix e.symm e.symm
    let b12 := g.b ∘ e.symm
    let A11 := contractMatrix (4 : Fin 12) (2 : Fin 11) A12
    let b11 := mergeCoefficient (4 : Fin 12) (2 : Fin 11) b12
    MatIn F A11 ∧ VecIn F b11 ∧ g.γ ∈ F :=
  (literal_geometry_in F M hm hs ht hc).fin11_mem e

end RKResearch.Certified.PaidDefectBridge.SDIRK118.Subfield
