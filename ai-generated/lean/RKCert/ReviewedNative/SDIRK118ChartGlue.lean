module

public import RKCert.ReviewedNative.PaidDefectOrderEight

import Mathlib.Tactic.Abel
import Mathlib.Tactic.Ring

@[expose] public section

noncomputable section

namespace RKResearch.Certified.PaidDefectBridge.SDIRK118

open RKResearch FiniteRootedTree
open RKResearch.Certified.Graded (mat diag row row_apply)
open scoped Matrix BigOperators

abbrev P (K : Type*) [Semiring K] := Polynomial K
abbrev V6 (K : Type*) := Fin 6 → K
abbrev V8 (K : Type*) := Fin 8 → K
abbrev Tableau (K : Type*) := Matrix (Fin 4 ⊕ Fin 8) (Fin 4 ⊕ Fin 8) K

variable {K : Type*} [Field K]

/-- A degree bound in the coefficient form needed by the scalar proof. -/
def PolyBound (n : ℕ) (f : P K) : Prop :=
  ∀ j : ℕ, n < j → f.coeff j = 0

def wDot {ι : Type*} [Fintype ι] (w a b : ι → K) : K :=
  ∑ i, w i * a i * b i

private theorem wDot_comm {ι : Type*} [Fintype ι] (w a b : ι → K) :
    wDot w a b = wDot w b a := by
  simp only [wDot]
  apply Finset.sum_congr rfl
  intro i _
  ring

private theorem wDot_add_left {ι : Type*} [Fintype ι] (w a b c : ι → K) :
    wDot w (a + b) c = wDot w a c + wDot w b c := by
  simp only [wDot, Pi.add_apply, mul_add, add_mul, Finset.sum_add_distrib]

private theorem wDot_add_right {ι : Type*} [Fintype ι] (w a b c : ι → K) :
    wDot w a (b + c) = wDot w a b + wDot w a c := by
  simp only [wDot, Pi.add_apply, mul_add, Finset.sum_add_distrib]

private theorem wDot_sub_right {ι : Type*} [Fintype ι] (w a b c : ι → K) :
    wDot w a (b - c) = wDot w a b - wDot w a c := by
  simp only [wDot, Pi.sub_apply, mul_sub, Finset.sum_sub_distrib]

private theorem wDot_smul_left {ι : Type*} [Fintype ι] (w a b : ι → K) (c : K) :
    wDot w (c • a) b = c * wDot w a b := by
  simp only [wDot, Pi.smul_apply, smul_eq_mul, Finset.mul_sum]
  apply Finset.sum_congr rfl
  intro i _
  ring

private theorem wDot_smul_right {ι : Type*} [Fintype ι] (w a b : ι → K) (c : K) :
    wDot w a (c • b) = c * wDot w a b := by
  rw [wDot_comm w a, wDot_smul_left, wDot_comm w b a]

private theorem weighted_mat
    (w : V8 K) (T L : Matrix (Fin 8) (Fin 8) K)
    (h : ∀ i j, w i * T i j = w j * L j i) (a b : V8 K) :
    wDot w a (mat T b) = wDot w (mat L a) b := by
  change (∑ i, w i * a i * (∑ j, T i j * b j)) =
    ∑ j, w j * (∑ i, L j i * a i) * b j
  simp only [Finset.mul_sum, Finset.sum_mul]
  rw [Finset.sum_comm]
  apply Finset.sum_congr rfl
  intro j _
  apply Finset.sum_congr rfl
  intro i _
  calc
    w i * a i * (T i j * b j) = (w i * T i j) * a i * b j := by ring
    _ = (w j * L j i) * a i * b j := by rw [h i j]
    _ = w j * (L j i * a i) * b j := by ring

private theorem weighted_clock (w ξ a b : V8 K) :
    wDot w a (diag ξ b) = wDot w (diag ξ a) b := by
  change (∑ i, w i * a i * (ξ i * b i)) =
    ∑ i, w i * (ξ i * a i) * b i
  apply Finset.sum_congr rfl
  intro i _
  ring

private theorem word_append_apply (L : Matrix (Fin 8) (Fin 8) K) (ξ z : V8 K)
    (U V : List Letter) :
    wordMap L ξ (U ++ V) z = wordMap L ξ U (wordMap L ξ V z) := by
  induction U with
  | nil => rfl
  | cons l U ih =>
      change letterMap L ξ l (wordMap L ξ (U ++ V) z) =
        letterMap L ξ l (wordMap L ξ U (wordMap L ξ V z))
      rw [ih]

private theorem weighted_word (w ξ : V8 K) (T L : Matrix (Fin 8) (Fin 8) K)
    (h : ∀ i j, w i * T i j = w j * L j i) (W : List Letter) (a b : V8 K) :
    wDot w a (wordMap T ξ W b) = wDot w (wordMap L ξ W.reverse a) b := by
  induction W generalizing a with
  | nil => rfl
  | cons l W ih =>
      have adj (v : V8 K) :
          wDot w a (letterMap T ξ l v) = wDot w (letterMap L ξ l a) v := by
        cases l
        · exact weighted_mat w T L h a v
        · exact weighted_clock w ξ a v
      calc
        _ = wDot w (letterMap L ξ l a) (wordMap T ξ W b) := adj _
        _ = wDot w (wordMap L ξ W.reverse (letterMap L ξ l a)) b := ih _
        _ = _ := by simp only [List.reverse_cons, word_append_apply, wordMap, LinearMap.id_apply, LinearMap.comp_apply]

/-- Operational inputs from the fixed 4+8 donor in physical suffix order. -/
structure Chart (K : Type*) [Field K] where
  mass : V6 K
  site : Fin 8 → Fin 6
  C : V8 K →ₗ[K] V6 K
  L : Matrix (Fin 8) (Fin 8) K
  I : P K →ₗ[K] P K
  Ex : P K →ₗ[K] V6 K
  Ey : P K →ₗ[K] V6 K
  projectOld : V8 K →ₗ[K] P K
  S : V6 K →ₗ[K] V6 K
  F : FiniteRootedTree → P K
  gamma : K
  s40 : K
  s50 : K
  s54 : K

namespace Chart

variable (d : Chart K)

def liftSites (a : V6 K) : V8 K := a ∘ d.site

def reverseVector (ξ : V8 K) (U : List Letter) : V8 K :=
  wordMap d.L ξ U 1

def profile : List Letter → P K
  | [] => 1
  | .transport :: U => d.I (profile U)
  | .clock :: U => (1 - Polynomial.X) * profile U

def revDefect (ξ : V8 K) (U : List Letter) : P K :=
  d.profile U - d.projectOld (d.reverseVector ξ U)

def graftVector (A : Tableau K) (H : P K) : V8 K :=
  mat (suffixBlock A) (d.liftSites (d.Ex H)) - d.liftSites (d.Ex (d.I H))

/-- Reduce the actual reviewed primitive seed to the block graft identity. -/
theorem graft_of_cross
    (A : Tableau K) (ξ : V8 K)
    (projF : (Fin 4 → K) →ₗ[K] P K) (ideal : FiniteRootedTree → P K)
    (hF : ∀ t, d.F t = ideal t - projF (Φ t A ∘ Sum.inl))
    (hD : ∀ t, d.liftSites (d.Ex (ideal t)) = idealDerivative ξ t)
    (hI : ∀ t, d.liftSites (d.Ex (d.I (ideal t))) = idealPrimitive ξ t)
    (hB : ∀ z : Fin 4 → K, crossBlock A *ᵥ z =
      d.liftSites (d.Ex (d.I (projF z))) -
        mat (suffixBlock A) (d.liftSites (d.Ex (projF z)))) :
    ∀ t, primitiveSeed A ξ t = d.graftVector A (d.F t) := by
  intro t
  change crossBlock A *ᵥ (Φ t A ∘ Sum.inl) +
    mat (suffixBlock A) (idealDerivative ξ t) - idealPrimitive ξ t = _
  have liftSub (u v : V6 K) :
      d.liftSites (u - v) = d.liftSites u - d.liftSites v := rfl
  rw [hB, ← hD t, ← hI t, hF t]
  simp only [graftVector, map_sub, liftSub]
  abel

/-- Finite operator, degree and scalar quadrature identities only. -/
structure Laws (A : Tableau K) (w ξ : V8 K) : Prop where
  balance : ∀ i j, w i * suffixBlock A i j = w j * d.L j i
  cluster : ∀ v a, wDot w v (d.liftSites a) = wDot d.mass (d.C v) a
  aggregate : ∀ v, d.C (mat d.L v) =
    d.Ey (d.I (d.projectOld v)) + d.S (d.C v - d.Ey (d.projectOld v))
  init : d.C 1 = d.Ey 1
  clock : ∀ v Q, d.C v = d.Ey Q →
    d.C (diag ξ v) = d.Ey ((1 - Polynomial.X) * Q)
  oldShort : ∀ U : List Letter, U.length ≤ 2 → d.revDefect ξ U = 0
  prefixLow : ∀ t, treeSize t ≤ 3 → d.F t = 0
  graft : ∀ t, primitiveSeed A ξ t = d.graftVector A (d.F t)
  seedDegree : ∀ t, PolyBound (treeGrade t) (d.F t)
  profileDegree : ∀ U, PolyBound U.length (d.profile U)
  green : ∀ (H Q : P K) (n m : ℕ), PolyBound n H → PolyBound m Q → n + m + 1 ≤ 7 →
    wDot d.mass (d.Ex H) (d.Ey (d.I Q)) =
      wDot d.mass (d.Ex (d.I H)) (d.Ey Q)

variable {d} {A : Tableau K} {w ξ : V8 K}
variable (law : d.Laws A w ξ)

include law in
private theorem aggregate_clean (v : V8 K) (Q : P K)
    (h : d.C v = d.Ey Q) :
    d.C (mat d.L v) = d.Ey (d.I Q) +
      (d.S (d.Ey (Q - d.projectOld v)) - d.Ey (d.I (Q - d.projectOld v))) := by
  rw [law.aggregate v, h]
  simp only [map_sub]
  abel

include law in
private theorem aligned (U : List Letter) (hU : U.length ≤ 3) :
    d.C (d.reverseVector ξ U) = d.Ey (d.profile U) := by
  revert hU
  induction U with
  | nil =>
    intro _
    exact law.init
  | cons l U ih =>
    intro hU
    have hs : U.length ≤ 2 := by
      simp only [List.length_cons] at hU
      omega
    have he := ih (show U.length ≤ 3 by omega)
    cases l
    · change d.C (mat d.L (d.reverseVector ξ U)) = d.Ey (d.I (d.profile U))
      have ha := aggregate_clean law (d.reverseVector ξ U) (d.profile U) he
      change d.C (mat d.L (d.reverseVector ξ U)) = d.Ey (d.I (d.profile U)) +
        (d.S (d.Ey (d.revDefect ξ U)) - d.Ey (d.I (d.revDefect ξ U))) at ha
      simpa only [law.oldShort U hs, map_zero, sub_self, add_zero] using ha
    · exact law.clock _ _ he

def rawMoment (d : Chart K) (H J : P K) : K :=
  wDot d.mass (d.Ex H) (d.S (d.Ey J) - d.Ey (d.I J))

include law in
/-- Derive the exact actual payment after transpose and scalar cancellation. -/
theorem payment_eq_raw (t : FiniteRootedTree) (W : List Letter)
    (hb : W.length + treeSize t < 8) (hm : W.length ≤ 3) :
    payment A w ξ t W = d.rawMoment (d.F t) (d.revDefect ξ W.reverse) := by
  let v := d.reverseVector ξ W.reverse
  let Q := d.profile W.reverse
  let H := d.F t
  let J := d.revDefect ξ W.reverse
  have ha : d.C v = d.Ey Q := aligned law W.reverse (by simpa only [List.length_reverse] using hm)
  have hb' : treeGrade t + 1 = treeSize t := by
    have ht : 0 < treeSize t := t.order.pos
    change treeSize t - 1 + 1 = treeSize t
    omega
  have hdeg : treeGrade t + W.reverse.length + 1 ≤ 7 := by
    have ht : treeGrade t + W.length + 1 ≤ 7 := by omega
    simpa only [List.length_reverse] using ht
  have hgreen := law.green H Q (treeGrade t) W.reverse.length
    (law.seedDegree t) (law.profileDegree W.reverse) hdeg
  have hh : d.C (mat d.L v) =
      d.Ey (d.I Q) + (d.S (d.Ey J) - d.Ey (d.I J)) := aggregate_clean law v Q ha
  calc
    payment A w ξ t W =
      wDot w (1 : V8 K) (wordMap (suffixBlock A) ξ W (primitiveSeed A ξ t)) := by
        simp only [payment, row_apply, dotProduct, wDot, Pi.one_apply, mul_one]
    _ = wDot w v (d.graftVector A H) := by
      rw [weighted_word w ξ (suffixBlock A) d.L law.balance, law.graft t] <;> rfl
    _ = wDot d.mass (d.Ex H) (d.C (mat d.L v)) -
        wDot d.mass (d.Ex (d.I H)) (d.C v) := by
      rw [graftVector, wDot_sub_right, weighted_mat w _ _ law.balance,
        law.cluster, law.cluster, wDot_comm d.mass (d.C (mat d.L v)),
        wDot_comm d.mass (d.C v)]
    _ = _ := by
      rw [hh, ha, wDot_add_right, hgreen]
      unfold rawMoment
      abel

include law in
theorem lowSeeds : LowSeedsZero8 A ξ := by
  intro t ht
  have h0 : d.liftSites (0 : V6 K) = 0 := rfl
  rw [law.graft t, law.prefixLow t ht]
  simp only [graftVector, map_zero, h0, sub_self]

include law in
theorem shortPayments : ShortPayments8 A w ξ := by
  intro t W _ hb hm
  rw [payment_eq_raw law t W hb (by omega), law.oldShort W.reverse (by
    simp only [List.length_reverse]
    omega)]
  simp [rawMoment, wDot]

def centralRight (d : Chart K) : P K →ₗ[K] V6 K :=
  d.Ey.comp d.I - d.gamma • d.Ey

def central (d : Chart K) (H J : P K) : K :=
  wDot d.mass (d.Ex H) (d.centralRight J)

def forwardCoords (d : Chart K) (H : P K) (i : Fin 2) : K :=
  if i = 0 then d.Ex H 4 else d.Ex H 5

def reverseCoords (d : Chart K) (J : P K) (i : Fin 2) : K :=
  if i = 0 then d.Ey J 0 else d.Ey J 4

def moment (d : Chart K) (U V : Fin 2 → P K) : Moment2 K :=
  Moment2.ofTaps (d.mass 4) (d.mass 5) d.s40 d.s50 d.s54
    (d.central (U 0) (V 0)) (d.central (U 0) (V 1))
    (d.central (U 1) (V 0)) (d.central (U 1) (V 1))

/-- The three literal strict entries in the six-site action. -/
def ExactSupport (d : Chart K) : Prop :=
  ∀ (a e : V6 K), wDot d.mass a (d.S e - d.gamma • e) =
    d.mass 4 * a 4 * d.s40 * e 0 +
    d.mass 5 * a 5 * d.s50 * e 0 +
    d.mass 5 * a 5 * d.s54 * e 4

private theorem central_two (d : Chart K) (U V : Fin 2 → P K)
    (a0 a1 b0 b1 : K) :
    d.central (a0 • U 0 + a1 • U 1) (b0 • V 0 + b1 • V 1) =
      (a0 * d.central (U 0) (V 0) * b0 + a0 * d.central (U 0) (V 1) * b1) +
      (a1 * d.central (U 1) (V 0) * b0 + a1 * d.central (U 1) (V 1) * b1) := by
  simp only [central, map_add, map_smul, wDot_add_left, wDot_add_right,
    wDot_smul_left, wDot_smul_right]
  ring

theorem rawMoment_factor (d : Chart K) (U V : Fin 2 → P K) (hs : d.ExactSupport)
    (H J : P K)
    (hH : H = d.Ex H 4 • U 0 + d.Ex H 5 • U 1)
    (hJ : J = d.Ey J 0 • V 0 + d.Ey J 4 • V 1) :
    d.rawMoment H J = (d.moment U V).pair (d.forwardCoords H) (d.reverseCoords J) := by
  have hc := central_two d U V (d.Ex H 4) (d.Ex H 5) (d.Ey J 0) (d.Ey J 4)
  rw [← hH, ← hJ] at hc
  have e :
      d.S (d.Ey J) - d.Ey (d.I J) =
        (d.S (d.Ey J) - d.gamma • d.Ey J) - d.centralRight J := by
    simp only [centralRight, LinearMap.sub_apply, LinearMap.comp_apply, LinearMap.smul_apply]
    abel
  unfold rawMoment
  rw [e, wDot_sub_right, hs]
  change _ - d.central H J = _
  rw [hc]
  have i0 : (0 : Fin 2) = 0 := rfl
  have i1 : (1 : Fin 2) ≠ 0 := by decide
  simp only [moment, Moment2.pair, Moment2.ofTaps, forwardCoords, reverseCoords,
    ite_true, if_neg i1]
  ring

/-- Interpolation of actual top residuals on four polynomial coefficients. -/
structure TopBases (d : Chart K) (ξ : V8 K) (U V : Fin 2 → P K) : Prop where
  forward : ∀ t, treeSize t = 4 →
    d.F t = d.Ex (d.F t) 4 • U 0 + d.Ex (d.F t) 5 • U 1
  reverse : ∀ W : List Letter, W.length = 3 →
    d.revDefect ξ W = d.Ey (d.revDefect ξ W) 0 • V 0 +
      d.Ey (d.revDefect ξ W) 4 • V 1

include law in
theorem topExpansion (U V : Fin 2 → P K) (s : d.ExactSupport)
    (bs : d.TopBases ξ U V) :
    TopExpansion8 A w ξ (fun t => d.forwardCoords (d.F t))
      (fun W => d.reverseCoords (d.revDefect ξ W.reverse)) (d.moment U V) := by
  intro t W ht hw
  rw [payment_eq_raw law t W (by omega) (by omega)]
  exact rawMoment_factor d U V s _ _ (bs.forward t ht)
    (bs.reverse W.reverse (by simpa only [List.length_reverse] using hw))

/-- Determinant identity on the plane vanishing at the two fixed nodes.
The selector and its value at the normalization node are never divisors. -/
theorem calibration_scale (Δ e0 e1 b0 b1 l0 l1 a b cal m : K)
    (he : a * e0 + b * e1 = 1) (hb : a * b0 + b * b1 = 0)
    (hm : m = a * l0 + b * l1) (hc : cal = Δ * (l1 * b0 - l0 * b1)) :
    cal = -(Δ * (e0 * b1 - e1 * b0)) * m := by
  have h : (e0 * b1 - e1 * b0) * m = l0 * b1 - l1 * b0 := by
    rw [hm]
    calc
      _ = (a * e0 + b * e1) * (l0 * b1 - l1 * b0) +
          (a * b0 + b * b1) * (l1 * e0 - l0 * e1) := by ring
      _ = _ := by rw [he, hb]; ring
  calc
    cal = Δ * (l1 * b0 - l0 * b1) := hc
    _ = -Δ * (l0 * b1 - l1 * b0) := by ring
    _ = _ := by rw [← h]; ring

theorem central_zero_iff_calibration_zero (Δ D m cal : K)
    (hΔ : Δ ≠ 0) (hD : D ≠ 0) (hs : cal = -(Δ * D) * m) :
    m = 0 ↔ cal = 0 := by
  rw [hs]
  constructor
  · intro hm
    rw [hm, mul_zero]
  · intro hp
    have hn : -(Δ * D) ≠ 0 := by
      intro h
      exact (mul_ne_zero hΔ hD) (neg_eq_zero.mp h)
    exact (mul_eq_zero.mp hp).resolve_left hn

include law in
/-- Non-root conclusion. No short payment or top expansion is assumed. -/
theorem hasOrder_eight_of_chart_calibration [CharZero K]
    (U V : Fin 2 → P K) (Δ D cal : K)
    (hquad : HasQuadratureOrder 8 w ξ)
    (hs : d.ExactSupport) (bs : d.TopBases ξ U V)
    (hs40 : d.s40 = d.central (U 0) (V 0) / d.mass 4)
    (hs50 : d.s50 = d.central (U 1) (V 0) / d.mass 5)
    (hs54 : d.s54 = d.central (U 1) (V 1) / d.mass 5)
    (hw4 : d.mass 4 ≠ 0) (hw5 : d.mass 5 ≠ 0)
    (hΔ : Δ ≠ 0) (hD : D ≠ 0)
    (hscale : cal = -(Δ * D) * d.central (U 0) (V 1))
    (hcal : cal = 0) :
    HasOrder 8 A (Sum.elim (0 : Fin 4 → K) w) := by
  have hc := (central_zero_iff_calibration_zero Δ D _ cal hΔ hD hscale).2 hcal
  have clearTap (u v : K) (hu : u ≠ 0) : u * (v / u) - v = 0 := by
    rw [div_eq_mul_inv, ← mul_assoc, mul_comm u v, mul_assoc,
      mul_inv_cancel₀ hu, mul_one, sub_self]
  apply hasOrder_eight_of_moment2 A w ξ _ _ (d.moment U V)
    hquad (lowSeeds law) (shortPayments law) (topExpansion law U V hs bs)
  · simp only [moment, Moment2.ofTaps, hs40]
    exact clearTap _ _ hw4
  · simp only [moment, Moment2.ofTaps, hc, neg_zero]
  · simp only [moment, Moment2.ofTaps, hs50]
    exact clearTap _ _ hw5
  · simp only [moment, Moment2.ofTaps, hs54]
    exact clearTap _ _ hw5

end Chart

end RKResearch.Certified.PaidDefectBridge.SDIRK118
