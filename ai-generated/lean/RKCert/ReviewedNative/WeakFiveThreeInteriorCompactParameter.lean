module

public import RKCert.ReviewedNative.WeakFiveThreeInteriorMomentGram
public import RKCert.ReviewedNative.WeakFiveThreeInteriorCertified

import Mathlib.Tactic.Linarith
import Mathlib.Tactic.NormNum
import Mathlib.Tactic.Ring

@[expose] public section

/-! # Actual compact defect parameter and its closed-rectangle enclosure -/
namespace RKCert.ReviewedNative.ThreeInteriorPencil

open Polynomial RKCert.ReviewedNative.FiniteGaussianNodalLift
open RKCert.ReviewedNative.PolynomialCertificate
open RKCert.ReviewedNative.PolynomialCertificate.WeakFiveCells
open scoped Polynomial BigOperators

noncomputable section
variable {K : Type*} [Field K] [LinearOrder K] [IsStrictOrderedRing K]

def actualDefect (s : K) (β ω : Fin 7 → K) : K :=
  indexedAtomicMoment Finset.univ β ω (X^13) - threeInteriorScaledMoment s (X^13)

theorem actual_sorted_scaled_rule {s : K} {r : Fin 3 → K} {m : Fin 4 → K}
    (w : ThreeInteriorWord) (worder : StrictMono (w.sites r m)) {μ : ThreeInteriorSite → K}
    (mp : ∀ i, 0 < μ i)
    (law : ExactRule (threeInteriorMoment s) Finset.univ (threeInteriorSites r m) μ 12) :
    ∃ ω : Fin 7 → K, (∀ i, 0 < ω i) ∧
      ExactRule (threeInteriorScaledMoment s) Finset.univ (w.sites r m) ω 12 := by
  have inj : Function.Injective w.labels :=
    fun _ _ h => worder.injective (congrArg (threeInteriorSites r m) h)
  let e₀ : ThreeInteriorSite ≃ Fin 7 := finSumFinEquiv
  have onto : Function.Surjective w.labels := by
    have h : Function.Surjective (e₀ ∘ w.labels) :=
      Finite.surjective_of_injective (e₀.injective.comp inj)
    intro j
    obtain ⟨i,ei⟩ := h (e₀ j)
    exact ⟨i,e₀.injective ei⟩
  let e : Fin 7 ≃ ThreeInteriorSite := Equiv.ofBijective w.labels ⟨inj,onto⟩
  refine ⟨fun i => 12252240*μ (w.labels i),fun i => mul_pos (by norm_num) (mp _),?_⟩
  intro P pd
  change (12252240:K)*threeInteriorMoment s P = _
  rw [law P pd,Finset.mul_sum]
  calc
    (∑ i : ThreeInteriorSite, (12252240:K)*(μ i*P.eval (threeInteriorSites r m i))) =
        ∑ i : ThreeInteriorSite, ((12252240:K)*μ i)*P.eval (threeInteriorSites r m i) := by
      exact Finset.sum_congr rfl fun i _ => (mul_assoc _ _ _).symm
    _ = _ := (Equiv.sum_comp e
      (fun i => ((12252240:K)*μ i)*P.eval (threeInteriorSites r m i))).symm

private theorem atomic_square_positive {β ω : Fin 7 → K}
    (bi : Function.Injective β) (inside : ∀ i, β i ∈ Set.Ioo 0 1) (wp : ∀ i, 0 < ω i)
    {P W : K[X]} (pd : P.natDegree ≤ 6) (pn : P ≠ 0)
    (pos : ∀ x ∈ Set.Ioo (0:K) 1, 0 < W.eval x) :
    0 < indexedAtomicMoment Finset.univ β ω (W*P^2) := by
  have live : ∃ i, P.eval (β i) ≠ 0 := by
    by_contra! hz
    apply pn
    let U : Finset (Fin 7) := Finset.univ
    have small : P.natDegree < U.card := by
      have card : U.card = 7 := by simp [U]
      rw [card]
      exact Nat.lt_succ_of_le pd
    have deg : P.degree < (U.card : WithBot ℕ) :=
      P.degree_le_natDegree.trans_lt (by exact_mod_cast small)
    exact Polynomial.eq_zero_of_degree_lt_of_eval_index_eq_zero U bi.injOn deg (fun i _ => hz i)
  rw [indexedAtomicMoment_apply]
  apply Finset.sum_pos'
  · intro i _
    rw [eval_mul,eval_pow]
    exact mul_nonneg (wp i).le (mul_nonneg (pos _ (inside i)).le (sq_nonneg _))
  · obtain ⟨i,ni⟩ := live
    refine ⟨i,Finset.mem_univ _,?_⟩
    rw [eval_mul,eval_pow]
    exact mul_pos (wp i) (mul_pos (pos _ (inside i)) (sq_pos_of_ne_zero ni))

theorem actualDefect_strict {s : K} (ss : s ∈ Set.Icc 0 1) {β ω : Fin 7 → K}
    (bi : Function.Injective β) (inside : ∀ i, β i ∈ Set.Ioo 0 1) (wp : ∀ i, 0 < ω i)
    (law : ExactRule (threeInteriorScaledMoment s) Finset.univ β ω 12) :
    compactLower s < actualDefect s β ω ∧ actualDefect s β ω < compactUpper s := by
  let J := threeInteriorScaledMoment s
  let atom := indexedAtomicMoment Finset.univ β ω
  let δ := actualDefect s β ω
  have sat (v : Fin 7 → K) (q : v (Fin.last 6) = 1) :
      (vecPolynomial v).coeff 6 = 1 :=
    (vecPolynomial_coeff v (Fin.last 6)).trans q
  have couple (v : Fin 7 → K) (q : v (Fin.last 6) = 1) :
      atom (vecPolynomial v ^ 2) = J (vecPolynomial v ^ 2) ∧
      atom (X*vecPolynomial v ^ 2) = J (X*vecPolynomial v ^ 2)+δ := by
    have d := vecPolynomial_degree v (show 7 ≤ 6+1 by decide)
    simpa only [pow_two,actualDefect,δ,sat v q,mul_one] using
      (exact12_pair_and_border law (vecPolynomial v) (vecPolynomial v) d d)
  have nonzero (v : Fin 7 → K) (q : v (Fin.last 6) = 1) : vecPolynomial v ≠ 0 := by
    intro z
    have e := sat v q
    rw [z,coeff_zero] at e
    exact zero_ne_one e
  obtain ⟨_,v,hv,hit,_⟩ := every_rayleigh_min ss natDegree_X.le x_unit_pos
  obtain ⟨_,u,hu,atU,_⟩ :=
    every_rayleigh_min ss (unit_right_weight_degree (K := K)).le one_sub_x_unit_pos
  constructor
  · have h : 0 < atom (X*vecPolynomial v ^ 2) :=
      atomic_square_positive bi inside wp (vecPolynomial_degree v le_rfl) (nonzero v hv) x_unit_pos
    rw [(couple v hv).2,← rayleigh_momentGram J X v] at h
    change 0 < rayleigh (gramA 7 s) v+δ at h
    change rayleigh (gramA 7 s) v = rayleighCost (gramA 7 s) at hit
    rw [hit] at h
    change -rayleighCost (gramA 7 s) < δ
    linarith only [h]
  · let P := vecPolynomial u
    have h : 0 < atom ((1-X)*P^2) :=
      atomic_square_positive bi inside wp (vecPolynomial_degree u le_rfl) (nonzero u hu) one_sub_x_unit_pos
    have shape : (1-X)*P^2 = P^2-X*P^2 := by rw [sub_mul,one_mul]
    have paid : atom ((1-X)*P^2) = J ((1-X)*P^2)-δ := by
      rw [shape,map_sub,map_sub]
      change atom (vecPolynomial u ^ 2)-atom (X*vecPolynomial u ^ 2) = _
      rw [(couple u hu).1,(couple u hu).2]
      dsimp only [P]
      ring
    rw [paid,← rayleigh_momentGram J (1-X) u] at h
    change 0 < rayleigh (gramCap 7 s) u-δ at h
    change rayleigh (gramCap 7 s) u = rayleighCost (gramCap 7 s) at atU
    rw [atU] at h
    exact sub_pos.mp h

def compactCoordinate (s δ : K) : K :=
  (δ-compactLower s)/(compactUpper s-compactLower s)

theorem compactCoordinate_spec {s δ : K} (ss : s ∈ Set.Icc 0 1)
    (lo : compactLower s < δ) (hi : δ < compactUpper s) :
    compactCoordinate s δ ∈ Set.Ioo 0 1 ∧
      δ = mix (compactLower s) (compactUpper s) (compactCoordinate s δ) := by
  let a := compactLower s
  let b := compactUpper s
  let j := compactCoordinate s δ
  have bp : 0 < b-a := sub_pos.mpr (lo.trans hi)
  have j0 : 0 < j := div_pos (sub_pos.mpr lo) bp
  have j1 : j < 1 := by
    change (δ-a)/(b-a) < 1
    apply (div_lt_iff₀ bp).2
    linarith only [hi]
  have clear : j*(b-a) = δ-a := div_mul_cancel₀ _ bp.ne'
  refine ⟨⟨j0,j1⟩,?_⟩
  change δ = mix a b j
  calc
    δ = a+j*(b-a) := by rw [clear]; ring
    _ = mix a b j := by unfold mix; ring

def defectBoxLow (sl su jl : K) : K := mix (compactLower su) (compactUpper sl) jl
def defectBoxHigh (sl su ju : K) : K := mix (compactLower sl) (compactUpper su) ju

private theorem mix_order_parameters {a b x y : K} (ab : a ≤ b) (xy : x ≤ y) :
    mix a b x ≤ mix a b y := by
  have h : 0 ≤ (y-x)*(b-a) := mul_nonneg (sub_nonneg.mpr xy) (sub_nonneg.mpr ab)
  unfold mix
  nlinarith only [h]

private theorem mix_order_endpoints {a b c d x : K} (ac : a ≤ c) (bd : b ≤ d)
    (hx : x ∈ Set.Icc 0 1) : mix a b x ≤ mix c d x :=
  add_le_add (mul_le_mul_of_nonneg_left ac (sub_nonneg.mpr hx.2))
    (mul_le_mul_of_nonneg_left bd hx.1)

/-- Exact same monotone enclosure as the literal Python verifier. This is
closed on both parameters and uses no finite checks in the field. -/
theorem defect_enclosed {s j sl su jl ju : K}
    (sp : s ∈ Set.Icc sl su) (jp : j ∈ Set.Icc jl ju)
    (slp : sl ∈ Set.Icc 0 1) (sup : su ∈ Set.Icc 0 1)
    (jlp : jl ∈ Set.Icc 0 1) (jup : ju ∈ Set.Icc 0 1) :
    mix (compactLower s) (compactUpper s) j ∈
      Set.Icc (defectBoxLow sl su jl) (defectBoxHigh sl su ju) := by
  have ss : s ∈ Set.Icc 0 1 := ⟨slp.1.trans sp.1,sp.2.trans sup.2⟩
  have ab : compactLower s ≤ compactUpper s :=
    ((compact_bounds_sign ss).1.trans (compact_bounds_sign ss).2).le
  exact ⟨(mix_order_endpoints (compactLower_anti ss sup sp.2) (compactUpper_mono slp ss sp.1) jlp).trans
      (mix_order_parameters ab jp.1),
    (mix_order_parameters ab jp.2).trans
      (mix_order_endpoints (compactLower_anti slp ss sp.1) (compactUpper_mono ss sup sp.2) jup)⟩

end
end RKCert.ReviewedNative.ThreeInteriorPencil
