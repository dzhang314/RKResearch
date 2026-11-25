module

public import RKCert.ReviewedNative.DyadicFourShiftClassification
public import RKCert.ReviewedNative.DyadicBalancedNodal
public import RKCert.ReviewedNative.RationalPrimeNodalSupport

import Mathlib.Algebra.Polynomial.Derivative
import Mathlib.Tactic.Ring
import Lean.Elab.Tactic.Omega

@[expose] public section

/-! # Rational contributing support: four dyadic tests exclude width at most 16

This works on actual nonzero aggregate sites in a characteristic-zero
field. Reflection is only an orientation of a second paid polynomial.
No symmetry of the rule, triangularity, or signs of weights are assumed. -/

namespace RKResearch.Certified.DyadicFourShift

open Polynomial RKResearch.Certified.RationalPrimeCut
open scoped BigOperators Polynomial Classical

theorem dyadic_oriented_nodal_no_four_shift (T : Finset ℚ) (hm : T.card ≤ 16)
    (orient : dyadicDenCount T-dyadicEvenCount T ≤ dyadicEvenCount T)
    (rows : ∀ j : Fin 4, UniformIntRowZero (integralRationalNodalHull T).coeff T.card j.val) :
    False := by
  let a := (integralRationalNodalHull T).coeff
  let t := dyadicDenCount T
  let u := dyadicEvenCount T
  have hut : u ≤ t := dyadicEvenCount_le_denCount T
  have ht17 : t < 17 := (dyadicDenCount_le_card T).trans_lt (by omega)
  have hu17 : u < 17 := hut.trans_lt ht17
  have divs : ∀ k, (2 : ℤ)^(dyadicCredit t u k) ∣ a k := integralNodal_dyadicCredit_dvd T
  have parity : ∀ k, (a k : ZMod 2) = (dyadicParity t u k : ZMod 2) := integralNodal_coeff_two T
  have tail (k : ℕ) (hk : T.card < k) : a k = 0 := by
    apply coeff_eq_zero_of_natDegree_lt
    simpa only [integralRationalNodalHull_natDegree] using hk
  have pay8 : DyadicFourRows8 a := dyadicFourRows8_of_uniformInt a hm tail rows
  have pass : (t,u) ∈ dyadicSurvivingPairs :=
    (dyadicParityGate_exact ⟨t,ht17⟩ ⟨u,hu17⟩).mp
      (dyadicParityGate_of_paid a hut orient parity divs pay8)
  rcases dyadicSurvivingPairs_test (t,u) pass with balanced | oneTerm
  · have ht : t=16 := congrArg Prod.fst balanced
    have hu : u=8 := congrArg Prod.snd balanced
    have ev (k : ℕ) (h : 2 ≤ dyadicCredit 16 8 k) : (a k : ZMod 4)=0 :=
      cast_zero_four_of_credit (by rw [ht,hu]; exact h) (divs k)
    have a6 := ev 6 (by decide)
    have a4 := ev 4 (by decide)
    have j1 := dyadicPaid4 a pay8 (1 : Fin 4)
    have j3 := dyadicPaid4 a pay8 (3 : Fin 4)
    change (a 14 : ZMod 4)+2*(a 6 : ZMod 4)=0 at j1
    change (a 12 : ZMod 4)+2*(a 4 : ZMod 4)=0 at j3
    rw [a6,mul_zero,add_zero] at j1
    rw [a4,mul_zero,add_zero] at j3
    exact dyadicBalanced_coeffs_ne_zero T hm ht hu ⟨j3,j1⟩
  · exact dyadicOneTerm_excludes_paid a parity divs pay8 oneTerm

end RKResearch.Certified.DyadicFourShift

namespace RKResearch

open Polynomial Certified.RationalPrimeCut Certified.DyadicFourShift
open scoped BigOperators Matrix Polynomial Classical

noncomputable section

variable {ι K : Type*} [Fintype ι] [Field K] [CharZero K]
  {p : ℕ} {b c : ι → K}

/-- Derivative exactness is obtained just by summing the paid coefficient
rows. This isolated helper keeps reflection independent of other cuts. -/
private theorem dyadic_formal_derivative_endpoints (ho : HasQuadratureOrder p b c)
    (P : K[X]) (deg : P.natDegree ≤ p) :
    (∑ i, b i * P.derivative.eval (c i)) = P.eval 1 - P.eval 0 := by
  by_cases hp : p=0
  · have dp : P.natDegree=0 := by omega
    rw [eq_C_of_natDegree_eq_zero dp]
    simp
  have dd0 := P.natDegree_derivative_le
  have dd : P.derivative.natDegree < p := by omega
  have row (k : ℕ) (hk : k < p) :
      ((k+1 : ℕ) : K)*(∑ i, b i*(c i)^k)=1 := by
    simpa only [Nat.succ_eq_add_one, dotProduct, Pi.pow_apply] using ho k hk
  calc
    _ = ∑ i, ∑ k ∈ Finset.range p,
          P.coeff (k+1) * (((k+1 : ℕ) : K) * (b i*(c i)^k)) := by
      apply Finset.sum_congr rfl
      intro i _
      rw [Polynomial.eval_eq_sum_range' dd (c i), Finset.mul_sum]
      apply Finset.sum_congr rfl
      intro k _
      rw [coeff_derivative]
      simp only [Nat.cast_add, Nat.cast_one] <;> ac_rfl
    _ = ∑ k ∈ Finset.range p, P.coeff (k+1)*(((k+1 : ℕ) : K)*(∑ i, b i*(c i)^k)) := by
      rw [Finset.sum_comm]
      simp only [Finset.mul_sum]
    _ = ∑ k ∈ Finset.range p, P.coeff (k+1) := by
      apply Finset.sum_congr rfl
      intro k hk
      rw [row k (Finset.mem_range.mp hk), mul_one]
    _ = _ := by
      rw [Polynomial.eval_eq_sum_range' (Nat.lt_succ_of_le deg) (1 : K),
        ← Polynomial.coeff_zero_eq_eval_zero, Finset.sum_range_succ']
      simp only [one_pow, mul_one] <;> ring

private theorem dyadic_reflected_moment (ho : HasQuadratureOrder p b c)
    (k : ℕ) (hk : k+1 ≤ p) :
    (∑ i, b i*(1-c i)^k) = 1 / ((k+1 : ℕ) : K) := by
  let P : K[X] := (1-X)^(k+1)
  have dl : (1 : K[X]).natDegree < (X : K[X]).natDegree := by simp
  have Pdeg : P.natDegree ≤ p := by
    dsimp only [P]
    rw [natDegree_pow, natDegree_sub_eq_right_of_natDegree_lt dl, natDegree_X, Nat.mul_one]
    exact hk
  have ends : P.eval 1 - P.eval 0 = -1 := by
    have h : k+1 ≠ 0 := by omega
    simp [P,h]
  have deriv (x : K) : P.derivative.eval x = -((k+1 : ℕ) : K)*(1-x)^k := by
    dsimp only [P]
    rw [derivative_pow]
    simp only [derivative_sub, derivative_one, derivative_X, zero_sub, eval_mul,
      eval_C, eval_pow, eval_sub, eval_neg, eval_one, eval_X, show k+1-1=k by omega]
    ring
  have heq : (∑ i, b i*P.derivative.eval (c i)) =
      -((k+1 : ℕ) : K)*(∑ i, b i*(1-c i)^k) := by
    rw [Finset.mul_sum]
    apply Finset.sum_congr rfl
    intro i _
    rw [deriv]
    ring
  have h := dyadic_formal_derivative_endpoints ho P Pdeg
  rw [heq, ends] at h
  apply (eq_div_iff (Nat.cast_ne_zero.mpr (by omega : k+1 ≠ 0))).mpr
  calc
    _ = -(-((k+1 : ℕ) : K)*(∑ i, b i*(1-c i)^k)) := by ring
    _ = _ := by rw [h,neg_neg]

theorem HasQuadratureOrder.no_dyadic_four_shift_support_of_rat
    (ho : HasQuadratureOrder p b c)
    (small : (activeQuadratureSites b c).card ≤ 16)
    (pay : (activeQuadratureSites b c).card+4 ≤ p)
    (rat : ∀ x ∈ activeQuadratureSites b c, ∃ r : ℚ, x = (r : K)) : False := by
  let S := activeQuadratureSites b c
  let μ := quadratureSiteWeight b c
  let ρ (x : S) : ℚ := Classical.choose (rat x.val x.property)
  have hρ (x : S) : x.val = (ρ x : K) := Classical.choose_spec (rat x.val x.property)
  have injρ : Function.Injective ρ := by
    intro x y h
    apply Subtype.ext
    exact (hρ x).trans ((congrArg (fun r : ℚ => (r : K)) h).trans (hρ y).symm)
  let T := (Finset.univ : Finset S).image ρ
  have hT : T.card = S.card := by
    dsimp only [T]
    rw [Finset.card_image_of_injective _ injρ, Finset.card_univ, Fintype.card_coe]
  have cover (x : K) (hx : x ∈ S) : ∃ r ∈ T, x = (r : K) := by
    let y : S := ⟨x,hx⟩
    exact ⟨ρ y, Finset.mem_image.mpr ⟨y, Finset.mem_univ _, rfl⟩, hρ y⟩
  by_cases orient : dyadicDenCount T-dyadicEvenCount T ≤ dyadicEvenCount T
  · have legal (k : ℕ) (hk : k+1 ≤ p) :
        (∑ x ∈ S, μ x*x^k) = 1 / ((k+1 : ℕ) : K) := by
      change (∑ x ∈ activeQuadratureSites b c, quadratureSiteWeight b c x * x^k) = _
      rw [← weighted_sum_eq_activeQuadratureSites b c (fun x => x^k)]
      have hr : ((k+1 : ℕ) : K) * (∑ i, b i*(c i)^k)=1 := by
        simpa only [dotProduct,Pi.pow_apply,Nat.succ_eq_add_one] using ho k hk
      exact (eq_div_iff (ho.isUnit (Nat.succ_pos k) hk).ne_zero).mpr
        (by simpa only [mul_comm] using hr)
    apply dyadic_oriented_nodal_no_four_shift T (by rw [hT]; exact small) orient
    intro j
    exact uniformIntRows_of_grouped_rat_roots S μ T cover legal (t:=4)
      (by rw [hT]; exact pay) j.val j.isLt
  · let S' := S.image (fun x : K => 1-x)
    let μ' (x : K) := μ (1-x)
    let T' := T.image (fun r : ℚ => 1-r)
    have injK : Function.Injective (fun x : K => 1-x) := by
      intro x y e
      simpa only [sub_sub_cancel] using congrArg (fun z : K => 1-z) e
    have injQ : Function.Injective (fun r : ℚ => 1-r) := by
      intro x y e
      simpa only [sub_sub_cancel] using congrArg (fun z : ℚ => 1-z) e
    have hT' : T'.card=S.card := by
      change (T.image (fun r : ℚ => 1-r)).card = S.card
      rw [Finset.card_image_of_injective _ injQ, hT]
    have cover' (x : K) (hx : x ∈ S') : ∃ r ∈ T', x = (r : K) := by
      obtain ⟨y,hy,eqx⟩ := Finset.mem_image.mp hx
      obtain ⟨r,hr,hyq⟩ := cover y hy
      refine ⟨1-r, Finset.mem_image.mpr ⟨r,hr,rfl⟩,?_⟩
      rw [← eqx,hyq,Rat.cast_sub,Rat.cast_one]
    have legal' (k : ℕ) (hk : k+1 ≤ p) :
        (∑ x ∈ S', μ' x*x^k) = 1 / ((k+1 : ℕ) : K) := by
      calc
        _ = ∑ x ∈ S, μ x*(1-x)^k := by
          change (∑ x ∈ S.image (fun x : K => 1-x), μ' x*x^k) = _
          rw [Finset.sum_image injK.injOn]
          simp only [μ', sub_sub_cancel]
        _ = ∑ i, b i*(1-c i)^k := (weighted_sum_eq_activeQuadratureSites b c (fun x => (1-x)^k)).symm
        _ = _ := dyadic_reflected_moment ho k hk
    have counts := dyadicCounts_reflect T
    have ori' : dyadicDenCount T'-dyadicEvenCount T' ≤ dyadicEvenCount T' := by
      change dyadicDenCount (T.image fun r => 1-r) -
        dyadicEvenCount (T.image fun r => 1-r) ≤ dyadicEvenCount (T.image fun r => 1-r)
      rw [counts.1,counts.2]
      have le := dyadicEvenCount_le_denCount T
      omega
    apply dyadic_oriented_nodal_no_four_shift T' (by rw [hT']; exact small) ori'
    intro j
    exact uniformIntRows_of_grouped_rat_roots S' μ' T' cover' legal' (t:=4)
      (by rw [hT']; exact pay) j.val j.isLt

/-- All-order form of the four-shift floor. Only the first twenty
moment degrees enter, so the site floor saturates at seventeen. -/
theorem HasQuadratureOrder.min17_sub3_le_activeQuadratureSites_of_rat
    (ho : HasQuadratureOrder p b c)
    (rat : ∀ x ∈ activeQuadratureSites b c, ∃ r : ℚ, x = (r : K)) :
    min 17 (p-3) ≤ (activeQuadratureSites b c).card := by
  by_contra h
  have h1 := min_le_left 17 (p-3)
  have h2 := min_le_right 17 (p-3)
  exact ho.no_dyadic_four_shift_support_of_rat (by omega) (by omega) rat

theorem HasOrder.min17_sub3_le_activeQuadratureSites_of_rat
    {A : Matrix ι ι K} (ho : HasOrder p A b)
    (rat : ∀ x ∈ activeQuadratureSites b (A *ᵥ 1), ∃ r : ℚ, x = (r : K)) :
    min 17 (p-3) ≤ (activeQuadratureSites b (A *ᵥ 1)).card :=
  ho.hasQuadratureOrder.min17_sub3_le_activeQuadratureSites_of_rat rat

theorem HasOrder.sub3_le_activeQuadratureSites_of_rat_of_le20
    {A : Matrix ι ι K} (ho : HasOrder p A b) (hp : p ≤ 20)
    (rat : ∀ x ∈ activeQuadratureSites b (A *ᵥ 1), ∃ r : ℚ, x = (r : K)) :
    p-3 ≤ (activeQuadratureSites b (A *ᵥ 1)).card := by
  have h := ho.min17_sub3_le_activeQuadratureSites_of_rat rat
  rwa [min_eq_right (by omega : p-3 ≤ 17)] at h

theorem HasOrder.seventeen_le_activeQuadratureSites_of_rat_order20
    {A : Matrix ι ι K} (ho : HasOrder 20 A b)
    (rat : ∀ x ∈ activeQuadratureSites b (A *ᵥ 1), ∃ r : ℚ, x = (r : K)) :
    17 ≤ (activeQuadratureSites b (A *ᵥ 1)).card := by
  simpa using ho.sub3_le_activeQuadratureSites_of_rat_of_le20 (by decide) rat

theorem HasOrder.min17_sub3_le_activeQuadratureSites_rat
    {A : Matrix ι ι ℚ} {w : ι → ℚ} (ho : HasOrder p A w) :
    min 17 (p-3) ≤ (activeQuadratureSites w (A *ᵥ 1)).card :=
  ho.min17_sub3_le_activeQuadratureSites_of_rat (fun x _ => ⟨x,rfl⟩)

end

end RKResearch
