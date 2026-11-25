module

public import RKCert.ReviewedNative.CrossedGaussianMomentLift
import Mathlib.Tactic.FieldSimp
import Mathlib.Tactic.Linarith
import Mathlib.Tactic.NormNum
import Mathlib.Tactic.Positivity

@[expose] public section

/-! # Strict signed moment of the second and fifth nodes

Draft. The preconditions concern a supplied degree-eleven positive
finite rule and the normalized, checked reference moments. The separate
upstream factorization/positive-rule adapter pays these preconditions.
-/
namespace RKCert.ReviewedNative.CrossedGaussianRational

open Polynomial
open RKCert.ReviewedNative.FiniteGaussianLocalizer
open RKCert.ReviewedNative.CrossedGaussianReference
open RKCert.ReviewedNative.CrossedGaussianScalar
open RKCert.ReviewedNative.CrossedGaussianMomentLift

noncomputable section
variable {K : Type*} [Field K] [LinearOrder K] [IsStrictOrderedRing K]

/-- Nonnegative polynomial squares are represented on the audited fixed
positive degree-19 mesh. The actual tests cost at most twelve before the
degree-two reference weight. -/
def ReferenceNonneg (E : K[X] →ₗ[K] K) : Prop :=
  ∀ P : K[X], P.natDegree ≤ 12 → (∀ y : K, 0 ≤ P.eval y) → 0 ≤ E P

private theorem comboDegree {P Q : K[X]} {a b : K}
    (hp : P.natDegree ≤ 4) (hq : Q.natDegree ≤ 4) :
    (C a*P+C b*Q).natDegree ≤ 4 :=
  natDegree_add_le_of_le ((natDegree_C_mul_le _ _).trans hp)
    ((natDegree_C_mul_le _ _).trans hq)

private theorem square_nonneg_cut (E : K[X] →ₗ[K] K) (nn : ReferenceNonneg E)
    (d : K) (L : K[X]) (degree : L.natDegree ≤ 4) :
    0 ≤ E ((X^2-C d)^2*L^2) := by
  have h : (X^2-C d : K[X]).natDegree ≤ 2 :=
    (natDegree_sub_le _ _).trans (by simp)
  apply nn _ (natDegree_mul_le_of_le (natDegree_pow_le_of_le 2 h)
    (natDegree_pow_le_of_le 2 degree))
  intro x
  simp only [eval_mul,eval_pow]
  exact mul_nonneg (sq_nonneg _) (sq_nonneg _)

private theorem weighted_nonneg_ref (E : K[X] →ₗ[K] K) (nn : ReferenceNonneg E)
    (A : K) (hA : 0 ≤ A) (L : K[X]) (degree : L.natDegree ≤ 4) :
    0 ≤ E ((C (6*A)+C (1:K)*X^2)*L^2) := by
  have h : (C (6*A)+C (1:K)*X^2 : K[X]).natDegree ≤ 2 := by
    have hC : (C (6*A) : K[X]).natDegree ≤ 2 := by rw [natDegree_C]; decide
    exact natDegree_add_le_of_le hC (natDegree_C_mul_X_pow_le _ _)
  apply nn _
    ((natDegree_mul_le_of_le h (natDegree_pow_le_of_le 2 degree)).trans (by decide))
  intro x
  simp only [eval_mul,eval_pow,eval_add,eval_C,eval_X,one_mul]
  exact mul_nonneg (add_nonneg (mul_nonneg (by norm_num) hA) (sq_nonneg _)) (sq_nonneg _)

theorem signed_pair_neg
    (E : K[X] →ₗ[K] K) (moment : ReferencePowers E)
    (even : ∀ p : K[X], E (p.comp (-X)) = E p) (nn : ReferenceNonneg E)
    {s : Finset K} {μ : K → K} {A k R S : K}
    (mass : ∀ y ∈ s, 0 ≤ μ y) (quad : CenteredExact E s μ A k)
    (exitLeft : ∀ d : K, 2 ≤ (s.filter (fun y => y < d)).card → R < d)
    (exitRight : ∀ e : K, 2 ≤ (s.filter (fun y => e < y)).card → e < S)
    (hA : 0 ≤ A) (hk : 0 ≤ k)
    (atQuarter : 0 ≤ A+1/16-k/4) (atHalf : 0 ≤ A+1/4-k/2)
    (at₂₃ : 0 ≤ A+4/9-(2:K)/3*k)
    (at₃₄ : 0 ≤ A+9/16-(3:K)/4*k)
    (at₉₁₀ : 0 ≤ A+81/100-(9:K)/10*k)
    (at₁ : 0 ≤ A+1-k) :
    E (centeredResidual A k*((X-C R)*(X-C S))) < 0 := by
  have coarseRight : (7:K)/20 < S := by
    apply exitRight
    apply upper_rank_exit E s μ A k ((7:K)/20) mass quad
    intro a b hab
    have hp := upper_coarse_pos A k hA hk at₂₃ at₃₄ at₉₁₀ at₁ hab
    rw [← coarseRawFive E moment,upperQ_scale] at hp
    exact pos_of_mul_pos_right hp (by norm_num)
  have strongRight : k ≤ 1 → (8:K)/15 < S := by
    intro hk₁
    apply exitRight
    apply upper_rank_exit E s μ A k ((8:K)/15) mass quad
    intro a b hab
    have hp := upper_strong_pos A k hA hk hk₁ atHalf hab
    rw [← strongRawFive E moment,upperQ_scale] at hp
    exact pos_of_mul_pos_right hp (by norm_num)
  have coarseLeft : R < -(13:K)/22 := by
    let t : K := 13/22
    have ht : 0 < t := by norm_num [t]
    rw [neg_div]
    change R < -t
    apply exitLeft
    obtain ⟨L₀,L₁,h₀,h₁,e₀,e₁,pos⟩ :=
      two_even_tests E (tauFactor (t^2) 1 0) fixedLower₀
        (by norm_num : 0 < (484*15015 : K)) (coarseTauFive E moment) fixedLower₀_rankTwo
    apply lower_parity_rank_exit E s μ A k t mass quad even h₀ h₁ e₀ e₁
    intro a b hab
    let L : K[X] := C a*L₀+C b*L₁
    let ℓ := t*A+(t+k)*t^2
    have hℓ : 0 < ℓ := by dsimp [ℓ]; positivity
    have hs := square_nonneg_cut E nn (t^2) L (comboDegree h₀ h₁)
    have hpos := pos a b hab
    unfold tauFactor at hpos ⊢
    exact affine_threshold_pos E (X^2) L (g₀ := 1) (g₁ := 0) (ℓ := ℓ)
      hℓ (by simp; positivity) (by simp [ℓ]) hs hpos
  have strongLeft : ((16:K)/25)*A / ((16:K)/25+k) < 1/8 → R < -(16:K)/25 := by
    intro hshift
    let t : K := 16/25
    have ht : 0 < t := by norm_num [t]
    change t*A/(t+k) < 1/8 at hshift
    rw [neg_div]
    change R < -t
    apply exitLeft
    obtain ⟨L₀,L₁,h₀,h₁,e₀,e₁,pos⟩ :=
      two_even_tests E (tauFactor (t^2) (1/8) 1) fixedLower₁
        (by norm_num : 0 < (8*625*15015 : K)) (strongTauFive E moment) fixedLower₁_rankTwo
    apply lower_parity_rank_exit E s μ A k t mass quad even h₀ h₁ e₀ e₁
    intro a b hab
    let L : K[X] := C a*L₀+C b*L₁
    let ℓ := (t*A+(t+k)*t^2)/(1/8+t^2)
    have hden : 0 < 1/8+t^2 := by positivity
    have hℓ : 0 < ℓ := by dsimp [ℓ]; positivity
    have hcut : ℓ ≤ t+k := (div_le_iff₀ hden).2 (by
      have hpay := (div_lt_iff₀ (show 0 < t+k by positivity)).1 hshift
      nlinarith only [hpay])
    have hmatch : t*A+(t+k)*t^2 = ℓ*(1/8+1*t^2) := by
      simpa only [one_mul,ℓ] using (div_mul_cancel₀ (t*A+(t+k)*t^2) hden.ne').symm
    have hs := square_nonneg_cut E nn (t^2) L (comboDegree h₀ h₁)
    have hpos := pos a b hab
    unfold tauFactor at hpos ⊢
    exact affine_threshold_pos E (X^2) L (g₀ := 1/8) (g₁ := 1) (ℓ := ℓ)
      hℓ (by simpa only [mul_one] using sub_nonneg.mpr hcut) hmatch hs hpos
  have lowShear : ∀ t : K, 0 < t → t^2 ≤ centerSecond A+1/250 →
      k ≤ 5*t/6 → R < -t ∧ t < S := by
    intro t ht hcut hsk
    let G : K[X] := C (6*A)+C (1:K)*X^2
    have hc : 0 < (250*15015^2*(A+1/5) : K) := by positivity
    obtain ⟨L₀,L₁,h₀,h₁,e₀,e₁,pos⟩ :=
      two_even_tests E (tauFactor (centerSecond A+1/250) (6*A) 1) (shiftedSkew A)
        hc (shiftedTauFive E moment A hA) (shiftedSkew_rankTwo A hA)
    have ref (a b : K) (hab : a ≠ 0 ∨ b ≠ 0) :
        0 < E ((X^2-C (t^2))*G*(C a*L₀+C b*L₁)^2) :=
      move_threshold_down_pos E (X^2) G (C a*L₀+C b*L₁) hcut
        (weighted_nonneg_ref E nn A hA _ (comboDegree h₀ h₁)) (pos a b hab)
    have compare (j : K) (hj : 0 < j) (h₆ : t ≤ 6*j)
        (a b : K) (hab : a ≠ 0 ∨ b ≠ 0) :
        0 < E (tauFactor (t^2) (t*A) j*(C a*L₀+C b*L₁)^2) := by
      let L : K[X] := C a*L₀+C b*L₁
      let ℓ := (t*A+j*t^2)/(6*A+t^2)
      have hden : 0 < 6*A+t^2 := by positivity
      have hℓ : 0 < ℓ := by dsimp [ℓ]; positivity
      have hℓj : ℓ ≤ j := (div_le_iff₀ hden).2 (by
        have tpay := mul_le_mul_of_nonneg_right h₆ hA
        nlinarith only [tpay])
      have hmatch : t*A+j*t^2 = ℓ*(6*A+1*t^2) := by
        simpa only [one_mul,ℓ] using (div_mul_cancel₀ (t*A+j*t^2) hden.ne').symm
      have rs := ref a b hab
      unfold G at rs
      unfold tauFactor
      exact affine_threshold_pos E (X^2) L (g₀ := 6*A) (g₁ := 1) (ℓ := ℓ)
        hℓ (by simpa only [mul_one] using sub_nonneg.mpr hℓj) hmatch
        (square_nonneg_cut E nn (t^2) L (comboDegree h₀ h₁)) rs
    constructor
    · apply exitLeft (-t)
      apply lower_parity_rank_exit E s μ A k t mass quad even h₀ h₁ e₀ e₁
      exact compare (t+k) (by positivity) (by linarith only [hk, ht])
    · apply exitRight t
      apply upper_parity_rank_exit E s μ A k t mass quad even h₀ h₁ e₀ e₁
      exact compare (t-k) (by linarith only [hsk, ht]) (by linarith only [hsk])
  rw [centered_pair_moment E moment A k R S hA]
  apply mul_neg_of_pos_of_neg
  · unfold massFactor
    positivity
  · exact pairValue_negative A k R S hA hk atHalf atQuarter
      coarseLeft coarseRight strongRight lowShear strongLeft

end
end RKCert.ReviewedNative.CrossedGaussianRational
