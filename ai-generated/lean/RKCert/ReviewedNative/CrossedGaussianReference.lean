module

public import RKCert.ReviewedNative.FiniteGaussianParity
import Mathlib.Tactic.Linarith
import Mathlib.Tactic.NormNum
import Mathlib.Tactic.Positivity
import Mathlib.Tactic.Ring

@[expose] public section

/-! # Rational reference certificates for the crossed six-node localizer

Draft. The integer arrays are small moment certificates common to the
entire quadratic residual family, not data from a physical profile.
-/
namespace RKCert.ReviewedNative.CrossedGaussianReference

open Polynomial
open RKCert.ReviewedNative.FiniteGaussianLocalizer

noncomputable section
variable {K : Type*} [Field K] [LinearOrder K] [IsStrictOrderedRing K]

structure Five (K : Type*) where
  a : K
  b : K
  c : K
  d : K
  e : K

def verticalQ (M : Five K) (x y : K) : K := binaryQ M.a M.b M.c x y

def diagonalQ (M : Five K) (x y : K) : K :=
  binaryQ (M.a-M.b) (M.b-M.c) (M.c-M.d) x y

def upperQ (M : Five K) (A k x y : K) : K :=
  binaryQ (A*M.a+M.c-k*M.b) (A*M.b+M.d-k*M.c)
    (A*M.c+M.e-k*M.d) x y

/-- Strict positivity of an affine binary-moment matrix along a segment,
and on the vertical ray above it. -/
theorem upper_between (M : Five K) {A k k₀ k₁ r b x y : K}
    (lo : k₀ ≤ k) (hi : k ≤ k₁) (span : k₀ < k₁) (height : r*k+b ≤ A)
    (vPos : 0 < verticalQ M x y)
    (p₀ : 0 < upperQ M (r*k₀+b) k₀ x y)
    (p₁ : 0 < upperQ M (r*k₁+b) k₁ x y) :
    0 < upperQ M A k x y := by
  let ℓ := (k-k₀)/(k₁-k₀)
  have hspan : 0 < k₁-k₀ := sub_pos.mpr span
  have hℓ : 0 ≤ ℓ := div_nonneg (sub_nonneg.mpr lo) hspan.le
  have hℓ₁ : ℓ ≤ 1 := (div_le_one₀ hspan).2 (sub_le_sub_right hi k₀)
  have hprod : ℓ*(k₁-k₀) = k-k₀ := div_mul_cancel₀ _ hspan.ne'
  have hline : (1-ℓ)*k₀+ℓ*k₁ = k := by
    calc
      (1-ℓ)*k₀+ℓ*k₁ = k₀+ℓ*(k₁-k₀) := by ring
      _ = k := by rw [hprod]; ring
  have hmix :
      upperQ M A k x y =
        (1-ℓ)*upperQ M (r*k₀+b) k₀ x y + ℓ*upperQ M (r*k₁+b) k₁ x y +
          (A-(r*k+b))*verticalQ M x y := by
    rw [← hline]
    unfold upperQ verticalQ binaryQ
    ring
  rw [hmix]
  have hn : 0 ≤ (A-(r*k+b))*verticalQ M x y :=
    mul_nonneg (sub_nonneg.mpr height) vPos.le
  apply add_pos_of_pos_of_nonneg ?_ hn
  rcases hℓ₁.lt_or_eq with hlt | heq
  · exact add_pos_of_pos_of_nonneg (mul_pos (sub_pos.mpr hlt) p₀)
      (mul_nonneg hℓ p₁.le)
  · simpa only [heq, sub_self, zero_mul, one_mul, zero_add] using p₁

theorem upper_diagonal_tail (M : Five K) {A k A₀ k₀ x y : K}
    (lo : k₀ ≤ k) (height : A₀+(k-k₀) ≤ A)
    (vPos : 0 < verticalQ M x y)
    (dPos : 0 < diagonalQ M x y)
    (p₀ : 0 < upperQ M A₀ k₀ x y) :
    0 < upperQ M A k x y := by
  have hmix :
      upperQ M A k x y =
      upperQ M A₀ k₀ x y + (k-k₀)*diagonalQ M x y +
        (A-(A₀+(k-k₀)))*verticalQ M x y := by
    unfold upperQ diagonalQ verticalQ binaryQ
    ring
  rw [hmix]
  exact add_pos_of_pos_of_nonneg
    (add_pos_of_pos_of_nonneg p₀ (mul_nonneg (sub_nonneg.mpr lo) dPos.le))
    (mul_nonneg (sub_nonneg.mpr height) vPos.le)

/-- Multiplying by this quartic leaves a genuine two-dimensional affine
test of total degree at most five before squaring. -/
def upperFilter : K[X] := X * (C (3:K)*X+1) * (C (3:K)*X+2) * (C (8:K)*X+7)

theorem upperFilter_degree : (upperFilter : K[X]).natDegree ≤ 4 := by
  have h (a b : K) : (C a*X+C b).natDegree ≤ 1 := by
    have l : (C a * X).natDegree ≤ 1 := (natDegree_C_mul_le _ _).trans (by simp)
    have r : (C b : K[X]).natDegree ≤ 1 := by simp
    simpa only [max_self] using natDegree_add_le_of_le l r
  have h₁ : (C (3:K)*X+1 : K[X]).natDegree ≤ 1 := by
    rw [←show C (1:K) = (1 : K[X]) by rw [map_one]]
    exact h 3 1
  have h₂ : (C (3:K)*X+2 : K[X]).natDegree ≤ 1 := by
    rw [←show C (2:K) = (2 : K[X]) by rw [map_ofNat]]
    exact h 3 2
  have h₃ : (C (8:K)*X+7 : K[X]).natDegree ≤ 1 := by
    rw [←show C (7:K) = (7 : K[X]) by rw [map_ofNat]]
    exact h 8 7
  exact natDegree_mul_le_of_le (natDegree_mul_le_of_le
    (natDegree_mul_le_of_le (by simp : (X : K[X]).natDegree ≤ 1) h₁) h₂) h₃

theorem upperFilter_mulX_degree : ((upperFilter : K[X])*X).natDegree ≤ 5 :=
  natDegree_mul_le_of_le upperFilter_degree (by simp : (X : K[X]).natDegree ≤ 1)

/-- 150150 times the five moments with the factor y−7/20. -/
def coarseCoeffs : Five K := ⟨154312665,125841301,104460713,88068505,75235601⟩

/-- 225225 times the five moments with the factor y−8/15. -/
def strongCoeffs : Five K := ⟨129694110,110704758,94764694,81701830,70994238⟩

theorem upper_coarse_pos (A k : K)
    (hA : 0 ≤ A) (hk : 0 ≤ k)
    (at₂₃ : 0 ≤ A+4/9-(2:K)/3*k)
    (at₃₄ : 0 ≤ A+9/16-(3:K)/4*k)
    (at₉₁₀ : 0 ≤ A+81/100-(9:K)/10*k)
    (at₁ : 0 ≤ A+1-k) {x y : K} (xy : x ≠ 0 ∨ y ≠ 0) :
    0 < upperQ coarseCoeffs A k x y := by
  have vp : 0 < verticalQ (coarseCoeffs : Five K) x y := by
    unfold verticalQ
    exact binaryQ_pos_of_principal _ _ _ (by norm_num [coarseCoeffs])
      (by norm_num [coarseCoeffs]) xy
  have dp : 0 < diagonalQ (coarseCoeffs : Five K) x y := by
    unfold diagonalQ
    exact binaryQ_pos_of_principal _ _ _ (by norm_num [coarseCoeffs])
      (by norm_num [coarseCoeffs]) xy
  have v₀ : 0 < upperQ (coarseCoeffs : Five K) 0 0 x y := by
    unfold upperQ
    exact binaryQ_pos_of_principal _ _ _ (by norm_num [coarseCoeffs])
      (by norm_num [coarseCoeffs]) xy
  have v₁ : 0 < upperQ (coarseCoeffs : Five K) 0 (2/3) x y := by
    unfold upperQ
    exact binaryQ_pos_of_principal _ _ _ (by norm_num [coarseCoeffs])
      (by norm_num [coarseCoeffs]) xy
  have v₂ : 0 < upperQ (coarseCoeffs : Five K) (1/2) (17/12) x y := by
    unfold upperQ
    exact binaryQ_pos_of_principal _ _ _ (by norm_num [coarseCoeffs])
      (by norm_num [coarseCoeffs]) xy
  have v₃ : 0 < upperQ (coarseCoeffs : Five K) (27/40) (33/20) x y := by
    unfold upperQ
    exact binaryQ_pos_of_principal _ _ _ (by norm_num [coarseCoeffs])
      (by norm_num [coarseCoeffs]) xy
  have v₄ : 0 < upperQ (coarseCoeffs : Five K) (9/10) (19/10) x y := by
    unfold upperQ
    exact binaryQ_pos_of_principal _ _ _ (by norm_num [coarseCoeffs])
      (by norm_num [coarseCoeffs]) xy
  by_cases h₁ : k ≤ (2:K)/3
  · refine upper_between coarseCoeffs (k₀ := 0) (k₁ := 2/3) (r := 0) (b := 0)
      hk h₁ (by norm_num) (by simpa using hA) vp ?_ ?_
    · simpa using v₀
    · simpa using v₁
  by_cases h₂ : k ≤ (17:K)/12
  · refine upper_between coarseCoeffs (k₀ := 2/3) (k₁ := 17/12)
      (r := 2/3) (b := -4/9) (le_of_not_ge h₁) h₂ (by norm_num)
      (by linarith only [at₂₃]) vp ?_ ?_
    · rw [show (2:K)/3*(2/3)+(-4/9) = 0 by norm_num]
      exact v₁
    · rw [show (2:K)/3*(17/12)+(-4/9) = 1/2 by norm_num]
      exact v₂
  by_cases h₃ : k ≤ (33:K)/20
  · refine upper_between coarseCoeffs (k₀ := 17/12) (k₁ := 33/20)
      (r := 3/4) (b := -9/16) (le_of_not_ge h₂) h₃ (by norm_num)
      (by linarith only [at₃₄]) vp ?_ ?_
    · rw [show (3:K)/4*(17/12)+(-9/16) = 1/2 by norm_num]
      exact v₂
    · rw [show (3:K)/4*(33/20)+(-9/16) = 27/40 by norm_num]
      exact v₃
  by_cases h₄ : k ≤ (19:K)/10
  · refine upper_between coarseCoeffs (k₀ := 33/20) (k₁ := 19/10)
      (r := 9/10) (b := -81/100) (le_of_not_ge h₃) h₄ (by norm_num)
      (by linarith only [at₉₁₀]) vp ?_ ?_
    · rw [show (9:K)/10*(33/20)+(-81/100) = 27/40 by norm_num]
      exact v₃
    · rw [show (9:K)/10*(19/10)+(-81/100) = 9/10 by norm_num]
      exact v₄
  exact upper_diagonal_tail coarseCoeffs (le_of_not_ge h₄)
    (by linarith only [at₁]) vp dp v₄

theorem upper_strong_pos (A k : K)
    (hA : 0 ≤ A) (hk : 0 ≤ k) (h₁ : k ≤ 1)
    (atHalf : 0 ≤ A+1/4-k/2)
    {x y : K} (xy : x ≠ 0 ∨ y ≠ 0) :
    0 < upperQ strongCoeffs A k x y := by
  have vp : 0 < verticalQ (strongCoeffs : Five K) x y := by
    unfold verticalQ
    exact binaryQ_pos_of_principal _ _ _ (by norm_num [strongCoeffs])
      (by norm_num [strongCoeffs]) xy
  have v₀ : 0 < upperQ (strongCoeffs : Five K) 0 0 x y := by
    unfold upperQ
    exact binaryQ_pos_of_principal _ _ _ (by norm_num [strongCoeffs])
      (by norm_num [strongCoeffs]) xy
  have v₁ : 0 < upperQ (strongCoeffs : Five K) 0 (1/2) x y := by
    unfold upperQ
    exact binaryQ_pos_of_principal _ _ _ (by norm_num [strongCoeffs])
      (by norm_num [strongCoeffs]) xy
  have v₂ : 0 < upperQ (strongCoeffs : Five K) (1/4) 1 x y := by
    unfold upperQ
    exact binaryQ_pos_of_principal _ _ _ (by norm_num [strongCoeffs])
      (by norm_num [strongCoeffs]) xy
  by_cases h : k ≤ (1:K)/2
  · refine upper_between strongCoeffs (k₀ := 0) (k₁ := 1/2) (r := 0) (b := 0)
      hk h (by norm_num) (by simpa using hA) vp ?_ ?_
    · simpa using v₀
    · simpa using v₁
  · refine upper_between strongCoeffs (k₀ := 1/2) (k₁ := 1)
      (r := 1/2) (b := -1/4) (le_of_not_ge h) h₁ (by norm_num)
      (by linarith only [atHalf]) vp ?_ ?_
    · rw [show (1:K)/2*(1/2)+(-1/4) = 0 by norm_num]
      exact v₁
    · rw [show (1:K)/2*1+(-1/4) = 1/4 by norm_num]
      exact v₂

def fixedLower₀ : Five K := ⟨-1084083,115401,128557,99385,75565⟩
def fixedLower₁ : Five K := ⟨-1682109,974831,928083,744495,590275⟩

/-- Anti-diagonals at cut v+1/250 and density 6A+τ, scaled by the
positive factor 250·15015²·(A+1/5). -/
def shiftedSkew (A : K) : Five K :=
  ⟨-9018009-13198500315*A-1352701350*A^2,
   118829139+1644283641*A+15188903730*A^2,
   109392855+1873409109*A+10190350170*A^2,
   88723635+1490365305*A+6962605650*A^2,
   71126055+1158242085*A+5004049050*A^2⟩

def rankTwo (D : Five K) : Prop :=
  ∃ x y : K, ∀ l m : K, l ≠ 0 ∨ m ≠ 0 →
    0 < hankelQ D.a D.b D.c D.d D.e (D.e*l*x) (D.e*l*y) (m-l*(D.c*x+D.d*y))

theorem fixedLower₀_rankTwo : rankTwo (fixedLower₀ : Five K) := by
  unfold rankTwo
  apply hankelQ_rank_two
  · norm_num [fixedLower₀]
  · norm_num [fixedLower₀, hankelDet]

theorem fixedLower₁_rankTwo : rankTwo (fixedLower₁ : Five K) := by
  unfold rankTwo
  apply hankelQ_rank_two
  · norm_num [fixedLower₁]
  · norm_num [fixedLower₁, hankelDet]

private def skewDetPos (A : K) : K :=
  5000000000*(1-1600*A^2)^2 + 6000000000*(1-A)^2 +
    299238245 + 256135365*A + 2928976764905*A^2 +
    684316900149611*A^3 + 1860430070229790*A^4 +
    83011156135607700*A^5 + 115508814788367000*A^6

theorem shiftedSkew_rankTwo (A : K) (hA : 0 ≤ A) : rankTwo (shiftedSkew A) := by
  unfold rankTwo
  apply hankelQ_rank_two
  · unfold shiftedSkew
    change 0 < 71126055+1158242085*A+5004049050*A^2
    positivity
  · have hd : hankelDet (shiftedSkew A).a (shiftedSkew A).b (shiftedSkew A).c
        (shiftedSkew A).d (shiftedSkew A).e = -(525515088384*skewDetPos A) := by
      unfold hankelDet shiftedSkew skewDetPos
      dsimp only
      ring
    rw [hd]
    have hp : 0 < skewDetPos A := by unfold skewDetPos; positivity
    exact neg_lt_zero.mpr (mul_pos (by norm_num) hp)

end
end RKCert.ReviewedNative.CrossedGaussianReference
