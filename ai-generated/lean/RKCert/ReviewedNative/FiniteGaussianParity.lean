module

public import RKCert.ReviewedNative.FiniteGaussianLocalizer
public import Mathlib.Algebra.Polynomial.Eval.SMul
import Lean.Elab.Tactic.Omega
import Mathlib.Tactic.Linarith
import Mathlib.Tactic.NormNum
import Mathlib.Tactic.Positivity
import Mathlib.Tactic.Ring

@[expose] public section

/-! # Finite Gaussian parity filters and two positive directions

Draft. The weighted signed-localizer interface is the audited finite one:
no real closure, analytic integral, or positivity of an extension mesh is used.
-/
namespace RKCert.ReviewedNative.FiniteGaussianLocalizer

open Polynomial
open scoped BigOperators

noncomputable section
variable {K : Type*} [Field K] [LinearOrder K] [IsStrictOrderedRing K]

/-- The two-dimensional positive-square variant of the finite node test. -/
theorem card_pos_ge_two_of_signedLocalizer_rank_two
    {s : Finset K} {μ : K → K} {g P₀ P₁ : K[X]}
    (mass : ∀ x ∈ s, 0 ≤ μ x)
    (pos : ∀ a b : K, a ≠ 0 ∨ b ≠ 0 →
      0 < signedLocalizer s μ g (C a * P₀ + C b * P₁)) :
    2 ≤ (s.filter (fun x => 0 < g.eval x)).card := by
  classical
  let T := s.filter (fun x => 0 < g.eval x)
  change 2 ≤ T.card
  by_contra hn
  have hcard : T.card ≤ 1 := by omega
  have hz : ∃ a b : K, (a ≠ 0 ∨ b ≠ 0) ∧
      ∀ x ∈ T, (C a * P₀ + C b * P₁).eval x = 0 := by
    rcases T.eq_empty_or_nonempty with ht | ⟨x, hx⟩
    · refine ⟨1, 0, Or.inl one_ne_zero, ?_⟩
      simp [ht]
    · have unique : ∀ y ∈ T, y = x :=
        fun y hy => Finset.card_le_one.mp hcard y hy x hx
      by_cases hP : P₀.eval x = 0
      · refine ⟨1, 0, Or.inl one_ne_zero, ?_⟩
        intro y hy
        simpa only [unique y hy, eval_add, eval_mul, eval_C, one_mul, zero_mul,
          add_zero] using hP
      · refine ⟨P₁.eval x, -P₀.eval x, Or.inr (by simpa only [neg_ne_zero] using hP), ?_⟩
        intro y hy
        simp only [unique y hy, eval_add, eval_mul, eval_C]
        ring
  obtain ⟨a, b, hab, kill⟩ := hz
  have hnonpos : signedLocalizer s μ g (C a * P₀ + C b * P₁) ≤ 0 := by
    unfold signedLocalizer
    apply Finset.sum_nonpos
    intro x hx
    by_cases hp : 0 < g.eval x
    · have hmem : x ∈ T := Finset.mem_filter.mpr ⟨hx, hp⟩
      simp [kill x hmem]
    · exact mul_nonpos_of_nonneg_of_nonpos (mass x hx)
        (mul_nonpos_of_nonpos_of_nonneg (le_of_not_gt hp) (sq_nonneg _))
  exact (not_lt_of_ge hnonpos) (pos a b hab)

/-- Use the same finite rank test without assuming more than the paid
degree bound for the underlying signed moments. -/
theorem card_pos_ge_two_of_exact_rank_two
    {s : Finset K} {μ : K → K} {B g P₀ P₁ : K[X]} {d : ℕ}
    (E : K[X] →ₗ[K] K)
    (mass : ∀ x ∈ s, 0 ≤ μ x)
    (exactRule : ∀ Q : K[X], Q.natDegree ≤ g.natDegree + 2*d →
      E (B*Q) = ∑ x ∈ s, μ x * Q.eval x)
    (deg₀ : P₀.natDegree ≤ d) (deg₁ : P₁.natDegree ≤ d)
    (pos : ∀ a b : K, a ≠ 0 ∨ b ≠ 0 →
      0 < E (B * (g * (C a * P₀ + C b * P₁)^2))) :
    2 ≤ (s.filter (fun x => 0 < g.eval x)).card := by
  apply card_pos_ge_two_of_signedLocalizer_rank_two mass
  intro a b hab
  let P : K[X] := C a * P₀ + C b * P₁
  have pd : P.natDegree ≤ d := by
    simpa only [P, max_self] using
      natDegree_add_le_of_le ((natDegree_C_mul_le a P₀).trans deg₀)
        ((natDegree_C_mul_le b P₁).trans deg₁)
  have qd : (g * P^2).natDegree ≤ g.natDegree + 2*d :=
    natDegree_mul_le_of_le (le_refl _) (natDegree_pow_le_of_le 2 pd)
  have h := pos a b hab
  change 0 < E (B * (g * P^2)) at h
  rw [exactRule (g * P^2) qd] at h
  simpa only [signedLocalizer, P, eval_mul, eval_pow] using h

theorem moment_C_mul (E : K[X] →ₗ[K] K) (a : K) (p : K[X]) :
    E (C a * p) = a * E p := by
  rw [← Polynomial.smul_eq_C_mul, map_smul, smul_eq_mul]

/-- Compare two affine density insertions at a threshold. Only the signed
threshold crossing and the explicitly paid square are needed. -/
theorem affine_threshold_pos
    (E : K[X] →ₗ[K] K) (T P : K[X]) {c f₀ f₁ g₀ g₁ ℓ : K}
    (hℓ : 0 < ℓ) (crossing : 0 ≤ f₁-ℓ*g₁)
    (match_at_cut : f₀+f₁*c = ℓ*(g₀+g₁*c))
    (square : 0 ≤ E ((T-C c)^2 * P^2))
    (ref : 0 < E ((T-C c) * (C g₀+C g₁*T) * P^2)) :
    0 < E ((T-C c) * (C f₀+C f₁*T) * P^2) := by
  have hconst : f₀ = ℓ*g₀-(f₁-ℓ*g₁)*c := by
    calc
      f₀ = (f₀+f₁*c)-f₁*c := by ring
      _ = _ := by rw [match_at_cut]; ring
  have hpoly :
      (T-C c) * (C f₀+C f₁*T) * P^2 =
      C ℓ * ((T-C c) * (C g₀+C g₁*T) * P^2) +
        C (f₁-ℓ*g₁) * ((T-C c)^2 * P^2) := by
    rw [hconst]
    simp only [map_sub, map_mul]
    ring
  rw [hpoly, map_add, moment_C_mul, moment_C_mul]
  exact add_pos_of_pos_of_nonneg (mul_pos hℓ ref) (mul_nonneg crossing square)

/-- Shrinking the threshold preserves positive directions whenever the
unlocalized weighted square is nonnegative. -/
theorem move_threshold_down_pos
    (E : K[X] →ₗ[K] K) (T g P : K[X]) {a b : K}
    (hab : b ≤ a) (sq : 0 ≤ E (g*P^2))
    (ref : 0 < E ((T-C a)*g*P^2)) :
    0 < E ((T-C b)*g*P^2) := by
  have hpoly :
      (T-C b)*g*P^2 = (T-C a)*g*P^2 + C (a-b)*(g*P^2) := by
    simp only [map_sub]
    ring
  rw [hpoly, map_add, moment_C_mul]
  exact add_pos_of_pos_of_nonneg ref (mul_nonneg (sub_nonneg.mpr hab) sq)

/-- In the centered coordinate, the residual is a monic quadratic. -/
def centeredResidual (A k : K) : K[X] := C A + X^2 - C k * X

/-- A quadratic in the squared centered coordinate. -/
def evenQuadratic (a b c : K) : K[X] := C a + C b * X^2 + C c * X^4

theorem evenQuadratic_comp_negX (a b c : K) :
    (evenQuadratic a b c).comp (-X) = evenQuadratic a b c := by
  simp only [evenQuadratic, add_comp, mul_comp, pow_comp, C_comp, X_comp]
  ring

theorem evenQuadratic_degree (a b c : K) : (evenQuadratic a b c).natDegree ≤ 4 := by
  unfold evenQuadratic
  have h₀ : (C a : K[X]).natDegree ≤ 4 := by simp
  have h₁ : (C b * X^2).natDegree ≤ 4 :=
    (natDegree_C_mul_X_pow_le b 2).trans (by decide)
  have h₂ : (C c * X^4).natDegree ≤ 4 := natDegree_C_mul_X_pow_le c 4
  have h₀₁ : (C a + C b * X^2).natDegree ≤ 4 := by
    simpa only [max_self] using natDegree_add_le_of_le h₀ h₁
  simpa only [max_self] using natDegree_add_le_of_le h₀₁ h₂

theorem upperParity_degree (t a b c : K) :
    ((X+C t)*evenQuadratic a b c).natDegree ≤ 5 := by
  apply natDegree_mul_le_of_le (m := 1) (n := 4)
  · exact (natDegree_add_le _ _).trans (by simp)
  · exact evenQuadratic_degree a b c

theorem lowerParity_degree (t a b c : K) :
    ((X-C t)*evenQuadratic a b c).natDegree ≤ 5 := by
  apply natDegree_mul_le_of_le (m := 1) (n := 4)
  · exact (natDegree_sub_le _ _).trans (by simp)
  · exact evenQuadratic_degree a b c

/-- Only evenness of the reference functional is needed for the parity
filter. Odd powers need not be separately estimated. -/
theorem parity_upper
    (E : K[X] →ₗ[K] K) (even : ∀ p : K[X], E (p.comp (-X)) = E p)
    (A k t : K) (L : K[X]) (hL : L.comp (-X) = L) :
    E (centeredResidual A k * ((X-C t)*((X+C t)*L)^2)) =
      E ((X^2-C (t^2))*(C (t*A)+C (t-k)*X^2)*L^2) := by
  let F : K[X] := centeredResidual A k * ((X-C t)*((X+C t)*L)^2)
  let G : K[X] := (X^2-C (t^2))*(C (t*A)+C (t-k)*X^2)*L^2
  change E F = E G
  have hpoly : F + F.comp (-X) = C (2 : K)*G := by
    simp only [F, G, centeredResidual, add_comp, sub_comp, mul_comp, pow_comp,
      C_comp, X_comp, hL, C_ofNat, map_sub, map_mul, map_pow]
    ring
  have h := congrArg (fun p : K[X] => E p) hpoly
  change E (F+F.comp (-X)) = E (C (2 : K)*G) at h
  rw [map_add, even F, moment_C_mul] at h
  linarith only [h]

theorem parity_lower
    (E : K[X] →ₗ[K] K) (even : ∀ p : K[X], E (p.comp (-X)) = E p)
    (A k t : K) (L : K[X]) (hL : L.comp (-X) = L) :
    E (centeredResidual A k * ((-X-C t)*((X-C t)*L)^2)) =
      E ((X^2-C (t^2))*(C (t*A)+C (t+k)*X^2)*L^2) := by
  let F : K[X] := centeredResidual A k * ((-X-C t)*((X-C t)*L)^2)
  let G : K[X] := (X^2-C (t^2))*(C (t*A)+C (t+k)*X^2)*L^2
  change E F = E G
  have hpoly : F + F.comp (-X) = C (2 : K)*G := by
    simp only [F, G, centeredResidual, add_comp, sub_comp, neg_comp, mul_comp, pow_comp,
      C_comp, X_comp, hL, C_ofNat, map_add, map_mul, map_pow]
    ring
  have h := congrArg (fun p : K[X] => E p) hpoly
  change E (F+F.comp (-X)) = E (C (2 : K)*G) at h
  rw [map_add, even F, moment_C_mul] at h
  linarith only [h]

/-- Binary symmetric square form. -/
def binaryQ (a b c x y : K) : K := a*x^2 + 2*b*x*y + c*y^2

/-- Ternary symmetric Hankel form, in the monomial basis 1, τ, τ². -/
def hankelQ (a b c d e x y z : K) : K :=
  a*x^2 + 2*b*x*y + c*y^2 + 2*c*x*z + 2*d*y*z + e*z^2

/-- The determinant of the symmetric Hankel matrix with anti-diagonals a through e. -/
def hankelDet (a b c d e : K) : K :=
  a*(c*e-d^2) - b*(b*e-c*d) + c*(b*d-c^2)

theorem binaryQ_pos_of_principal (a b c : K) (ha : 0<a) (hdet : 0<a*c-b^2)
    {x y : K} (h : x ≠ 0 ∨ y ≠ 0) :
    0 < binaryQ a b c x y := by
  have hin : a * binaryQ a b c x y = (a*x+b*y)^2 + (a*c-b^2)*y^2 := by
    unfold binaryQ
    ring
  have hprod : 0 < a * binaryQ a b c x y := by
    rw [hin]
    by_cases hy : y = 0
    · have hx : x ≠ 0 := h.resolve_right (fun hy' => hy' hy)
      subst y
      simpa using sq_pos_of_ne_zero (mul_ne_zero ha.ne' hx)
    · exact add_pos_of_nonneg_of_pos (sq_nonneg _) (mul_pos hdet (sq_pos_of_ne_zero hy))
  exact pos_of_mul_pos_right hprod ha.le

private theorem binaryQ_has_pos (a b c : K) (hdet : a*c-b^2 < 0) :
    ∃ x y : K, 0 < binaryQ a b c x y := by
  rcases lt_trichotomy a 0 with ha | ha | ha
  · refine ⟨-b, a, ?_⟩
    have e : binaryQ a b c (-b) a = a*(a*c-b^2) := by unfold binaryQ; ring
    rw [e]
    exact mul_pos_of_neg_of_neg ha hdet
  · subst a
    have hb : b ≠ 0 := by
      intro e
      subst b
      simp at hdet
    refine ⟨(1-c)*b, 2*b^2, ?_⟩
    have e : binaryQ 0 b c ((1-c)*b) (2*b^2) = 4*b^4 := by unfold binaryQ; ring
    rw [e]
    have hb4 : 0 < b^4 := by
      calc
        0 < (b^2)^2 := pow_pos (sq_pos_of_ne_zero hb) 2
        _ = b^4 := by ring
    exact mul_pos (by norm_num) hb4
  · refine ⟨1, 0, ?_⟩
    simpa [binaryQ] using ha

/-- Explicit Schur-complement construction of two positive directions.
The determinant has negative sign and the last diagonal is positive.
No spectral theorem or existence of square roots is required. -/
theorem hankelQ_rank_two (a b c d e : K) (he : 0<e) (hdet : hankelDet a b c d e < 0) :
    ∃ x y : K, ∀ l m : K, l ≠ 0 ∨ m ≠ 0 →
      0 < hankelQ a b c d e (e*l*x) (e*l*y) (m-l*(c*x+d*y)) := by
  have hs : (a*e-c^2)*(c*e-d^2)-(b*e-c*d)^2 < 0 := by
    have h : (a*e-c^2)*(c*e-d^2)-(b*e-c*d)^2 = e*hankelDet a b c d e := by
      unfold hankelDet
      ring
    rw [h]
    exact mul_neg_of_pos_of_neg he hdet
  obtain ⟨x, y, hxy⟩ := binaryQ_has_pos (a*e-c^2) (b*e-c*d) (c*e-d^2) hs
  refine ⟨x, y, ?_⟩
  intro l m hm
  have h : hankelQ a b c d e (e*l*x) (e*l*y) (m-l*(c*x+d*y)) =
      e * (l^2 * binaryQ (a*e-c^2) (b*e-c*d) (c*e-d^2) x y + m^2) := by
    unfold hankelQ binaryQ
    ring
  rw [h]
  apply mul_pos he
  rcases hm with hl | hm
  · exact add_pos_of_pos_of_nonneg (mul_pos (sq_pos_of_ne_zero hl) hxy) (sq_nonneg _)
  · exact add_pos_of_nonneg_of_pos (mul_nonneg (sq_nonneg _) hxy.le) (sq_pos_of_ne_zero hm)

end
end RKCert.ReviewedNative.FiniteGaussianLocalizer
