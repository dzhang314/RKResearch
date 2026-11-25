module

public import RKCert.ReviewedNative.CrossedGaussianReference
public import RKCert.ReviewedNative.CrossedGaussianScalar
import Lean.Elab.Tactic.Omega
import Mathlib.Tactic.FieldSimp
import Mathlib.Tactic.IntervalCases
import Mathlib.Tactic.Linarith
import Mathlib.Tactic.NormNum
import Mathlib.Tactic.Ring

@[expose] public section

/-! # Bridge between the paid polynomial moments and the exact matrix certificates

Draft. This file introduces only polynomial identities and scalar moment
expansions. Normalized reference moment delivery is supplied separately by
the checked order-19 rational integration rule / formal primitive.
-/
namespace RKCert.ReviewedNative.CrossedGaussianMomentLift

open Polynomial
open RKCert.ReviewedNative.FiniteGaussianLocalizer
open RKCert.ReviewedNative.CrossedGaussianReference
open RKCert.ReviewedNative.CrossedGaussianScalar
open scoped BigOperators

noncomputable section
variable {K : Type*} [Field K] [LinearOrder K] [IsStrictOrderedRing K]

/-- The normalized moments of the (1−y²) reference on [−1,1]. -/
def refMoment (K : Type*) [Field K] (n : ℕ) : K :=
  if n % 2 = 0 then 3 / ((n+1 : ℕ) : K) / ((n+3 : ℕ) : K) else 0

def ReferencePowers (E : K[X] →ₗ[K] K) : Prop :=
  ∀ n : ℕ, n ≤ 13 → E (X^n) = refMoment K n

def affineSquare (x y : K) : K[X] := C x+C y*X

/-- Exact moment expansion; not an implication based on moment signs. -/
theorem affine_square_binary (E : K[X] →ₗ[K] K) (F : K[X]) (x y : K) :
    E (F*(affineSquare x y)^2) = binaryQ (E F) (E (F*X)) (E (F*X^2)) x y := by
  have hp : F*(affineSquare x y)^2 =
      C (x^2)*F+C (2*x*y)*(F*X)+C (y^2)*(F*X^2) := by
    simp only [affineSquare, map_mul, map_pow, C_ofNat]
    ring
  rw [hp]
  simp only [map_add, moment_C_mul, binaryQ]
  ring

def tauHankel (E : K[X] →ₗ[K] K) (F : K[X]) : Five K :=
  ⟨E F,E (F*X^2),E (F*X^4),E (F*X^6),E (F*X^8)⟩

theorem even_square_hankel (E : K[X] →ₗ[K] K) (F : K[X]) (x y z : K) :
    E (F*(evenQuadratic x y z)^2) =
      hankelQ (tauHankel E F).a (tauHankel E F).b (tauHankel E F).c
        (tauHankel E F).d (tauHankel E F).e x y z := by
  have hp : F*(evenQuadratic x y z)^2 =
      C (x^2)*F + C (2*x*y)*(F*X^2) +
      C (y^2+2*x*z)*(F*X^4) + C (2*y*z)*(F*X^6) + C (z^2)*(F*X^8) := by
    simp only [evenQuadratic,map_add,map_mul,map_pow,C_ofNat]
    ring
  rw [hp]
  simp only [map_add E, moment_C_mul, tauHankel, hankelQ]
  ring

def tauFactor (t a b : K) : K[X] := (X^2-C t)*(C a+C b*X^2)

theorem tau_entry (E : K[X] →ₗ[K] K) (t a b : K) (j : ℕ) :
    E (tauFactor t a b*X^(2*j)) =
      b*E (X^(2*j+4))+(a-t*b)*E (X^(2*j+2))-t*a*E (X^(2*j)) := by
  have hp : tauFactor t a b*X^(2*j) =
      C b*X^(2*j+4)+C (a-t*b)*X^(2*j+2)-C (t*a)*X^(2*j) := by
    simp only [tauFactor,map_sub,map_mul,pow_add]
    ring
  rw [hp]
  simp only [map_sub E, map_add E, moment_C_mul]

def tauRaw (E : K[X] →ₗ[K] K) (t a b : K) (j : ℕ) : K :=
  E (tauFactor t a b*X^(2*j))

theorem tauHankel_eq_raw (E : K[X] →ₗ[K] K) (t a b : K) :
    tauHankel E (tauFactor t a b) =
      ⟨tauRaw E t a b 0,tauRaw E t a b 1,tauRaw E t a b 2,
       tauRaw E t a b 3,tauRaw E t a b 4⟩ := by
  simp [tauHankel,tauRaw]

theorem tauRaw_closed (E : K[X] →ₗ[K] K) (hp : ReferencePowers E)
    (t a b : K) (j : ℕ) (hj : j ≤ 4) :
    tauRaw E t a b j = b*refMoment K (2*j+4)+(a-t*b)*refMoment K (2*j+2)-
      t*a*refMoment K (2*j) := by
  change ∀ n : ℕ, n ≤ 13 → E (X^n) = refMoment K n at hp
  rw [tauRaw,tau_entry,hp (2*j+4) (by omega),hp (2*j+2) (by omega),hp (2*j) (by omega)]

def upperUscaled (K : Type*) [Field K] (j : ℕ) : K :=
  match j with
  | 0 => 37009050
  | 1 => 28384434
  | 2 => 22518682
  | 3 => 18327610
  | 4 => 15221514
  | 5 => 12851090
  | _ => 0

theorem upperFilter_sq_times (j : ℕ) :
    (upperFilter : K[X])^2*X^j =
      C (196:K)*X^(j+2)+C (2212:K)*X^(j+3)+C (10021:K)*X^(j+4)+
      C (23346:K)*X^(j+5)+C (29601:K)*X^(j+6)+C (19440:K)*X^(j+7)+
      C (5184:K)*X^(j+8) := by
  simp only [upperFilter,pow_add,C_ofNat]
  ring

theorem upperU_mom (E : K[X] →ₗ[K] K) (hp : ReferencePowers E)
    (j : ℕ) (hj : j ≤ 5) :
    E ((upperFilter : K[X])^2*X^j) = upperUscaled K j / 15015 := by
  change ∀ n : ℕ, n ≤ 13 → E (X^n) = refMoment K n at hp
  rw [upperFilter_sq_times]
  simp only [map_add,moment_C_mul]
  interval_cases j <;> norm_num [ReferencePowers, hp, refMoment, upperUscaled]

def upperRaw (E : K[X] →ₗ[K] K) (t : K) (j : ℕ) : K :=
  E ((X-C t)*(upperFilter : K[X])^2*X^j)

theorem upperRaw_mom (E : K[X] →ₗ[K] K) (hp : ReferencePowers E)
    (t : K) (j : ℕ) (hj : j ≤ 4) :
    upperRaw E t j = (upperUscaled K (j+1)-t*upperUscaled K j)/15015 := by
  unfold upperRaw
  have hp' : (X-C t)*(upperFilter : K[X])^2*X^j =
      (upperFilter : K[X])^2*X^(j+1)-C t*((upperFilter : K[X])^2*X^j) := by
    simp only [pow_succ]
    ring
  rw [hp',map_sub,moment_C_mul,upperU_mom E hp (j+1) (Nat.succ_le_succ hj),
    upperU_mom E hp j (hj.trans (by decide))]
  ring

def rawFive (E : K[X] →ₗ[K] K) (t : K) : Five K :=
  ⟨upperRaw E t 0,upperRaw E t 1,upperRaw E t 2,upperRaw E t 3,upperRaw E t 4⟩

def scaleFive (c : K) (M : Five K) : Five K :=
  ⟨c*M.a,c*M.b,c*M.c,c*M.d,c*M.e⟩

theorem coarseTauFive (E : K[X] →ₗ[K] K) (hp : ReferencePowers E) :
    scaleFive (484*15015) (tauHankel E (tauFactor (((13:K)/22)^2) 1 0)) = fixedLower₀ := by
  simp [scaleFive,tauHankel_eq_raw,fixedLower₀,tauRaw_closed E hp,
    refMoment,Five.mk.injEq] <;> norm_num

theorem strongTauFive (E : K[X] →ₗ[K] K) (hp : ReferencePowers E) :
    scaleFive (8*625*15015) (tauHankel E (tauFactor (((16:K)/25)^2) (1/8) 1)) = fixedLower₁ := by
  simp [scaleFive,tauHankel_eq_raw,fixedLower₁,tauRaw_closed E hp,
    refMoment,Five.mk.injEq] <;> norm_num

theorem shiftedTauFive (E : K[X] →ₗ[K] K) (hp : ReferencePowers E)
    (A : K) (hA : 0 ≤ A) :
    scaleFive (250*15015^2*(A+1/5))
      (tauHankel E (tauFactor (centerSecond A+1/250) (6*A) 1)) = shiftedSkew A := by
  have hW : 5*A+1 ≠ 0 := (show 0 < 5*A+1 by linarith only [hA]).ne'
  simp [scaleFive,tauHankel_eq_raw,shiftedSkew,tauRaw_closed E hp,
    refMoment,Five.mk.injEq,centerSecond,massFactor]
  field_simp [hW] <;> (try ring) <;> simp

theorem upperQ_scale (c : K) (M : Five K) (A k x y : K) :
    upperQ (scaleFive c M) A k x y = c*upperQ M A k x y := by
  simp only [upperQ,scaleFive,binaryQ]
  ring

def fiveHankelQ (D : Five K) (x y z : K) : K := hankelQ D.a D.b D.c D.d D.e x y z

theorem fiveHankelQ_scale (c : K) (M : Five K) (x y z : K) :
    fiveHankelQ (scaleFive c M) x y z = c*fiveHankelQ M x y z := by
  simp only [scaleFive,fiveHankelQ,hankelQ]
  ring

/-- A reference rank certificate supplies two explicit even polynomials. -/
theorem two_even_tests (E : K[X] →ₗ[K] K) (F : K[X]) {c : K} (D : Five K)
    (hc : 0 < c) (hD : scaleFive c (tauHankel E F) = D) (hr : rankTwo D) :
    ∃ L₀ L₁ : K[X], L₀.natDegree ≤ 4 ∧ L₁.natDegree ≤ 4 ∧
      L₀.comp (-X) = L₀ ∧ L₁.comp (-X) = L₁ ∧
      ∀ l m : K, l ≠ 0 ∨ m ≠ 0 → 0 < E (F*(C l*L₀+C m*L₁)^2) := by
  obtain ⟨x,y,h⟩ := hr
  let L₀ := evenQuadratic (D.e*x) (D.e*y) (-(D.c*x+D.d*y))
  let L₁ := evenQuadratic (0:K) 0 1
  refine ⟨L₀,L₁,evenQuadratic_degree _ _ _,evenQuadratic_degree _ _ _,
    evenQuadratic_comp_negX _ _ _,evenQuadratic_comp_negX _ _ _,?_⟩
  intro l m hm
  have id : C l*L₀+C m*L₁ =
      evenQuadratic (D.e*l*x) (D.e*l*y) (m-l*(D.c*x+D.d*y)) := by
    simp only [L₀,L₁,evenQuadratic,map_add,map_sub,map_neg,map_mul,map_zero,map_one]
    ring
  have good : 0 < fiveHankelQ D (D.e*l*x) (D.e*l*y) (m-l*(D.c*x+D.d*y)) := h l m hm
  rw [id,even_square_hankel]
  have eq := congrArg (fun C => fiveHankelQ C (D.e*l*x) (D.e*l*y) (m-l*(D.c*x+D.d*y))) hD
  rw [fiveHankelQ_scale] at eq
  rw [← eq] at good
  exact pos_of_mul_pos_right good hc.le

theorem coarseRawFive (E : K[X] →ₗ[K] K) (hp : ReferencePowers E) :
    scaleFive 150150 (rawFive E (7/20)) = coarseCoeffs := by
  simp [scaleFive,rawFive,coarseCoeffs,upperRaw_mom E hp,
    upperUscaled,Five.mk.injEq] <;> norm_num

theorem strongRawFive (E : K[X] →ₗ[K] K) (hp : ReferencePowers E) :
    scaleFive 225225 (rawFive E (8/15)) = strongCoeffs := by
  simp [scaleFive,rawFive,strongCoeffs,upperRaw_mom E hp,
    upperUscaled,Five.mk.injEq] <;> norm_num

theorem upper_square_raw (E : K[X] →ₗ[K] K) (A k t x y : K) :
    E (centeredResidual A k*((X-C t)*((upperFilter : K[X])*affineSquare x y)^2)) =
      upperQ (rawFive E t) A k x y := by
  let F : K[X] := (X-C t)*(upperFilter : K[X])^2
  let B : K[X] := centeredResidual A k
  have hi (j : ℕ) : E (B*F*X^j) =
      A*upperRaw E t j+upperRaw E t (j+2)-k*upperRaw E t (j+1) := by
    have hpoly : B*F*X^j =
        C A*(F*X^j)+F*X^(j+2)-C k*(F*X^(j+1)) := by
      simp only [B,centeredResidual,pow_add]
      ring
    rw [hpoly]
    simp only [map_sub,map_add,moment_C_mul,F,upperRaw]
  have hpoly : B*((X-C t)*((upperFilter : K[X])*affineSquare x y)^2) =
      (B*F)*(affineSquare x y)^2 := by unfold F; ring
  change E (B*((X-C t)*((upperFilter : K[X])*affineSquare x y)^2)) = _
  rw [hpoly,affine_square_binary]
  have h₀ := hi 0
  have h₁ := hi 1
  have h₂ := hi 2
  simp only [Nat.reduceAdd,pow_zero,pow_one,mul_one] at h₀ h₁ h₂
  rw [h₀,h₁,h₂]
  rfl

/-- The only reference exactness paid by the signed Gaussian frame. -/
def CenteredExact (E : K[X] →ₗ[K] K) (s : Finset K) (μ : K → K) (A k : K) : Prop :=
  ∀ P : K[X], P.natDegree ≤ 11 →
    E (centeredResidual A k * P) = ∑ y ∈ s, μ y * P.eval y

theorem upper_rank_exit (E : K[X] →ₗ[K] K) (s : Finset K) (μ : K → K)
    (A k t : K) (mass : ∀ y ∈ s, 0 ≤ μ y) (quad : CenteredExact E s μ A k)
    (pos : ∀ a b : K, a ≠ 0 ∨ b ≠ 0 → 0 < upperQ (rawFive E t) A k a b) :
    2 ≤ (s.filter (fun y => t < y)).card := by
  classical
  have degG : (X-C t : K[X]).natDegree ≤ 1 := (natDegree_sub_le _ _).trans (by simp)
  have h := card_pos_ge_two_of_exact_rank_two (s := s) (μ := μ) (B := centeredResidual A k)
    (g := X-C t) (P₀ := upperFilter) (P₁ := (upperFilter : K[X])*X) (d := 5)
    E mass (fun Q dQ => quad Q (dQ.trans (by omega)))
    (upperFilter_degree.trans (by decide)) upperFilter_mulX_degree (by
      intro a b hab
      have hP : C a*(upperFilter : K[X])+C b*((upperFilter : K[X])*X) =
          (upperFilter : K[X])*affineSquare a b := by unfold affineSquare; ring
      rw [hP,upper_square_raw]
      exact pos a b hab)
  simpa only [eval_sub,eval_X,eval_C,sub_pos] using h

theorem upper_parity_rank_exit (E : K[X] →ₗ[K] K) (s : Finset K) (μ : K → K)
    (A k t : K) (mass : ∀ y ∈ s, 0 ≤ μ y) (quad : CenteredExact E s μ A k)
    (even : ∀ p : K[X], E (p.comp (-X)) = E p) {L₀ L₁ : K[X]}
    (dd₀ : L₀.natDegree ≤ 4) (dd₁ : L₁.natDegree ≤ 4)
    (ev₀ : L₀.comp (-X) = L₀) (ev₁ : L₁.comp (-X) = L₁)
    (pos : ∀ a b : K, a ≠ 0 ∨ b ≠ 0 →
      0 < E (tauFactor (t^2) (t*A) (t-k) * (C a*L₀+C b*L₁)^2)) :
    2 ≤ (s.filter (fun y => t < y)).card := by
  classical
  have degG : (X-C t : K[X]).natDegree ≤ 1 := (natDegree_sub_le _ _).trans (by simp)
  have degX : (X+C t : K[X]).natDegree ≤ 1 := (natDegree_add_le _ _).trans (by simp)
  have h := card_pos_ge_two_of_exact_rank_two (s := s) (μ := μ) (B := centeredResidual A k)
    (g := X-C t) (P₀ := (X+C t)*L₀) (P₁ := (X+C t)*L₁) (d := 5)
    E mass (fun Q dQ => quad Q (dQ.trans (by omega)))
    (natDegree_mul_le_of_le degX dd₀) (natDegree_mul_le_of_le degX dd₁) (by
      intro a b hab
      let L : K[X] := C a*L₀+C b*L₁
      have hL : L.comp (-X) = L := by simp only [L,add_comp,mul_comp,C_comp,ev₀,ev₁]
      have hP : C a*((X+C t)*L₀)+C b*((X+C t)*L₁) = (X+C t)*L := by unfold L; ring
      rw [hP,parity_upper E even A k t L hL]
      exact pos a b hab)
  simpa only [eval_sub,eval_X,eval_C,sub_pos] using h

theorem lower_parity_rank_exit (E : K[X] →ₗ[K] K) (s : Finset K) (μ : K → K)
    (A k t : K) (mass : ∀ y ∈ s, 0 ≤ μ y) (quad : CenteredExact E s μ A k)
    (even : ∀ p : K[X], E (p.comp (-X)) = E p) {L₀ L₁ : K[X]}
    (dd₀ : L₀.natDegree ≤ 4) (dd₁ : L₁.natDegree ≤ 4)
    (ev₀ : L₀.comp (-X) = L₀) (ev₁ : L₁.comp (-X) = L₁)
    (pos : ∀ a b : K, a ≠ 0 ∨ b ≠ 0 →
      0 < E (tauFactor (t^2) (t*A) (t+k) * (C a*L₀+C b*L₁)^2)) :
    2 ≤ (s.filter (fun y => y < -t)).card := by
  classical
  have degG : (-X-C t : K[X]).natDegree ≤ 1 := (natDegree_sub_le _ _).trans (by simp)
  have degX : (X-C t : K[X]).natDegree ≤ 1 := (natDegree_sub_le _ _).trans (by simp)
  have h := card_pos_ge_two_of_exact_rank_two (s := s) (μ := μ) (B := centeredResidual A k)
    (g := -X-C t) (P₀ := (X-C t)*L₀) (P₁ := (X-C t)*L₁) (d := 5)
    E mass (fun Q dQ => quad Q (dQ.trans (by omega)))
    (natDegree_mul_le_of_le degX dd₀) (natDegree_mul_le_of_le degX dd₁) (by
      intro a b hab
      let L : K[X] := C a*L₀+C b*L₁
      have hL : L.comp (-X) = L := by simp only [L,add_comp,mul_comp,C_comp,ev₀,ev₁]
      have hP : C a*((X-C t)*L₀)+C b*((X-C t)*L₁) = (X-C t)*L := by unfold L; ring
      rw [hP,parity_lower E even A k t L hL]
      exact pos a b hab)
  have hp0 (y : K) : (0 < (-X-C t : K[X]).eval y) ↔ y < -t := by
    simp only [eval_sub,eval_neg,eval_X,eval_C]
    constructor <;> intro h' <;> linarith only [h']
  simpa only [hp0] using h

/-- The unscaled normalization in the signed-moment exit. -/
theorem centered_pair_moment (E : K[X] →ₗ[K] K) (hp : ReferencePowers E)
    (A k R S : K) (hA : 0 ≤ A) :
    E (centeredResidual A k*((X-C R)*(X-C S))) =
      (massFactor A/5)*pairValue (centerMean A k) (centerSecond A) R S := by
  have m₀ : E (1 : K[X]) = 1 := by simpa [refMoment] using hp 0 (by decide)
  have m₁ : E (X : K[X]) = 0 := by simpa [refMoment] using hp 1 (by decide)
  have m₂ : E ((X : K[X])^2) = 1/5 := by
    have h := hp 2 (by decide)
    norm_num [refMoment] at h ⊢
    exact h
  have m₃ : E ((X : K[X])^3) = 0 := by simpa [refMoment] using hp 3 (by decide)
  have m₄ : E ((X : K[X])^4) = 3/35 := by
    have h := hp 4 (by decide)
    norm_num [refMoment] at h ⊢
    exact h
  have p :
      centeredResidual A k*((X-C R)*(X-C S)) =
      X^4-C (k+R+S)*X^3+C (A+k*(R+S)+R*S)*X^2-
        C (A*(R+S)+k*R*S)*X+C (A*R*S)*1 := by
    simp only [centeredResidual,map_add,map_mul]
    ring
  have hW : massFactor A ≠ 0 := (show 0 < massFactor A by
    unfold massFactor
    linarith only [hA]).ne'
  rw [p]
  simp only [map_add E,map_sub E,moment_C_mul,m₀,m₁,m₂,m₃,m₄]
  unfold pairValue centerMean centerSecond
  field_simp [hW] <;> simp only [massFactor] <;> ring

end
end RKCert.ReviewedNative.CrossedGaussianMomentLift
