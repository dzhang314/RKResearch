module

public import RKCert.ReviewedNative.WeakFiveThreeInteriorLocalizer
public import Mathlib.Algebra.BigOperators.Fin

import Mathlib.Tactic.NormNum
import Lean.Elab.Tactic.Omega
import Mathlib.Tactic.Ring
import Mathlib.Tactic.Positivity

@[expose] public section

/-! # Six-moment integer checking for the literal ThreeInterior ports

A fraction is not reduced. Multiplying by a root factor sends adjacent
moments `M[j], M[j+1]` to `d*M[j+1]-n*M[j]`. At the leaves the same
two root moments test both density ends. Only the semantic soundness
lemma uses a field or polynomials. -/
namespace RKCert.ReviewedNative.ThreeInteriorPencil

open Polynomial RKCert.Endpoint RKCert.ReviewedNative.PositiveRule19
open RKCert.ReviewedNative.PolynomialCertificate.WeakFiveCells
open RKCert.ReviewedNative.OrderedPolynomialSignStrips (indexedHull)
open scoped Polynomial BigOperators

/-- A homogeneous coordinate with the sign of its denominator checked by
the original cell's interval guards. -/
structure PortFraction where
  num : ℤ
  den : ℤ

def PortFraction.value {K : Type*} [Field K] (a : PortFraction) : K :=
  (a.num:K)/(a.den:K)

private theorem PortFraction.den_mul_value (a : PortFraction) (h : 0 < a.den) :
    (a.den:ℚ)*a.value = (a.num:ℚ) := by
  have hq : 0 < (a.den:ℚ) := by exact_mod_cast h
  unfold PortFraction.value
  rw [mul_comm, div_mul_cancel₀ _ hq.ne']

structure PortMoments where
  m0 : ℤ
  m1 : ℤ
  m2 : ℤ
  m3 : ℤ
  m4 : ℤ
  m5 : ℤ

def PortMoments.get (m : PortMoments) : ℕ → ℤ
  | 0 => m.m0
  | 1 => m.m1
  | 2 => m.m2
  | 3 => m.m3
  | 4 => m.m4
  | 5 => m.m5
  | _ => 0

/-- Start with 840 times the first six moments of the selected cap. -/
def portBaseMoments : Bool → ℕ → PortMoments
  | false, 1 => ⟨420,280,210,168,140,120⟩
  | false, 2 => ⟨280,210,168,140,120,105⟩
  | true, 1 => ⟨420,140,70,42,28,20⟩
  | true, 2 => ⟨280,70,28,14,8,5⟩
  | _, _ => ⟨0,0,0,0,0,0⟩

def PortMoments.shift (m : PortMoments) (a : PortFraction) : PortMoments :=
  ⟨a.den*m.m1-a.num*m.m0, a.den*m.m2-a.num*m.m1, a.den*m.m3-a.num*m.m2,
    a.den*m.m4-a.num*m.m3, a.den*m.m5-a.num*m.m4, 0⟩

def PortMoments.atGamma (m : PortMoments) (g : PortFraction) : ℤ :=
  (g.den-g.num)*m.m0+g.num*m.m1

def checkIntegerSign (positive : Bool) (v : ℤ) : Bool :=
  if positive then decide (0<v) else decide (v<0)

/-- Each root axis is checked on both sides; at the leaf both
density endpoints are tested with the same two moments. -/
def checkPortRootCorners : (n : ℕ) → PortMoments →
    (Fin n → Bool → PortFraction) → (Bool → PortFraction) → Bool → Bool
  | 0, m, _, g, positive =>
      checkIntegerSign positive (m.atGamma (g false)) &&
        checkIntegerSign positive (m.atGamma (g true))
  | n+1, m, a, g, positive =>
      checkPortRootCorners n (m.shift (a 0 false)) (fun i => a i.succ) g positive &&
        checkPortRootCorners n (m.shift (a 0 true)) (fun i => a i.succ) g positive

private def PortMoments.represents (m : PortMoments) (scale : ℚ) (P : ℚ[X])
    (width : ℕ) : Prop :=
  ∀ j, j < width → (m.get j:ℚ) = scale * integral 0 1 (P * X^j)

private theorem unitIntegralPow (n : ℕ) :
    integral (0:ℚ) 1 (X^n) = ((n:ℚ)+1)⁻¹ := by
  have nz : (n:ℚ)+1 ≠ 0 := (show 0 < (n:ℚ)+1 by positivity).ne'
  have repr : formalPrimitive (X^n : ℚ[X]) = C ((n:ℚ)+1)⁻¹ * X^(n+1) := by
    apply eq_of_derivative_and_eval_zero
    · rw [derivative_formalPrimitive, derivative_C_mul, derivative_X_pow_succ, ← mul_assoc,
        ← C_mul, inv_mul_cancel₀ nz, C_1, one_mul]
    · simp
  rw [integral_zero_left, repr]
  simp

private theorem unitIntegralLeft (p j : ℕ) :
    integral (0:ℚ) 1 (X^p*X^j) = (((p+j:ℕ):ℚ)+1)⁻¹ := by
  rw [← pow_add, unitIntegralPow]

private theorem unitIntegralRightOne (j : ℕ) :
    integral (0:ℚ) 1 ((1-X)*X^j) = ((j:ℚ)+1)⁻¹ - (((j+1:ℕ):ℚ)+1)⁻¹ := by
  have split : (1-X)*(X:ℚ[X])^j = X^j-X^(j+1) := by rw [pow_succ]; ring
  rw [split, (integral (0:ℚ) 1).map_sub, unitIntegralPow, unitIntegralPow]

private theorem unitIntegralRightOne_pow (j : ℕ) :
    integral (0:ℚ) 1 ((1-X)^1*X^j) = ((j:ℚ)+1)⁻¹ - (((j+1:ℕ):ℚ)+1)⁻¹ := by
  simpa only [pow_one] using unitIntegralRightOne j

private theorem unitIntegralRightTwo (j : ℕ) :
    integral (0:ℚ) 1 ((1-X)^2*X^j) =
      ((j:ℚ)+1)⁻¹ - 2*(((j+1:ℕ):ℚ)+1)⁻¹ + (((j+2:ℕ):ℚ)+1)⁻¹ := by
  have split : (1-X)^2*(X:ℚ[X])^j = X^j-C 2*X^(j+1)+X^(j+2) := by
    rw [pow_add (X:ℚ[X]) j 1, pow_add (X:ℚ[X]) j 2]
    simp only [C_ofNat, pow_one]
    ring
  rw [split, (integral (0:ℚ) 1).map_add, (integral (0:ℚ) 1).map_sub,
    threeInterior_integral_C_mul, unitIntegralPow, unitIntegralPow, unitIntegralPow]

private theorem portBaseMoments_spec (right : Bool) {p : ℕ} (hp : p=1 ∨ p=2) :
    (portBaseMoments right p).represents 840 (threeInteriorCap right ^ p) 6 := by
  intro j hj
  have h : j=0 ∨ j=1 ∨ j=2 ∨ j=3 ∨ j=4 ∨ j=5 := by omega
  cases right with
  | false =>
      rcases hp with rfl | rfl <;>
        rcases h with rfl | rfl | rfl | rfl | rfl | rfl <;>
        simp only [portBaseMoments, PortMoments.get, threeInteriorCap, unitIntegralLeft] <;> norm_num
  | true =>
      rcases hp with rfl | rfl <;>
        rcases h with rfl | rfl | rfl | rfl | rfl | rfl <;>
        simp only [portBaseMoments, PortMoments.get, threeInteriorCap,
          unitIntegralRightOne_pow, unitIntegralRightTwo] <;> norm_num

private theorem PortMoments.get_shift (m : PortMoments) (a : PortFraction)
    {j : ℕ} (h : j < 5) :
    (m.shift a).get j = a.den*m.get (j+1)-a.num*m.get j := by
  have ex : j=0 ∨ j=1 ∨ j=2 ∨ j=3 ∨ j=4 := by omega
  rcases ex with rfl | rfl | rfl | rfl | rfl <;> rfl

private theorem PortMoments.shift_spec {m : PortMoments} {scale : ℚ} {P : ℚ[X]}
    {n : ℕ} (h : m.represents scale P (n+1)) (hn : n ≤ 5) (a : PortFraction)
    (dn : 0 < a.den) :
    (m.shift a).represents (scale*(a.den:ℚ)) (P*(X-C a.value)) n := by
  intro j hj
  have z : (P*(X-C a.value))*X^j = P*X^(j+1)-C a.value*(P*X^j) := by
    rw [pow_succ]
    ring
  rw [m.get_shift a (hj.trans_le hn), Int.cast_sub, Int.cast_mul, Int.cast_mul,
    h (j+1) (Nat.succ_lt_succ hj), h j (hj.trans (Nat.lt_succ_self n)),
    z, (integral (0:ℚ) 1).map_sub, threeInterior_integral_C_mul, ← a.den_mul_value dn]
  ring

private theorem PortMoments.gamma_spec {m : PortMoments} {scale : ℚ} {P : ℚ[X]}
    (h : m.represents scale P 2) (scale0 : 0 < scale) (g : PortFraction)
    (g0 : 0 < g.den) (positive : Bool)
    (pass : checkIntegerSign positive (m.atGamma g) = true) :
    threeInteriorSigned positive
      (integral 0 1 (P * threeInteriorResidual (1-g.value))) := by
  have v : (g.den:ℚ)*g.value = (g.num:ℚ) := g.den_mul_value g0
  have m0 : (m.m0:ℚ) = scale * integral 0 1 P := by
    simpa only [PortMoments.get,pow_zero,mul_one] using h 0 (by decide)
  have m1 : (m.m1:ℚ) = scale * integral 0 1 (P*X) := by
    simpa only [PortMoments.get,pow_one] using h 1 (by decide)
  have z : P*threeInteriorResidual (1-g.value) =
      C (1-g.value)*P+C g.value*(P*X) := by
    simp only [threeInteriorResidual, sub_sub_cancel]
    ring
  have eq : (m.atGamma g : ℚ) = (scale*(g.den:ℚ))*
      integral 0 1 (P*threeInteriorResidual (1-g.value)) := by
    simp only [PortMoments.atGamma,Int.cast_add,Int.cast_mul,Int.cast_sub,m0,m1]
    rw [z, (integral (0:ℚ) 1).map_add, threeInterior_integral_C_mul,
      threeInterior_integral_C_mul, ← v]
    ring
  have mul0 : 0 < scale*(g.den:ℚ) := mul_pos scale0 (by exact_mod_cast g0)
  cases positive
  · have zI : m.atGamma g < 0 := of_decide_eq_true pass
    have zQ : (m.atGamma g : ℚ) < 0 := by exact_mod_cast zI
    rw [eq] at zQ
    change _ < (0:ℚ)
    exact lt_of_not_ge (fun hn => (not_lt_of_ge (mul_nonneg mul0.le hn)) zQ)
  · have zI : 0 < m.atGamma g := of_decide_eq_true pass
    have zQ : (0:ℚ) < (m.atGamma g : ℚ) := by exact_mod_cast zI
    rw [eq] at zQ
    change (0:ℚ) < _
    exact (mul_pos_iff_of_pos_left mul0).mp zQ

private theorem rootCorners_sound (n : ℕ) :
    ∀ (m : PortMoments) (a : Fin n → Bool → PortFraction)
      (g : Bool → PortFraction) (positive : Bool) (scale : ℚ) (P : ℚ[X]),
      n ≤ 4 → m.represents scale P (n+2) → 0 < scale →
      (∀ i b, 0 < (a i b).den) → (∀ b, 0 < (g b).den) →
      checkPortRootCorners n m a g positive = true →
      ∀ (v : Fin n → Bool) (b : Bool), threeInteriorSigned positive
        (integral 0 1 ((P * ∏ i, (X-C (a i (v i)).value)) *
          threeInteriorResidual (1-(g b).value))) := by
  induction n with
  | zero =>
      intro m a g positive scale P hn spec scale0 a0 g0 h v b
      have h' := Bool.and_eq_true_iff.mp (show
        (checkIntegerSign positive (m.atGamma (g false)) &&
          checkIntegerSign positive (m.atGamma (g true))) = true from h)
      cases b
      · simpa only [Fin.prod_univ_zero,mul_one] using
          PortMoments.gamma_spec (m := m) spec scale0 (g false) (g0 false) positive h'.1
      · simpa only [Fin.prod_univ_zero,mul_one] using
          PortMoments.gamma_spec (m := m) spec scale0 (g true) (g0 true) positive h'.2
  | succ n ih =>
      intro m a g positive scale P hn spec scale0 a0 g0 h v b
      let q := a 0 (v 0)
      have q0 : 0 < q.den := a0 0 (v 0)
      have spec' : (m.shift q).represents (scale*(q.den:ℚ)) (P*(X-C q.value)) (n+2) :=
        PortMoments.shift_spec (m := m) spec (by omega) q q0
      have h' := Bool.and_eq_true_iff.mp (show
        (checkPortRootCorners n (m.shift (a 0 false)) (fun i => a i.succ) g positive &&
          checkPortRootCorners n (m.shift (a 0 true)) (fun i => a i.succ) g positive) = true from h)
      have tail : checkPortRootCorners n (m.shift q) (fun i => a i.succ) g positive = true := by
        cases h0 : v 0
        · simpa only [q,h0] using h'.1
        · simpa only [q,h0] using h'.2
      have s := ih (m.shift q) (fun i => a i.succ) g positive _
        (P*(X-C q.value)) (by omega) spec' (mul_pos scale0 (by exact_mod_cast q0))
        (fun i e => a0 i.succ e) g0 tail (fun i => v i.succ) b
      simpa only [Fin.prod_univ_succ,mul_assoc,q] using s

/-- Full strict check of the rational localizer pencil, not a point sampling
lemma. The selected end of every root coordinate and of gamma is arbitrary. -/
theorem portRootCorners_sound {n p : ℕ} {right positive : Bool}
    (hp : p=1 ∨ p=2) (hn : n≤4) (a : Fin n → Bool → PortFraction)
    (g : Bool → PortFraction) (a0 : ∀ i b, 0 < (a i b).den)
    (g0 : ∀ b, 0 < (g b).den)
    (h : checkPortRootCorners n (portBaseMoments right p) a g positive = true)
    (v : Fin n → Bool) (b : Bool) :
    threeInteriorSigned positive
      (threeInteriorLocalizerPencil right p
        (Fin.cons ((g b).value (K := ℚ)) (fun i => (a i (v i)).value))) := by
  rw [threeInteriorLocalizerPencil_cons]
  have base : (portBaseMoments right p).represents 840 (threeInteriorCap right ^ p) (n + 2) := by
    intro j hj
    exact portBaseMoments_spec right hp j (by omega)
  have z := rootCorners_sound n (portBaseMoments right p) a g positive 840
    (threeInteriorCap right ^ p) hn base
    (by norm_num) a0 g0 h v b
  change threeInteriorSigned positive (integral 0 1
    (threeInteriorCap right^p * (threeInteriorResidual (1-(g b).value) *
      indexedHull (fun i => (a i (v i)).value) Finset.univ)))
  have reorder :
      ((threeInteriorCap right : ℚ[X])^p * ∏ i, (X-C (a i (v i)).value)) *
          threeInteriorResidual (1-(g b).value) =
        (threeInteriorCap right^p * (threeInteriorResidual (1-(g b).value) *
          indexedHull (fun i => (a i (v i)).value) Finset.univ)) := by
    unfold indexedHull
    ac_rfl
  rwa [reorder] at z

end RKCert.ReviewedNative.ThreeInteriorPencil
