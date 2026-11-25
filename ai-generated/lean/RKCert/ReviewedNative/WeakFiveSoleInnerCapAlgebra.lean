module

public import RKCert.ReviewedNative.FiniteGaussianGridPositivity
public import Mathlib.Data.Fin.VecNotation

import Mathlib.Tactic.FinCases
import Mathlib.Tactic.NormNum
import Mathlib.Tactic.Ring

@[expose] public section

/-! # Four-axis affine algebra for the two paid right-window phases

The two exterior affine coefficients add to one. After eliminating the
second coefficient, the four-axis signed test has only sixteen vertices.
The same scalar formula handles the two phases by signed root shifts. -/
namespace RKCert.ReviewedNative.WeakFiveSoleInnerUniform

open Polynomial RKCert.Endpoint
open RKCert.ReviewedNative.PositiveRule19
open RKCert.ReviewedNative.FiniteGaussianGridPositivity

inductive Phase where
  | A
  | B
  deriving DecidableEq

def Phase.zIndex : Phase → Fin 6
  | .A => 1
  | .B => 0

def Phase.rootIndex : Phase → Fin 3 → Fin 6
  | .A => ![0,2,4]
  | .B => ![1,3,5]

/-- The five pure moments times 420. Four consecutive differences
produce each four-entry affine row exactly. -/
def Phase.scaledBase : Phase → Fin 5 → ℤ
  | .A => ![70,35,21,14,10]
  | .B => ![140,35,14,7,4]

def pick {T : Type*} (lo hi : T) : Bool → T
  | false => lo
  | true => hi

noncomputable section
variable {K : Type*} [Field K] [LinearOrder K] [IsStrictOrderedRing K]

def Phase.weight (p : Phase) : K[X] :=
  match p with
  | .A => unitWeight K
  | .B => (1-X)^2

def gammaPolynomial (g : K) : K[X] := C (1-g)+C g*X

def Phase.mixedPower (p : Phase) (j : Fin 4) (g : K) : K :=
  ((p.scaledBase j.castSucc : K) +
    g*((p.scaledBase j.succ : K)-(p.scaledBase j.castSucc : K)))/420

/-- The three inputs after gamma are signed shifts: every factor is
(X+t_i). This unifies ((X+e)(X-l)(X-k)) with the three negative shifts. -/
def signedTest (p : Phase) (g a b c : K) : K :=
  p.mixedPower 3 g + (a+b+c)*p.mixedPower 2 g +
    (a*b+a*c+b*c)*p.mixedPower 1 g + (a*b*c)*p.mixedPower 0 g

private theorem unit_power_cap (n : ℕ) :
    integral (0 : K) 1 (X^n) = 1/((n+1 : ℕ) : K) := by
  rw [←monomial_one_right_eq_X_pow,integral_zero_left]
  simp [formalPrimitive,support_monomial n (one_ne_zero : (1 : K) ≠ 0)]

private theorem pure_power (p : Phase) (j : Fin 5) :
    integral (0 : K) 1 (p.weight*X^j.val) = (p.scaledBase j : K)/420 := by
  cases p
  · have e : unitWeight K*X^j.val = X^(j.val+1)-X^(j.val+2) := by
      simp only [unitWeight,pow_succ]
      ring
    change integral 0 1 (unitWeight K*X^j.val) = _
    rw [e,map_sub,unit_power_cap,unit_power_cap]
    fin_cases j <;> norm_num [Phase.scaledBase]
  · have e : ((1-X)^2 : K[X])*X^j.val =
        X^j.val - C (2 : K)*X^(j.val+1)+X^(j.val+2) := by
      simp only [pow_succ,map_ofNat]
      ring
    change integral 0 1 (((1-X)^2 : K[X])*X^j.val) = _
    rw [e]
    simp only [map_add,map_sub,←Polynomial.smul_eq_C_mul,map_smul,smul_eq_mul,unit_power_cap]
    fin_cases j <;> norm_num [Phase.scaledBase]

private theorem mixed_power (p : Phase) (j : Fin 4) (g : K) :
    integral (0 : K) 1 (p.weight*gammaPolynomial g*X^j.val) = p.mixedPower j g := by
  have e : p.weight*gammaPolynomial g*X^j.val =
      C (1-g)*(p.weight*X^j.castSucc.val) + C g*(p.weight*X^j.succ.val) := by
    change p.weight*gammaPolynomial g*X^j.val =
      C (1-g)*(p.weight*X^j.val) + C g*(p.weight*X^(j.val+1))
    simp only [gammaPolynomial,pow_succ]
    ring
  rw [e]
  simp only [map_add,←Polynomial.smul_eq_C_mul,map_smul,smul_eq_mul,pure_power,Phase.mixedPower]
  ring

theorem test_eq_integral (p : Phase) (g a b c : K) :
    integral 0 1 (p.weight*gammaPolynomial g*((X+C a)*(X+C b)*(X+C c))) =
      signedTest p g a b c := by
  have e : p.weight*gammaPolynomial g*((X+C a)*(X+C b)*(X+C c)) =
      p.weight*gammaPolynomial g*X^3+
      C (a+b+c)*(p.weight*gammaPolynomial g*X^2)+
      C (a*b+a*c+b*c)*(p.weight*gammaPolynomial g*X^1)+
      C (a*b*c)*(p.weight*gammaPolynomial g*X^0) := by
    simp only [map_add,map_mul,pow_zero,pow_one,pow_succ]
    ring
  have m0 : integral 0 1 (p.weight*gammaPolynomial g*X^0) = p.mixedPower 0 g :=
    mixed_power p 0 g
  have m1 : integral 0 1 (p.weight*gammaPolynomial g*X^1) = p.mixedPower 1 g :=
    mixed_power p 1 g
  have m2 : integral 0 1 (p.weight*gammaPolynomial g*X^2) = p.mixedPower 2 g :=
    mixed_power p 2 g
  have m3 : integral 0 1 (p.weight*gammaPolynomial g*X^3) = p.mixedPower 3 g :=
    mixed_power p 3 g
  rw [e]
  simp only [map_add (integral (0 : K) 1),←Polynomial.smul_eq_C_mul,map_smul,smul_eq_mul,m0,m1,m2,m3,signedTest]

/-- An affine function has one endpoint at least as large as its value
at a boxed point, including when the interval is degenerate. -/
def EndpointAffine (f : K → K) : Prop :=
  ∀ x, f x = f 0 + x*(f 1-f 0)

theorem affine_le_of_endpoints {f : K → K} (aff : EndpointAffine f)
    {l x h cap : K} (lx : l≤x) (xh : x≤h) (lo : f l≤cap) (hi : f h≤cap) : f x≤cap := by
  by_cases s : 0≤f 1-f 0
  · have m := mul_le_mul_of_nonneg_right xh s
    have e : f x≤f h := by rw [aff x,aff h]; exact add_le_add (le_refl (f 0)) m
    exact e.trans hi
  · have m := mul_le_mul_of_nonpos_right lx (le_of_not_ge s)
    have e : f x≤f l := by rw [aff x,aff l]; exact add_le_add (le_refl (f 0)) m
    exact e.trans lo

/-- A generic four-axis signed bound: exactly sixteen vertices suffice. -/
theorem four_affine_le_of_vertices (f : K → K → K → K → K)
    (gA : ∀ a b c, EndpointAffine (fun g => f g a b c))
    (aA : ∀ g b c, EndpointAffine (fun a => f g a b c))
    (bA : ∀ g a c, EndpointAffine (fun b => f g a b c))
    (cA : ∀ g a b, EndpointAffine (fun c => f g a b c))
    {g a b c gl gh al ah bl bh cl ch cap : K}
    (hg : gl≤g ∧ g≤gh) (ha : al≤a ∧ a≤ah) (hb : bl≤b ∧ b≤bh) (hc : cl≤c ∧ c≤ch)
    (vertices : ∀ g a b c : Bool,
      f (pick gl gh g) (pick al ah a) (pick bl bh b) (pick cl ch c)≤cap) :
    f g a b c≤cap := by
  have cStep (i j k : Bool) : f (pick gl gh i) (pick al ah j) (pick bl bh k) c≤cap :=
    affine_le_of_endpoints (cA _ _ _) hc.1 hc.2 (vertices i j k false) (vertices i j k true)
  have bStep (i j : Bool) : f (pick gl gh i) (pick al ah j) b c≤cap :=
    affine_le_of_endpoints (bA _ _ _) hb.1 hb.2 (cStep i j false) (cStep i j true)
  have aStep (i : Bool) : f (pick gl gh i) a b c≤cap :=
    affine_le_of_endpoints (aA _ _ _) ha.1 ha.2 (bStep i false) (bStep i true)
  exact affine_le_of_endpoints (gA _ _ _) hg.1 hg.2 (aStep false) (aStep true)

theorem signedTest_le_of_vertices (p : Phase) {g a b c gl gh al ah bl bh cl ch cap : K}
    (hg : gl≤g ∧ g≤gh) (ha : al≤a ∧ a≤ah) (hb : bl≤b ∧ b≤bh) (hc : cl≤c ∧ c≤ch)
    (vertices : ∀ g a b c : Bool, signedTest p
      (pick gl gh g) (pick al ah a) (pick bl bh b) (pick cl ch c)≤cap) :
    signedTest p g a b c≤cap := by
  apply four_affine_le_of_vertices (signedTest p) _ _ _ _ hg ha hb hc vertices
  all_goals
    intro i j k x
    simp only [signedTest,Phase.mixedPower]
    ring

end
end RKCert.ReviewedNative.WeakFiveSoleInnerUniform
