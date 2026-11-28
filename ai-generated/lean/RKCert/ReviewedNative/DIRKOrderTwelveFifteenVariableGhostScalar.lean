import Mathlib.Tactic.LinearCombination
import Mathlib.Tactic.Ring
import Mathlib.Algebra.Polynomial.FieldDivision
import Mathlib.Algebra.Order.Field.Basic
import Mathlib.Tactic.NormNum

/-! Scalar field gates used by the genuine two- and three-pair DIRK12
    chronology arguments. No signs, stage coefficients, or order hypotheses
    are inferred here. -/
namespace RKResearch.Certified.Graded.OrderTwelveFifteen.VariableGhostScalar

open Polynomial

variable {K : Type*} [Field K] [CharZero K]

/-- The two scalar moments of a cubic with zero constant coefficient. -/
theorem cubicMomentLine (a c₁ c₂ c₃ : K) (ha : a ≠ 0)
    (h₁ : 30*c₁ + 20*a*c₂ + 15*a^2*c₃ = 0)
    (h₂ : 20*c₁ + 15*a*c₂ + 12*a^2*c₃ = 0) :
    c₁ = 3*a^2*c₃/10 ∧ c₂ = -(6*a*c₃/5) := by
  have h : a * (c₂ + 6*a*c₃/5) = 0 := by
    linear_combination (3/5)*h₂ - (2/5)*h₁
  have hc₂ : c₂ = -(6*a*c₃/5) :=
    eq_neg_of_add_eq_zero_left ((mul_eq_zero.mp h).resolve_left ha)
  have hc₁ : c₁ = 3*a^2*c₃/10 := by
    linear_combination h₁/30 - (2*a/3)*hc₂
  exact ⟨hc₁, hc₂⟩

/-- A moment-zero cubic also vanishes at either paid Radau donor. -/
theorem cubicMomentDonor (a d c₁ c₂ c₃ : K) (ha : a ≠ 0)
    (h₁ : 30*c₁ + 20*a*c₂ + 15*a^2*c₃ = 0)
    (h₂ : 20*c₁ + 15*a*c₂ + 12*a^2*c₃ = 0)
    (hd : 10*d^2 - 12*a*d + 3*a^2 = 0) :
    c₁*d + c₂*d^2 + c₃*d^3 = 0 := by
  obtain ⟨hc₁,hc₂⟩ := cubicMomentLine a c₁ c₂ c₃ ha h₁ h₂
  linear_combination d*hc₁ + d^2*hc₂ + (d*c₃/10)*hd

/-- The exact scalar primitive of X(X-d)(X-v)(X-u) after the two
    true first-singleton Radau equations. -/
theorem radauQuarticPrimitive (d v u x : K)
    (h₁ : 5*(d+v) = 6*u) (h₂ : 10*d*v = 3*u^2) :
    x^5/5 - (d+v+u)*x^4/4 + (d*v+(d+v)*u)*x^3/3 - d*v*u*x^2/2 =
      x^2*(x-u)^2*(4*x-3*u)/20 := by
  linear_combination (-x^4/20+u*x^3/15)*h₁ + (x^3/30-u*x^2/20)*h₂

/-- Two donor pivot factors that are units over the exact characteristic-zero
    field whenever the singleton clock is nonzero. -/
theorem radauGuard (u x : K) (hu : u ≠ 0)
    (h : 10*x^2 - 12*u*x + 3*u^2 = 0) :
    4*x ≠ 3*u ∧ 3*x ≠ 2*u := by
  constructor
  · intro e
    have e' : x = 3*u/4 := by linear_combination e/4
    rw [e'] at h
    have hu2 : u^2 = 0 := by linear_combination (-8/3)*h
    exact (pow_ne_zero 2 hu) hu2
  · intro e
    have e' : x = 2*u/3 := by linear_combination e/3
    rw [e'] at h
    have hu2 : u^2 = 0 := by linear_combination (-9/5)*h
    exact (pow_ne_zero 2 hu) hu2

omit [CharZero K] in
/-- The two scalar jets of B=X²(X-a)² and (X-w)B cannot both be
    implemented by one diagonal at w. The second derivative is B(w). -/
theorem twoCleanReceiverJets (a w diag : K) (hw : w ≠ 0) (hwa : w ≠ a)
    (h₁ : w^2*(w-a)^2 = diag*(2*w*(w-a)^2+2*w^2*(w-a)))
    (h₂ : 0 = diag*(w^2*(w-a)^2)) : False := by
  have hB : w^2*(w-a)^2 ≠ 0 := mul_ne_zero (pow_ne_zero 2 hw)
    (pow_ne_zero 2 (sub_ne_zero.mpr hwa))
  have hd : diag = 0 := (mul_eq_zero.mp h₂.symm).resolve_right hB
  rw [hd, zero_mul] at h₁
  exact hB h₁


omit [CharZero K] in
/-- There is no nonzero polynomial of degree at most five with three distinct
    double roots. This is the primitive contradiction in the spent-pair cut. -/
theorem noThreeDoubleRoots (p : K[X]) (a b c : K) (hab : a ≠ b)
    (hac : a ≠ c) (hbc : b ≠ c) (hdeg : p.natDegree ≤ 5)
    (ha : p.IsRoot a ∧ p.derivative.IsRoot a)
    (hb : p.IsRoot b ∧ p.derivative.IsRoot b)
    (hc : p.IsRoot c ∧ p.derivative.IsRoot c) : p = 0 := by
  by_contra hp
  classical
  let M := Multiset.replicate 2 a + Multiset.replicate 2 b + Multiset.replicate 2 c
  have ma : 2 ≤ p.rootMultiplicity a :=
    (Polynomial.one_lt_rootMultiplicity_iff_isRoot hp).mpr ha
  have mb : 2 ≤ p.rootMultiplicity b :=
    (Polynomial.one_lt_rootMultiplicity_iff_isRoot hp).mpr hb
  have mc : 2 ≤ p.rootMultiplicity c :=
    (Polynomial.one_lt_rootMultiplicity_iff_isRoot hp).mpr hc
  have hm : M ≤ p.roots := by
    refine Multiset.le_iff_count.mpr ?_
    intro t
    simp only [M, Multiset.count_add, Multiset.count_replicate, Polynomial.count_roots]
    by_cases ta : t = a
    · subst t
      simpa [hab.symm, hac.symm] using ma
    by_cases tb : t = b
    · subst t
      simpa [hab, hbc.symm] using mb
    by_cases tc : t = c
    · subst t
      simpa [hac, hbc] using mc
    simp [Ne.symm ta, Ne.symm tb, Ne.symm tc]
  have h6 : 6 ≤ p.roots.card := by simpa [M] using Multiset.card_le_card hm
  have hnat := h6.trans (Polynomial.card_roots' p)
  omega

omit [CharZero K] in
/-- Polynomial form of the two real receiver tests; apart from the imported
    field operations, this lemma only uses product differentiation. -/
theorem twoCleanPrimitives (a w diag : K) (hw : w ≠ 0) (hwa : w ≠ a)
    (h₁ : (X^2*(X-C a)^2 : K[X]).eval w =
      diag*(X^2*(X-C a)^2 : K[X]).derivative.eval w)
    (h₂ : ((X^2*(X-C a)^2)*(X-C w) : K[X]).eval w =
      diag*((X^2*(X-C a)^2)*(X-C w) : K[X]).derivative.eval w) : False := by
  let B : K[X] := X^2*(X-C a)^2
  change B.eval w = diag*B.derivative.eval w at h₁
  change (B*(X-C w)).eval w = diag*(B*(X-C w)).derivative.eval w at h₂
  have nz : B.eval w ≠ 0 := by
    simpa [B] using mul_ne_zero (pow_ne_zero 2 hw) (pow_ne_zero 2 (sub_ne_zero.mpr hwa))
  have jet : 0 = diag*B.eval w := by simpa [Polynomial.derivative_mul] using h₂
  have hd : diag = 0 := (mul_eq_zero.mp jet.symm).resolve_right nz
  rw [hd, zero_mul] at h₁
  exact nz h₁

/-- The scalar stop before a spent pair has a definite, denominator-cleared
    gate over every ordered field, with no assumption that the clock is positive. -/
theorem spentSign {L : Type*} [Field L] [LinearOrder L] [IsStrictOrderedRing L]
    (s t : L) (hs : s ≠ 0) :
    s^5/5 - (s+2*t)*s^4/4 + (2*s*t+t^2)*s^3/3 - s^3*t^2/2 ≠ 0 := by
  have h : s^5/5 - (s+2*t)*s^4/4 + (2*s*t+t^2)*s^3/3 - s^3*t^2/2 =
      -(s^3 * (s^2 + 5*(s-2*t)^2)) / 120 := by ring
  rw [h]
  have hpos : 0 < s^2 + 5*(s-2*t)^2 :=
    add_pos_of_pos_of_nonneg (sq_pos_of_ne_zero hs)
      (mul_nonneg (by norm_num) (sq_nonneg (s-2*t)))
  exact div_ne_zero (neg_ne_zero.mpr (mul_ne_zero (pow_ne_zero 3 hs) (ne_of_gt hpos))) (by norm_num)

#print axioms noThreeDoubleRoots
#print axioms twoCleanPrimitives
#print axioms spentSign
#print axioms cubicMomentLine
#print axioms cubicMomentDonor
#print axioms radauQuarticPrimitive
#print axioms radauGuard
#print axioms twoCleanReceiverJets

end RKResearch.Certified.Graded.OrderTwelveFifteen.VariableGhostScalar
