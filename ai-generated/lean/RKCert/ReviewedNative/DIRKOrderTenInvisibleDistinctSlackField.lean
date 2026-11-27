module

public import RKCert.ReviewedNative.DIRKOrderTenInvisibleOffSlackField

@[expose] public section

/-! # Marked-block algebra for the two fully distinct invisible slacks

The separate tableau proof supplies actual grading, support, and
ordinary suffix. These lemmas isolate the signed debit and the exact
linear DA compensation; the numerical scalar is the existing
interior-duplicate DA certificate. -/
namespace RKResearch.Certified.Graded.InvisibleDistinctSlackField

open Lean.Grind
open InvisibleOffSlackField (three_reads_live)

section RingGates
variable {K : Type} [CommRing K]

/-- Cleared true first and compensated second moments if the only
nonzero reflected donor label is V. -/
theorem one_label_has_no_debit_polynomial (V b e t : K)
    (h₁ : 2*(V*t)=b*V^2)
    (h₂ : 6*(V^2*t)=(2*b+e)*V^3) :
    (b-e)*V^3=0 := by
  have h : V*(3*(2*(V*t)))=6*(V^2*t) := by grind
  rw [h₁,h₂] at h
  clear h₁ h₂
  grind

/-- The two-node cubic remainder with actual G coefficient e and
cleared compensated third moment. The mass b−e is not assumed positive. -/
theorem one_later_debit_polynomial (U V b e D K₄ u t : K)
    (h₁ : 2*(U*u+V*t)=b*V^2)
    (h₂ : 6*(U^2*u+V^2*t)=(2*b+e)*V^3)
    (h₃ : 4*(U^3*u+V^3*t)=(b+e)*V^4+4*K₄*D-2*e*K₄*V) :
    12*K₄*D-6*e*K₄*V=(b-e)*V^3*(V-2*U) := by
  have he :
      3*(4*(U^3*u+V^3*t)) =
        2*(U+V)*(6*(U^2*u+V^2*t))-6*U*V*(2*(U*u+V*t)) := by
    clear h₁ h₂ h₃
    grind
  rw [h₁,h₂,h₃] at he
  clear h₁ h₂ h₃
  grind

structure Tap (K : Type) where
  b : K
  eta : K
  value : K

def weightRead : List (Tap K) → K
  | [] => 0
  | x::xs => x.b*x.value+weightRead xs

def markedRead : List (Tap K) → K
  | [] => 0
  | x::xs => x.eta*x.value+markedRead xs

def paidRead (d v : K) : List (Tap K) → K
  | [] => 0
  | x::xs => (d*(x.b-x.eta)+v*x.eta)*x.value+paidRead d v xs

/-- The same DA contribution works for any number of earlier physical
rows at the same fixed clock. No individual late weight is divided out. -/
theorem late_block_contribution (d v : K) (xs : List (Tap K)) :
    paidRead d v xs = d*(weightRead xs-markedRead xs)+v*markedRead xs := by
  induction xs with
  | nil =>
    simp only [paidRead,weightRead,markedRead]
    grind
  | cons x xs ih =>
    simp only [paidRead,weightRead,markedRead,ih]
    grind
end RingGates

section FieldGates
variable {K : Type} [Field K]

private theorem cancelScalar (a x : K) (ha : a ≠ 0) (h : a*x=0) : x=0 := by
  have ht := congrArg (fun z => a⁻¹*z) h
  rw [←Semiring.mul_assoc, Field.inv_mul_cancel ha, Semiring.one_mul, Semiring.mul_zero] at ht
  exact ht

theorem one_label_has_no_debit (V b e t : K) (hV : V≠0)
    (h₁ : 2*(V*t)=b*V^2) (h₂ : 6*(V^2*t)=(2*b+e)*V^3) : b=e := by
  have hh := one_label_has_no_debit_polynomial V b e t h₁ h₂
  have h : V*(V*(V*(b-e)))=0 := by grind
  have q := cancelScalar V _ hV (cancelScalar V _ hV (cancelScalar V _ hV h))
  grind

/-- Every interpolation weight for evaluation at zero on three
distinct nonzero heads is itself nonzero. -/
theorem three_nonzero_head_weights (a b c wa wb wc m : K)
    (ha : a≠0) (hb : b≠0) (hc : c≠0) (hm : m≠0)
    (hd₁ : a-b≠0) (hd₂ : a-c≠0) (hd₃ : b-c≠0)
    (h₀ : wa+wb+wc=m)
    (h₁ : wa*a+wb*b+wc*c=0) (h₂ : wa*a^2+wb*b^2+wc*c^2=0) :
    wa≠0 ∧ wb≠0 ∧ wc≠0 := by
  have ne : ¬(a*wa=0 ∧ b*wb=0 ∧ c*wc=0) := by
    rintro ⟨x,y,z⟩
    have xa := cancelScalar a wa ha x
    have xb := cancelScalar b wb hb y
    have xc := cancelScalar c wc hc z
    exact hm (by grind)
  obtain ⟨A,B,C⟩ := three_reads_live a b c (a*wa) (b*wb) (c*wc)
    hd₁ hd₂ hd₃ (by grind) (by grind) ne
  exact ⟨by intro e; exact A (by simp [e,Semiring.mul_zero]),
    by intro e; exact B (by simp [e,Semiring.mul_zero]),
    by intro e; exact C (by simp [e,Semiring.mul_zero])⟩

theorem debit_from_distinct_weighted_head (b h hJ : K)
    (hb : b≠0) (hJ₀ : hJ≠0) (hd : hJ-h≠0) :
    b-(b*h)/hJ≠0 := by
  intro hzero
  have ii := Field.mul_inv_cancel hJ₀
  rw [Field.div_eq_mul_inv] at hzero
  have h : b*(hJ-h)=0 := by grind
  exact hd (cancelScalar b _ hb h)

theorem marked_mass (b e bJ : K) (hbJ : bJ≠0) :
    b-(e/bJ)*bJ=b-e := by
  rw [Field.div_eq_mul_inv,Semiring.mul_assoc,Field.inv_mul_cancel hbJ,Semiring.mul_one]

/-- DA on the latest marked receiver, when the only two rows from
its reflected label in the suffix are k and j. -/
theorem two_row_marked_da (e bJ V d t : K) (hbJ : bJ≠0) :
    (e*d+bJ*t)*d+(bJ*(V/2))*(t-(e/bJ)*(V/2)) =
      ((e*d+bJ*t)-(e/bJ)*(bJ*(V/2)))*(d+V/2) := by
  have ii := Field.mul_inv_cancel hbJ
  simp only [Field.div_eq_mul_inv]
  grind
end FieldGates

end RKResearch.Certified.Graded.InvisibleDistinctSlackField
