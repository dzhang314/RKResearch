module

public import RKCert.ReviewedNative.WeakFiveInteriorRemainder

@[expose] public section

/-! # Native weak-five scalar classifier and explicit remaining obligations

All branches consume the same original source Moments. The classifier
has already removed lower degree, opposite outer exterior directions,
both wrong inner directions, multiple exterior labels, four interior
changes, and the genuinely crossed positive tail. No separate weak-four
or held fibre enters.
-/

namespace RKCert.ReviewedNative.PolynomialCertificate.WeakFiveCells

open Polynomial
open RKCert.ReviewedNative.WeakFive16
open RKCert.ReviewedNative.OrderedRootGapSaturation
open RKCert.ReviewedNative.WeakFiveCrossedPositiveTail
open scoped Polynomial

universe u
variable {K : Type u} [Field K] [LinearOrder K] [IsStrictOrderedRing K]

/-- The actual sole-outer alternatives. The strict relative ordering of
the other inner mark is a proved square-balance consequence. -/
def SoleOuter (c : Fin 5 → K) : Prop :=
  (c 4 < 0 ∧ MarkInterior c 1 ∧ MarkInterior c 2 ∧ MarkInterior c 3 ∧ c 1 < c 3) ∨
  (1 < c 1 ∧ MarkInterior c 2 ∧ MarkInterior c 3 ∧ MarkInterior c 4 ∧ c 2 < c 4)

/-- The sole-inner alternatives already contain three simple unit roots,
a proved strict exterior root gap, and overlap of the two true end windows. -/
def SoleInner (q : K[X]) (c : Fin 5 → K) : Prop :=
  c 4 < c 1 ∧
  ((c 2 < 0 ∧ MarkInterior c 1 ∧ MarkInterior c 3 ∧ MarkInterior c 4 ∧
    ∃ E : OrderedExtension K, ∃ (r : Fin 3 → E.carrier) (e : E.carrier),
      ExteriorRootLayout (q.map E.embed) r e (E.embed (c 2)) 0) ∨
   (1 < c 3 ∧ MarkInterior c 1 ∧ MarkInterior c 2 ∧ MarkInterior c 4 ∧
    ∃ E : OrderedExtension K, ∃ (r : Fin 3 → E.carrier) (e : E.carrier),
      ExteriorRootLayout (q.map E.embed) r e 1 (E.embed (c 3))))

def ThreeInterior (q : K[X]) (c : Fin 5 → K) : Prop :=
  AllFourMarksInterior c ∧
  ∃ E : OrderedExtension K, ∃ (r : Fin 3 → E.carrier) (e : E.carrier),
    ThreeChangeLayout (q.map E.embed) r e

def CrossedNegative (q Z : K[X]) (c : Fin 5 → K) : Prop :=
  ∃ E : OrderedExtension K, ∃ (r s b₀ b₁ : E.carrier),
    NegativeTailPacket (monicProfile (q.map E.embed)) (Z.map E.embed)
      (fun i => E.embed (c i)) r s b₀ b₁

/-- Common classifier for the real remaining scalar leaves. The two
interior alternatives are exact, not epistemic "at least" conditions. -/
theorem actual_weak_five_remaining_sectors {q Z : K[X]} {c : Fin 5 → K} (M : Moments q Z c) :
    SoleOuter c ∨ SoleInner q c ∨ ThreeInterior q c ∨ CrossedNegative q Z c := by
  rcases actual_mark_sector M with marks | ⟨z,u,a,h⟩ | ⟨u,a,h,z⟩ | ⟨a,u,h,z⟩ | ⟨h,u,a,z⟩
  · rcases actual_interior_remainder M marks with three | negative
    · exact Or.inr (Or.inr (Or.inl ⟨marks,three⟩))
    · exact Or.inr (Or.inr (Or.inr negative))
  · exact Or.inl (Or.inl ⟨z,u,a,h,outer_left_u_lt_h M z u h⟩)
  · exact Or.inl (Or.inr ⟨u,a,h,z,outer_right_a_lt_z M u a z⟩)
  · obtain ⟨overlap,layout⟩ := inner_left_exact_layout M a u z
    exact Or.inr (Or.inl ⟨overlap,Or.inl ⟨a,u,h,z,layout⟩⟩)
  · obtain ⟨overlap,layout⟩ := inner_right_exact_layout M h u z
    exact Or.inr (Or.inl ⟨overlap,Or.inr ⟨h,u,a,z,layout⟩⟩)

/-- Explicit producer-to-consumer handoff. No classical exhaustive branch
or table theorem is silently assumed. This is a conditional assembly, not
a claim that these four endpoint obligations have been formally discharged. -/
theorem no_weak_five_from_remaining_scalar_endpoints {q Z : K[X]} {c : Fin 5 → K}
    (M : Moments q Z c)
    (outer : SoleOuter c → False) (inner : SoleInner q c → False)
    (three : ThreeInterior q c → False) (negative : CrossedNegative q Z c → False) : False := by
  rcases actual_weak_five_remaining_sectors M with ext | ext | tr | neg
  · exact outer ext
  · exact inner ext
  · exact three tr
  · exact negative neg

end RKCert.ReviewedNative.PolynomialCertificate.WeakFiveCells
