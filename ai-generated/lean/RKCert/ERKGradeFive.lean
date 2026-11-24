module

public import RKCert.GradeFiveReduction
public import RKCert.CaseIIStage
public import RKCert.CharZeroTransfer

@[expose] public section

/-! # The characteristic-zero grade-five surplus and ERK lower bounds

The normalized-case assumptions are proved from the actual strictly lower
tableau and its separated stage profiles. The dimension transfer back to
the full order equations is independent of weights and node multiplicities.
-/
namespace RKCert.Paired
open Module

variable {K : Type*} [Field K] [CharZero K] {s p : ℕ}

/-- Every characteristically zero strictly explicit stage algebra separated
through grade five has at least five independent pure defects there. -/
theorem grade_five_surplus {A : Fin s → Fin s → K}
    (ha : StrictLower A) (hsep : Separated A 5) :
    5 ≤ finrank K (zeroSpace A 5) := by
  by_contra! h
  obtain ⟨m,B,hB,h1,hs,hrows,h3,h4,h5⟩ :=
    exists_normalized_minimal_five_eigen_profile ha hsep (by omega)
  have hcast : Fin.castLE (show 5≤m+5 by omega) (1:Fin 5) = (1:Fin (m+5)) := by
    apply Fin.ext
    rfl
  apply CaseII.compressed_caseII_impossible hB (by omega)
  · rwa [hcast]
  · simpa only [one_div] using hs
  · exact h3
  · exact h4
  · exact h5
  · exact hrows

/-- The original denominator-cleared conditions alone force the stronger
characteristic-zero explicit stage floor for all p ≥ 10. -/
theorem erk_stage_surplus_charZero_field {A : Fin s → Fin s → K} {b : Vec K s}
    (ha : StrictLower A) (ho : HasTreeOrderAtLeast A b p) (hp : 10 ≤ p) :
    (3*p+1)/2-1 ≤ s := by
  have hs := explicit_order_le_stages ha ho
  have hsep : Separated A 5 := explicit_separated ha ho (by omega) (by omega)
  exact stage_surplus_of_five_rank ha ho hp (grade_five_surplus ha hsep)

end RKCert.Paired

namespace RKCert

/-- The characteristic-zero scope also allows zero divisors: specialize
to a field retaining every positive integer scalar. -/
theorem erk_stage_surplus_charZero {R : Type*} [CommRing R] [CharZero R] {s p : ℕ}
    {A : Fin s → Fin s → R} {b : Fin s → R}
    (ha : StrictLower A) (ho : HasTreeOrderAtLeast A b p) (hp : 10 ≤ p) :
    (3*p+1)/2-1 ≤ s :=
  explicit_of_charZero_fields (fun _ _ _ _ _ hA hO =>
    Paired.erk_stage_surplus_charZero_field hA hO hp) ha ho

theorem explicit_order10_ge14_charZero {R : Type*} [CommRing R] [CharZero R] {s : ℕ}
    {A : Fin s → Fin s → R} {b : Fin s → R}
    (ha : StrictLower A) (ho : HasTreeOrderAtLeast A b 10) : 14 ≤ s := by
  exact erk_stage_surplus_charZero ha ho (by decide)

theorem explicit_order11_ge16_charZero {R : Type*} [CommRing R] [CharZero R] {s : ℕ}
    {A : Fin s → Fin s → R} {b : Fin s → R}
    (ha : StrictLower A) (ho : HasTreeOrderAtLeast A b 11) : 16 ≤ s := by
  exact erk_stage_surplus_charZero ha ho (by decide)

theorem explicit_order12_ge17_charZero {R : Type*} [CommRing R] [CharZero R] {s : ℕ}
    {A : Fin s → Fin s → R} {b : Fin s → R}
    (ha : StrictLower A) (ho : HasTreeOrderAtLeast A b 12) : 17 ≤ s := by
  exact erk_stage_surplus_charZero ha ho (by decide)

end RKCert
