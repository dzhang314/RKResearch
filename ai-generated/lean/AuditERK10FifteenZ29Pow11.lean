import RKCert.ReviewedNative.ERK10FifteenZ29Pow11
open RKResearch
open RKResearch.Certified.ERK10FifteenZ29Pow11
example : Modulus = 29^11 := by decide
example : ERK A ∧ HasOrder 10 A b ∧ ¬ HasOrder 11 A b := exact_zmod
example (k : ℕ) (hk : k ≤ 11) (R : Type*) [CommRing R]
    [Nontrivial R] [CharP R (29^k)] :
    ∃ (A : Matrix (Fin 15) (Fin 15) R) (b : Fin 15 → R),
      ERK A ∧ HasOrder 10 A b ∧ ¬ HasOrder 11 A b := by
  apply exact_of_char_dvd R
  change 29^k ∣ 29^11
  exact pow_dvd_pow 29 hk
