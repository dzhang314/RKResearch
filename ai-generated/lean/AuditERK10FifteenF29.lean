import RKCert.ReviewedNative.ERK10FifteenF29
open RKResearch
open RKResearch.Certified.ERK10FifteenF29
example : Modulus = 29 := rfl
example : HasOrder 10 A b := order_ten
example : ERK A ∧ HasOrder 10 A b ∧ ¬ HasOrder 11 A b := exact_zmod
example (R : Type*) [CommRing R] [Nontrivial R] [CharP R 29] :
    ∃ (A : Matrix (Fin 15) (Fin 15) R) (b : Fin 15 → R),
      ERK A ∧ HasOrder 10 A b ∧ ¬ HasOrder 11 A b := exact_of_char R
