module

public import RKCert.ReviewedNative.ERK10SixteenF11
public import RKCert.ReviewedNative.ERK10SixteenF13
public import RKCert.ReviewedNative.ERK10SixteenF17
public import RKCert.ReviewedNative.ERK10SixteenF19
public import RKCert.ReviewedNative.ERK10SixteenF23

public section

namespace RKResearch.Certified.ERK10PrimeFieldTransfer

open RKResearch FiniteRootedTree
open scoped Matrix FiniteRootedTree

theorem exact_of_injective_hom
    {S R : Type*} [CommRing S] [CommRing R]
    {A : Matrix (Fin 16) (Fin 16) S} {b : Fin 16 → S}
    (f : S →+* R) (hf : Function.Injective f)
    (h : ERK A ∧ HasOrder 10 A b ∧ ¬ HasOrder 11 A b) :
    ERK (A.map f) ∧ HasOrder 10 (A.map f) (f ∘ b) ∧
      ¬ HasOrder 11 (A.map f) (f ∘ b) := by
  refine ⟨?_, h.2.1.map f, ?_⟩
  · intro i j hij
    change f (A i j) = 0
    rw [h.1 hij, map_zero]
  · intro hz
    exact h.2.2 ((hasOrder_map_iff (f := f) hf).mp hz)

theorem exact_of_char11 (R : Type*) [CommRing R] [Nontrivial R] [CharP R 11] :
    ∃ (A : Matrix (Fin 16) (Fin 16) R) (b : Fin 16 → R),
      ERK A ∧ HasOrder 10 A b ∧ ¬ HasOrder 11 A b := by
  let f : ZMod 11 →+* R := ZMod.castHom (dvd_refl 11) R
  exact ⟨_, _, exact_of_injective_hom f (ZMod.castHom_injective R) ERK10SixteenF11.exact_f11⟩

theorem exact_of_char13 (R : Type*) [CommRing R] [Nontrivial R] [CharP R 13] :
    ∃ (A : Matrix (Fin 16) (Fin 16) R) (b : Fin 16 → R),
      ERK A ∧ HasOrder 10 A b ∧ ¬ HasOrder 11 A b := by
  let f : ZMod 13 →+* R := ZMod.castHom (dvd_refl 13) R
  exact ⟨_, _, exact_of_injective_hom f (ZMod.castHom_injective R) ERK10SixteenF13.exact_f13⟩

theorem exact_of_char17 (R : Type*) [CommRing R] [Nontrivial R] [CharP R 17] :
    ∃ (A : Matrix (Fin 16) (Fin 16) R) (b : Fin 16 → R),
      ERK A ∧ HasOrder 10 A b ∧ ¬ HasOrder 11 A b := by
  let f : ZMod 17 →+* R := ZMod.castHom (dvd_refl 17) R
  exact ⟨_, _, exact_of_injective_hom f (ZMod.castHom_injective R) ERK10SixteenF17.exact_f17⟩

theorem exact_of_char19 (R : Type*) [CommRing R] [Nontrivial R] [CharP R 19] :
    ∃ (A : Matrix (Fin 16) (Fin 16) R) (b : Fin 16 → R),
      ERK A ∧ HasOrder 10 A b ∧ ¬ HasOrder 11 A b := by
  let f : ZMod 19 →+* R := ZMod.castHom (dvd_refl 19) R
  exact ⟨_, _, exact_of_injective_hom f (ZMod.castHom_injective R) ERK10SixteenF19.exact_f19⟩

theorem exact_of_char23 (R : Type*) [CommRing R] [Nontrivial R] [CharP R 23] :
    ∃ (A : Matrix (Fin 16) (Fin 16) R) (b : Fin 16 → R),
      ERK A ∧ HasOrder 10 A b ∧ ¬ HasOrder 11 A b := by
  let f : ZMod 23 →+* R := ZMod.castHom (dvd_refl 23) R
  exact ⟨_, _, exact_of_injective_hom f (ZMod.castHom_injective R) ERK10SixteenF23.exact_f23⟩

end RKResearch.Certified.ERK10PrimeFieldTransfer

#print axioms RKResearch.Certified.ERK10PrimeFieldTransfer.exact_of_char11
#print axioms RKResearch.Certified.ERK10PrimeFieldTransfer.exact_of_char13
#print axioms RKResearch.Certified.ERK10PrimeFieldTransfer.exact_of_char17
#print axioms RKResearch.Certified.ERK10PrimeFieldTransfer.exact_of_char19
#print axioms RKResearch.Certified.ERK10PrimeFieldTransfer.exact_of_char23
