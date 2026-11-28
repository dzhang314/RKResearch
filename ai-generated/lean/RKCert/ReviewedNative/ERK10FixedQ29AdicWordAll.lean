module

public import RKCert.ReviewedNative.ERK10FixedQ29AdicZTailPhysicalRows

@[expose] public section

namespace RKResearch.Certified.ERK10FixedQ29Adic.Physical
open Nonlinear Polynomial
open scoped BigOperators
noncomputable section

variable {R : Type*} [CommRing R]
variable (ρ : R→+*F) [IsLocalHom ρ] (c a b : R)
variable (hp : (decic R).eval c=0) (hc : ρ c=2) (ha : ρ a=11) (hb : ρ b=20)
variable (hRoot : (headQuadratic c).eval a=0) (hOther : b=headSum c-a)
include ρ hp hc ha hb hRoot hOther

/-- All eight word receipts at each of the eleven actual reverse rows. -/
theorem actualK_all_words (i : Site) (k : Word) :
    ∑ j : Site,actualK c a b i j*wordInput c a b j k=wordTarget c a b i k := by
  fin_cases i
  · exact actualK_first c a b k
  · exact actualK_second ρ c a b hp hc ha hb k
  · exact actualK_third ρ c a b hp hc ha hb hRoot hOther k
  · exact actualK_center ρ c a b hp hc ha hb hRoot hOther 3 (Or.inl rfl) k
  · exact actualK_center ρ c a b hp hc ha hb hRoot hOther 4 (Or.inr rfl) k
  · exact actualK_d ρ c a b hp hc ha hb hRoot hOther k
  · exact actualK_e ρ c a b hp hc ha hb hRoot hOther k
  · exact actualK_f ρ c a b hp hc ha hb hRoot hOther k
  · exact actualK_late ρ c a b hp hc ha hb 8 (by decide +kernel) k
  · exact actualK_late ρ c a b hp hc ha hb 9 (by decide +kernel) k
  · exact actualK_late ρ c a b hp hc ha hb 10 (by decide +kernel) k

theorem actualK_complete :
    strictlyLower (actualK c a b) ∧
    (∀ i : Site, ∀ k : Word,
      ∑ j : Site,actualK c a b i j*wordInput c a b j k=wordTarget c a b i k) ∧
    actualK c a b 9 8=(actualHost c a b).zb ∧
    actualK c a b 10 8=(actualHost c a b).za ∧
    actualK c a b 10 9=(actualHost c a b).va :=
  ⟨actualK_strict c a b,actualK_all_words ρ c a b hp hc ha hb hRoot hOther,actualK_ports c a b⟩

end
end RKResearch.Certified.ERK10FixedQ29Adic.Physical

#print axioms RKResearch.Certified.ERK10FixedQ29Adic.Physical.actualK_all_words
#print axioms RKResearch.Certified.ERK10FixedQ29Adic.Physical.actualK_complete
