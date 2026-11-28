module

import RKCert.ReviewedNative.DIRK12MidpointRealExactOrder

open RKResearch RKResearch.Certified.Graded RKResearch.Certified.DIRK12MidpointReverse
open RKResearch.Certified.DIRK12MidpointForward RKResearch.Certified.DIRK12MidpointRealInterval
open RKResearch.Certified.DirectedRatBox

open scoped Matrix

section
variable (x f : ℝ) (hx : Encloses xBox x) (hf : Encloses fBox f)
  (hx0 : realX x=0) (hf0 : realF x f=0)

local notation "Areal" => (Feed.tableau (Actual.assembled x f))
local notation "Breal" => (Feed.b (Actual.assembled x f))
local notation "G" => (Actual.profileG x f)
local notation "H" => (Actual.profileH x f)
local notation "Y" => ((1:V15 ℝ)-nodes Areal)

example :
    ∃ a b c : ℝ, DualSupport12.reverse Areal Breal 4=a • G+b • H+c • (Y*H) :=
  Actual.reverse_five_three x f hx hf hx0 hf0

example : ∃ a b c : ℝ, mat (Matrix.transpose Areal) H=a • G+b • H+c • (Y*H) :=
  Actual.transpose_H_three x f hx hf hx0 hf0

example : HasOrder 12 Areal Breal :=
  Actual.assembled_hasOrder12 x f hx hf hx0 hf0

example : ¬ HasOrder 13 Areal Breal :=
  Actual.assembled_notOrder13 x f hx hf hx0 hf0

end

example :
    ∃ (A : Matrix (Fin 15) (Fin 15) ℝ) (b : Fin 15 → ℝ),
      Matrix.IsLowerTriangular A ∧ A 0 0=0 ∧ A 1 1=1/16 ∧ A 14 14=0 ∧
        HasOrder 12 A b ∧ ¬ HasOrder 13 A b :=
  Actual.exists_exact_real_dirk12

#print axioms Actual.annihilator_three
#print axioms Actual.reverse_five_three
#print axioms Actual.transpose_H_three
#print axioms Actual.assembled_hasOrder12
#print axioms Actual.assembled_notOrder13
#print axioms Actual.exists_exact_real_dirk12
