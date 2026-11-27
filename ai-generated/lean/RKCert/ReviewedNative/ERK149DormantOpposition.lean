module

public import RKCert.ReviewedNative.ERK149TwoPairRawTranspose

import Mathlib.Tactic.FieldSimp
import Mathlib.Tactic.Ring

@[expose] public section

namespace RKResearch.Certified.ERK149DormantOpposition

variable {K : Type*} [Field K]

/-- The sum across the two opposite nonzero physical weights is one
effective donor in every paid defect read. This does not delete a stage. -/
theorem effective_read (p q w w' f f' : K) (hw : w ≠ 0)
    (h₁ : w+w'=0) (h₂ : f+f'=0) :
    p*f+q*f'=(p*w+q*w')*(f/w) := by
  have hw' : w' = -w := eq_neg_of_add_eq_zero_left (by simpa [add_comm] using h₁)
  have hf' : f' = -f := eq_neg_of_add_eq_zero_left (by simpa [add_comm] using h₂)
  rw [hw',hf']
  field_simp [hw] <;> ring

end RKResearch.Certified.ERK149DormantOpposition
