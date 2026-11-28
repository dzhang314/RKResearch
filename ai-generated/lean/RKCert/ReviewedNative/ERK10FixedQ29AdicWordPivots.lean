module

public import RKCert.ReviewedNative.ERK10FixedQ29AdicWordInput
public import Mathlib.LinearAlgebra.Matrix.NonsingularInverse

@[expose] public section

namespace RKResearch.Certified.ERK10FixedQ29Adic.Physical
open Matrix
open scoped BigOperators
noncomputable section
set_option maxHeartbeats 400000

variable {R : Type*} [CommRing R]

def leadWords (A : Site→Word→R) (m : ℕ) (hm : m≤8) : Matrix (Fin m) (Fin m) R :=
  fun i j => A (Fin.castLE (hm.trans (by decide : 8≤11)) i) (Fin.castLE hm j)

def inverseRows : List (List (List F)) := [
  [],
  [[15]],
  [[15, 0], [25, 15]],
  [[15, 0, 0], [17, 14, 3], [6, 8, 5]],
  [[15, 0, 0, 0], [24, 13, 19, 3], [12, 3, 27, 15], [26, 17, 18, 7]],
  [[15, 0, 0, 0, 0], [24, 13, 19, 19, 5], [12, 3, 27, 0, 8], [26, 17, 18, 9, 26], [0, 0, 0, 9, 1]],
  [[15, 0, 0, 0, 0, 0], [15, 26, 21, 25, 12, 5], [11, 27, 24, 20, 12, 7], [7, 9, 19, 12, 15, 17], [19, 8, 28, 6, 12, 12], [5, 25, 15, 16, 9, 23]],
  [[15, 0, 0, 0, 0, 0, 0], [15, 26, 21, 25, 12, 5, 0], [11, 27, 24, 20, 12, 7, 0], [7, 9, 19, 12, 15, 17, 0], [19, 8, 28, 6, 12, 12, 0], [5, 25, 15, 16, 9, 23, 0], [23, 6, 10, 10, 28, 12, 17]],
  [[15, 0, 0, 0, 0, 0, 0, 0], [15, 26, 21, 25, 12, 5, 0, 0], [11, 27, 24, 20, 12, 7, 0, 0], [7, 9, 19, 12, 15, 17, 0, 0], [19, 8, 28, 6, 12, 12, 0, 0], [5, 25, 15, 16, 9, 23, 0, 0], [23, 6, 10, 10, 28, 12, 17, 0], [25, 24, 28, 26, 22, 25, 27, 12]]
]

def inverseMod (m : ℕ) : Matrix (Fin m) (Fin m) F :=
  fun i j => ((inverseRows[m]?.getD [])[i.val]?.getD [])[j.val]?.getD 0

theorem lead_inverse_kernel :
    ∀ m : Fin 9, ∀ i j : Fin m.val,
      (leadWords wordMod m.val (by omega) * inverseMod m.val) i j =
        (if i=j then 1 else 0) := by
  simp only [Matrix.mul_apply]
  decide +kernel

theorem field_lead_paid (m : ℕ) (hm : m≤8) :
    IsUnit (leadWords wordMod m hm).det := by
  have hI : leadWords wordMod m hm*inverseMod m=1 := by
    ext i j
    rw [Matrix.one_apply]
    exact lead_inverse_kernel ⟨m,by omega⟩ i j
  have hh : (leadWords wordMod m hm).det*(inverseMod m).det=1 := by
    rw [←Matrix.det_mul,hI,Matrix.det_one]
  exact IsUnit.of_mul_eq_one _ hh

variable (ρ : R→+*F) [IsLocalHom ρ]
variable (c a b : R) (hp : (decic R).eval c=0) (hc : ρ c=2) (ha : ρ a=11) (hb : ρ b=20)
include ρ hp hc ha hb

/-- All leading principal word cuts, including the eight-word raw cut,
have an actual unit determinant over the local coefficient ring. -/
theorem actual_lead_paid (m : ℕ) (hm : m≤8) :
    IsUnit (leadWords (wordInput c a b) m hm).det := by
  apply IsUnit.of_map ρ
  have hMap : (leadWords (wordInput c a b) m hm).map ρ = leadWords wordMod m hm := by
    ext i j
    exact actual_word_input_mod ρ c a b hp hc ha hb _ _
  rw [RingHom.map_det]
  change IsUnit ((leadWords (wordInput c a b) m hm).map ρ).det
  rw [hMap]
  exact field_lead_paid m hm

end
end RKResearch.Certified.ERK10FixedQ29Adic.Physical

#print axioms RKResearch.Certified.ERK10FixedQ29Adic.Physical.lead_inverse_kernel
#print axioms RKResearch.Certified.ERK10FixedQ29Adic.Physical.actual_lead_paid
