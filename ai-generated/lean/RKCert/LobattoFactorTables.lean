module
public import RKCert.SplitFactorGate
public import Mathlib.Tactic.IntervalCases

@[expose] public section
namespace RKCert.FixedFactor
open Polynomial
noncomputable def intHorner : List ℤ → ℤ[X]
  | [] => 0
  | a::l => C a + X*intHorner l

def readCoeff : List ℤ → ℕ → ℤ
  | [], _ => 0
  | a::_, 0 => a
  | _::l, i+1 => readCoeff l i

theorem coeff_horner (l : List ℤ) (i : ℕ) : (intHorner l).coeff i=readCoeff l i := by
  induction l generalizing i with
  | nil => simp [intHorner,readCoeff]
  | cons a l ih =>
    cases i with
    | zero => simp only [intHorner,coeff_add,coeff_C_zero,coeff_X_mul_zero,add_zero,readCoeff]
    | succ j => simp only [intHorner,coeff_add,coeff_C_succ,coeff_X_mul,zero_add,ih,readCoeff]

theorem read_out (l : List ℤ) (i : ℕ) (hi : l.length ≤ i) : readCoeff l i=0 := by
  induction l generalizing i with
  | nil => rfl
  | cons a l ih =>
    cases i with
    | zero => simp at hi
    | succ i => exact ih _ (Nat.le_of_succ_le_succ hi)

theorem degree_horner_le (l : List ℤ) (D : ℕ) (h : l.length ≤ D+1) : (intHorner l).natDegree≤D := by
  apply natDegree_le_iff_coeff_eq_zero.mpr
  intro i hi; rw [coeff_horner,read_out _ _ (by omega)]

theorem z_grid_split {p : ℕ} [Fact p.Prime] (l : List ℤ) (a : List (ZMod p))
    (hc : l.length≤a.length+1)
    (exact' : ∀i≤a.length, ((readCoeff l i:ℤ):ZMod p)=coeffs a i) :
    (intHorner l).map (Int.castRingHom (ZMod p))=linearProduct id a := by
  ext i; rw [coeff_map,coeff_horner,coeff_product]
  by_cases hi : i≤a.length
  · exact exact' i hi
  · rw [read_out l i (by omega),map_zero,← coeff_product,
      coeff_eq_zero_of_natDegree_lt (by rw [degree_product]; omega)]

def digits7 : List ℤ := [14530697473149,-914519421387,17764557525,-151833825,637065,-1287,1]
def digits8 : List ℤ := [-8550986578849000000,209289881300500000,-1609922163850000,5629098475000,
  -10234724500,10020010,-5005,1]
noncomputable def grid7 := intHorner digits7
noncomputable def grid8 := intHorner digits8
def knots7 : List (ZMod 1237) := [1005,1065,1028,638,601,661]
def knots8 : List (ZMod 1249) := [561,1121,172,715,9,309,869]

set_option maxRecDepth 50000 in
instance prime7 : Fact (Nat.Prime 1237) := ⟨by decide +kernel⟩
set_option maxRecDepth 50000 in
instance prime8 : Fact (Nat.Prime 1249) := ⟨by decide +kernel⟩

theorem degree_grid7 : grid7.natDegree=6 := by
  apply le_antisymm (degree_horner_le digits7 6 (by decide))
  apply le_natDegree_of_ne_zero
  change (intHorner digits7).coeff 6 ≠ 0
  rw [coeff_horner]; decide

theorem degree_grid8 : grid8.natDegree=7 := by
  apply le_antisymm (degree_horner_le digits8 7 (by decide))
  apply le_natDegree_of_ne_zero
  change (intHorner digits8).coeff 7 ≠ 0
  rw [coeff_horner]; decide

theorem monic_grid7 : grid7.Monic := by
  rw [Monic,leadingCoeff,degree_grid7,grid7,coeff_horner]; decide
theorem monic_grid8 : grid8.Monic := by
  rw [Monic,leadingCoeff,degree_grid8,grid8,coeff_horner]; decide

set_option maxRecDepth 50000 in
theorem split_grid7 : grid7.map (Int.castRingHom (ZMod 1237))=linearProduct id knots7 := by
  apply z_grid_split _ _ (by decide); intro i hi
  change i≤6 at hi; interval_cases i <;> decide

set_option maxRecDepth 50000 in
theorem split_grid8 : grid8.map (Int.castRingHom (ZMod 1249))=linearProduct id knots8 := by
  apply z_grid_split _ _ (by decide); intro i hi
  change i≤7 at hi; interval_cases i <;> decide

set_option maxHeartbeats 0 in
set_option maxRecDepth 50000 in
theorem checked_grid7 : checked 420 4 (0::knots7) knots7=true := by decide +kernel

set_option maxHeartbeats 0 in
set_option maxRecDepth 50000 in
theorem checked_grid8 : checked 420 5 (0::knots8) knots8=true := by decide +kernel

theorem splitX {p : ℕ} [Fact p.Prime] (H : ℤ[X]) (a : List (ZMod p))
    (he:H.map (Int.castRingHom (ZMod p))=linearProduct id a) :
    (X*H).map (Int.castRingHom (ZMod p))=linearProduct id (0::a) := by
  simp [linearProduct,he]

universe u
variable {K : Type u} [Field K] [CharZero K]

/-- All 6 root sites and all 99 sublists of degree at most four are verified. -/
theorem gate_grid7 (P : K[X]) (w : K) (hm:P.Monic) (hd:P∣(X*grid7).map (Int.castRingHom K))
    (degP:P.natDegree≤4) (hw:(grid7.map (Int.castRingHom K)).eval w=0) : moment 420 4 P w≠0 :=
  good_prime 1237 (X*grid7) grid7 (monic_X.mul monic_grid7) monic_grid7 420 4
    (modular_table _ _ 420 4 (0::knots7) knots7 (splitX _ _ split_grid7) split_grid7 checked_grid7) P w hm hd degP hw

/-- All 7 root sites and all 219 sublists of degree at most five are verified. -/
theorem gate_grid8 (P : K[X]) (w : K) (hm:P.Monic) (hd:P∣(X*grid8).map (Int.castRingHom K))
    (degP:P.natDegree≤5) (hw:(grid8.map (Int.castRingHom K)).eval w=0) : moment 420 5 P w≠0 :=
  good_prime 1249 (X*grid8) grid8 (monic_X.mul monic_grid8) monic_grid8 420 5
    (modular_table _ _ 420 5 (0::knots8) knots8 (splitX _ _ split_grid8) split_grid8 checked_grid8) P w hm hd degP hw

end RKCert.FixedFactor
