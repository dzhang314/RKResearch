module

public import Mathlib.Algebra.BigOperators.Fin
public import Mathlib.Algebra.Order.Field.Basic
public import Mathlib.Data.Fin.VecNotation
public import Mathlib.Order.Fin.Basic

import Mathlib.Tactic.FinCases
import Mathlib.Tactic.NormNum

@[expose] public section

/-! # Small strictly interior positive rational unit quadrature

The table and the twenty exact integer residuals are independent of the
RK theory. Normalized nodes are divided by 128, and weights by the
positive common mass denominator. Only closed natural arithmetic is
used for the certificate; the generic consumer casts those identities.

The exact coefficients can also be checked directly in the rational certificate.
-/
namespace RKCert.ReviewedNative.PositiveRule19
open scoped BigOperators

def pointNumerator : Fin 19 → ℕ :=
  ![1, 3, 6, 11, 18, 26, 34, 44, 54, 64, 74, 84, 94, 102, 110, 117, 122, 125, 127]

def massDenominator : ℕ := 425643294094315542650108828261897814911098830084716100131250000

def massNumerator : Fin 19 → ℕ :=
  ![7814342460740946038962452076987648755614684681221457313792000,
   4685351381346908599620158826884682287277020980078379008000000,
   15592018568332813787561889361221967959072108781593162953079375,
   18371798829007469411027940120405361266792834205990421790720000,
   27465356830788935181174499358384782493848445386944149883562500,
   24427545848317978187064782321083671660786656928557411284752375,
   30996358051620617353037286683523494150404841727706394580592548,
   33628036229450614193353899723312119705056163937683900966131712,
   33272296800004995904814596438679866786986113716667117803133970,
   33137084095092985336873818440930624779421089391831308963721040,
   33272296800004995904814596438679866786986113716667117803133970,
   33628036229450614193353899723312119705056163937683900966131712,
   30996358051620617353037286683523494150404841727706394580592548,
   24427545848317978187064782321083671660786656928557411284752375,
   27465356830788935181174499358384782493848445386944149883562500,
   18371798829007469411027940120405361266792834205990421790720000,
   15592018568332813787561889361221967959072108781593162953079375,
   4685351381346908599620158826884682287277020980078379008000000,
   7814342460740946038962452076987648755614684681221457313792000]

theorem pointNumerator_pos (i : Fin 19) : 0 < pointNumerator i := by
  fin_cases i <;> norm_num [pointNumerator]

theorem pointNumerator_lt (i : Fin 19) : pointNumerator i < 128 := by
  fin_cases i <;> norm_num [pointNumerator]

theorem pointNumerator_strictMono : StrictMono pointNumerator := by
  apply Fin.strictMono_iff_lt_succ.mpr
  intro i
  fin_cases i <;> norm_num [pointNumerator]

theorem massNumerator_pos (i : Fin 19) : 0 < massNumerator i := by
  fin_cases i <;> norm_num [massNumerator]

theorem massDenominator_pos : 0 < massDenominator := by
  norm_num [massDenominator]

set_option maxRecDepth 2600 in
set_option maxHeartbeats 700000 in
/-- The small exact certificate: the ordinary uncentered k-th moment, with
all denominators cleared. This uses no approximate numerical data. -/
theorem integer_moment (k : Fin 20) :
    (k.val+1) * (∑ i : Fin 19, massNumerator i * pointNumerator i ^ k.val) =
      massDenominator * 128 ^ k.val := by
  fin_cases k <;>
    norm_num [Fin.sum_univ_succ, pointNumerator, massNumerator, massDenominator]

section Field
variable (K : Type*) [Field K]

/-- The same strictly interior node table, with coefficients in K. -/
def point (i : Fin 19) : K := (pointNumerator i : K) / 128

/-- The same exact positive weights, with coefficients in K. -/
def weight (i : Fin 19) : K := (massNumerator i : K) / (massDenominator : K)

variable [CharZero K]

theorem exact_monomial (k : Fin 20) :
    (∑ i : Fin 19, weight K i * point K i ^ k.val) =
      (1 : K) / ((k.val+1:ℕ):K) := by
  have d : (massDenominator : K) ≠ 0 := Nat.cast_ne_zero.mpr massDenominator_pos.ne'
  have u : (128 : K) ≠ 0 := by exact_mod_cast (show (128:ℕ) ≠ 0 by decide)
  have q : ((k.val+1:ℕ):K) ≠ 0 := Nat.cast_ne_zero.mpr (Nat.succ_ne_zero _)
  have E := congrArg (fun n : ℕ => (n : K)) (integer_moment k)
  simp only [Nat.cast_mul, Nat.cast_sum, Nat.cast_pow, Nat.cast_ofNat] at E
  calc
    _ = (∑ i : Fin 19, (massNumerator i:K) * (pointNumerator i:K) ^ k.val) /
        ((massDenominator:K) * (128:K)^k.val) := by
      conv_rhs => rw [div_eq_mul_inv, Finset.sum_mul]
      apply Finset.sum_congr rfl
      intro i _
      rw [weight, point, div_pow, div_mul_div_comm, div_eq_mul_inv]
    _ = _ := by
      apply (div_eq_div_iff (mul_ne_zero d (pow_ne_zero _ u)) q).mpr
      simpa only [one_mul, mul_comm (((k.val+1:ℕ):K))] using E

end Field

section Ordered
variable (K : Type*) [Field K] [LinearOrder K] [IsStrictOrderedRing K]

theorem point_pos (i : Fin 19) : 0 < point K i :=
  div_pos (Nat.cast_pos.mpr (pointNumerator_pos i)) (by norm_num)

theorem point_lt_one (i : Fin 19) : point K i < 1 := by
  change (pointNumerator i : K) / 128 < 1
  apply (div_lt_iff₀ (by norm_num : (0:K)<128)).mpr
  rw [one_mul]
  exact_mod_cast pointNumerator_lt i

theorem point_strictMono : StrictMono (point K) := by
  intro i j h
  change (pointNumerator i : K) / 128 < (pointNumerator j : K) / 128
  apply (div_lt_div_iff_of_pos_right (by norm_num : (0:K)<128)).mpr
  exact_mod_cast pointNumerator_strictMono h

theorem weight_pos (i : Fin 19) : 0 < weight K i :=
  div_pos (Nat.cast_pos.mpr (massNumerator_pos i)) (Nat.cast_pos.mpr massDenominator_pos)

end Ordered
end RKCert.ReviewedNative.PositiveRule19
