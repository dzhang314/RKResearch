module

public import RKCert.ReviewedNative.ERKOrder16WeakFourFirstMomentReceipts
public import RKCert.ReviewedNative.PolynomialBracket
import Mathlib.Tactic.IntervalCases
import Mathlib.Tactic.NormNum
import Lean.Elab.Tactic.Omega

@[expose] public section

/-! # Computable coefficient lists for the weak-four references

The reflected checker need not reduce polynomial multiplication or classical
support manipulation. It evaluates these ascending rational lists by Horner.
Each list is checked against the exact polynomial used at the native interface.
-/
namespace RKCert.ReviewedNative.WeakFourFirstOnly

open Polynomial
open RKCert.ReviewedNative.PolynomialBracket (ofCoeffs coeff_ofCoeffs)

def referenceJList : List ℚ :=
  [-8,252,-2520,11550,-27720,36036,-24024,6435]

def referenceKList : List ℚ :=
  [-36,840,-6930,27720,-60060,72072,-45045,11440]

def referenceP₀List : List ℚ := 0::referenceKList

def referenceP₁List : List ℚ :=
  [8,-288,3360,-18480,55440,-96096,96096,-51480,11440]

def referenceN₁List : List ℚ :=
  [-8,288,-3360,18480,-55440,96096,-96096,51480,-11440]

def listCoeff (A : List ℚ) (k : ℕ) : ℚ := A[k]?.getD 0

private theorem listCoeff_eq_zero_of_len_le (A : List ℚ) {i : ℕ} (h : A.length ≤ i) :
    listCoeff A i=0 := by
  simp only [listCoeff,List.getElem?_eq_none_iff.mpr h,Option.getD_none]

theorem referenceJList_polynomial : ofCoeffs referenceJList=firstReferenceJ ℚ := by
  ext i
  rw [coeff_ofCoeffs]
  change listCoeff referenceJList i = _
  by_cases h : i < 8
  · interval_cases i <;> norm_num [listCoeff,referenceJList,firstReferenceJ,
      ofFn_coeff_eq_val_of_lt]
  · have bound : referenceJList.length ≤ i := by
      change 8 ≤ i
      exact le_of_not_gt h
    rw [listCoeff_eq_zero_of_len_le _ bound]
    symm
    apply coeff_eq_zero_of_natDegree_lt
    rw [firstReferenceJ_degree]
    omega

theorem referenceKList_polynomial : ofCoeffs referenceKList=firstReferenceK ℚ := by
  ext i
  rw [coeff_ofCoeffs]
  change listCoeff referenceKList i = _
  by_cases h : i < 8
  · interval_cases i <;> norm_num [listCoeff,referenceKList,firstReferenceK,
      ofFn_coeff_eq_val_of_lt]
  · have bound : referenceKList.length ≤ i := by
      change 8 ≤ i
      exact le_of_not_gt h
    rw [listCoeff_eq_zero_of_len_le _ bound]
    symm
    apply coeff_eq_zero_of_natDegree_lt
    rw [firstReferenceK_degree]
    omega

theorem referenceP₀List_polynomial : ofCoeffs referenceP₀List=firstReferenceP₀ ℚ := by
  simp only [referenceP₀List,ofCoeffs,map_zero,zero_add,referenceKList_polynomial,
    firstReferenceP₀]

private theorem referenceP₁List_coeff (i : ℕ) :
    listCoeff referenceP₁List i = listCoeff referenceP₀List i-listCoeff referenceJList i := by
  by_cases h : i < 9
  · interval_cases i <;> norm_num [listCoeff,referenceP₁List,referenceP₀List,referenceKList,
      referenceJList]
  · have a : referenceP₁List.length ≤ i := by
      change 9 ≤ i
      exact le_of_not_gt h
    have b : referenceP₀List.length ≤ i := by
      change 9 ≤ i
      exact le_of_not_gt h
    have c : referenceJList.length ≤ i := by
      change 8 ≤ i
      omega
    rw [listCoeff_eq_zero_of_len_le _ a,listCoeff_eq_zero_of_len_le _ b,
      listCoeff_eq_zero_of_len_le _ c,sub_zero]

theorem referenceP₁List_polynomial : ofCoeffs referenceP₁List=firstReferenceP₁ ℚ := by
  rw [firstReferenceP₁_identity,←referenceP₀List_polynomial,←referenceJList_polynomial]
  ext i
  simpa only [coeff_sub,coeff_ofCoeffs,listCoeff] using referenceP₁List_coeff i

theorem referenceN₁List_polynomial : ofCoeffs referenceN₁List= -firstReferenceP₁ ℚ := by
  rw [←referenceP₁List_polynomial]
  ext i
  simp only [coeff_neg,coeff_ofCoeffs]
  change listCoeff referenceN₁List i = -listCoeff referenceP₁List i
  by_cases h : i < 9
  · interval_cases i <;> norm_num [listCoeff,referenceN₁List,referenceP₁List]
  · have a : referenceN₁List.length ≤ i := by
      change 9 ≤ i
      exact le_of_not_gt h
    have b : referenceP₁List.length ≤ i := by
      change 9 ≤ i
      exact le_of_not_gt h
    rw [listCoeff_eq_zero_of_len_le _ a,listCoeff_eq_zero_of_len_le _ b,neg_zero]

end RKCert.ReviewedNative.WeakFourFirstOnly
