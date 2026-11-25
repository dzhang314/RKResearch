module

public import RKCert.ReviewedNative.PositiveIntervalGrid19
public import RKCert.ReviewedNative.FiniteGaussianParity

import Mathlib.Tactic.IntervalCases
import Mathlib.Tactic.Linarith
import Mathlib.Tactic.NormNum
import Mathlib.Tactic.Ring

@[expose] public section

/-! # Small rational witnesses for the crossed negative-tail thresholds

A fixed two-dimensional polynomial space works for all three generators
of the left-biased cone. One degree-five line works for all three
generators of the whole nonnegative endpoint cone at the upper cut.
The constants here represent integrations of explicit polynomials, not
samples of a coefficient or physical clock space. -/
namespace RKCert.ReviewedNative.CrossedNegativeReference

open Polynomial RKCert.Endpoint
open RKCert.ReviewedNative.PositiveRule19
open RKCert.ReviewedNative.FiniteGaussianLocalizer
open scoped BigOperators

noncomputable section
variable {K : Type*} [Field K] [LinearOrder K] [IsStrictOrderedRing K]
set_option maxHeartbeats 1800000

def w (K : Type*) [Field K] : K[X] := X*(1-X)
def loCut (K : Type*) [Field K] : K[X] := 1-4*X
def hiCut (K : Type*) [Field K] : K[X] := 8*X-7
def lo₀ (K : Type*) [Field K] : K[X] := (4*X-3)*(2*X-1)^2
def lo₁ (K : Type*) [Field K] : K[X] := (4*X-3)*(2*X-1)^4
def hi (K : Type*) [Field K] : K[X] :=
  427141*X^5-224510*X^4-294415*X^3+234740*X^2-48315*X+2502

theorem deg_affine (a b : K) : (C a*X-C b).natDegree ≤ 1 :=
  (natDegree_sub_le _ _).trans (max_le
    ((natDegree_C_mul_le a _).trans (by simp)) (by simp))

theorem deg_w : (w K).natDegree ≤ 2 := by
  unfold w
  apply natDegree_mul_le_of_le (m:=1) (n:=1) (by simp)
  exact (natDegree_sub_le _ _).trans (by simp)

theorem deg_loCut : (loCut K).natDegree ≤ 1 := by
  unfold loCut
  exact (natDegree_sub_le _ _).trans (max_le (by simp)
    (natDegree_mul_le_of_le (m:=0) (n:=1) (by simp) (by simp)))

theorem deg_hiCut : (hiCut K).natDegree ≤ 1 := by
  simpa only [hiCut,Polynomial.C_ofNat] using (deg_affine (8:K) 7)

theorem deg_lo₀ : (lo₀ K).natDegree ≤ 5 := by
  have a : (4*X-3:K[X]).natDegree ≤ 1 := by
    simpa only [Polynomial.C_ofNat] using (deg_affine (4:K) 3)
  have b : (2*X-1:K[X]).natDegree ≤ 1 := by
    simpa only [Polynomial.C_ofNat,map_one] using (deg_affine (2:K) 1)
  exact (natDegree_mul_le_of_le a (natDegree_pow_le_of_le 2 b)).trans (by decide)

theorem deg_lo₁ : (lo₁ K).natDegree ≤ 5 := by
  have a : (4*X-3:K[X]).natDegree ≤ 1 := by
    simpa only [Polynomial.C_ofNat] using (deg_affine (4:K) 3)
  have b : (2*X-1:K[X]).natDegree ≤ 1 := by
    simpa only [Polynomial.C_ofNat,map_one] using (deg_affine (2:K) 1)
  exact natDegree_mul_le_of_le a (natDegree_pow_le_of_le 4 b)

theorem deg_hi : (hi K).natDegree ≤ 5 := by
  have sub {A B : K[X]} (da : A.natDegree ≤ 5) (db : B.natDegree ≤ 5) :
      (A-B).natDegree ≤ 5 := (natDegree_sub_le _ _).trans (max_le da db)
  have add {A B : K[X]} (da : A.natDegree ≤ 5) (db : B.natDegree ≤ 5) :
      (A+B).natDegree ≤ 5 := natDegree_add_le_of_degree_le da db
  have p (a : K) (j : ℕ) (hj : j ≤ 5) : ((C a)*X^j).natDegree ≤ 5 :=
    calc
      ((C a)*X^j).natDegree ≤ ((X : K[X])^j).natDegree := natDegree_C_mul_le _ _
      _ = j := Polynomial.natDegree_X_pow j
      _ ≤ 5 := hj
  unfold hi
  refine add (sub (add (sub (sub ?_ ?_) ?_) ?_) ?_) ?_
  · simpa only [Polynomial.C_ofNat] using (p 427141 5 (by decide))
  · simpa only [Polynomial.C_ofNat] using (p 224510 4 (by decide))
  · simpa only [Polynomial.C_ofNat] using (p 294415 3 (by decide))
  · simpa only [Polynomial.C_ofNat] using (p 234740 2 (by decide))
  · simpa only [Polynomial.C_ofNat,pow_one] using (p 48315 1 (by decide))
  · have h : (C (2502 : K)).natDegree ≤ 5 := by simp
    simpa only [Polynomial.C_ofNat] using h

private theorem primitive_pow (n : ℕ) :
    formalPrimitive ((X:K[X])^n) = monomial (n+1) (1/((n:K)+1)) := by
  rw [← monomial_one_right_eq_X_pow]
  simp [formalPrimitive,support_monomial n (one_ne_zero : (1:K) ≠ 0)]

theorem int_pow (u : K) (j : ℕ) :
    integral 0 u ((X:K[X])^j) = u^(j+1)/((j:K)+1) := by
  rw [integral_zero_left,primitive_pow,eval_monomial]
  simp only [div_eq_mul_inv,one_mul]
  exact mul_comm _ _

theorem int_C_mul_pow (u a : K) (j : ℕ) :
    integral 0 u (C a*X^j) = a*(u^(j+1)/((j:K)+1)) := by
  rw [moment_C_mul,int_pow]

/-- Apply a linear integral to the three explicit entries of a binary
localizer, without expanding the two variable coefficients. -/
theorem binary_entries (E : K[X] →ₗ[K] K) (W g P₀ P₁ : K[X]) (a b : K) :
    E (W*(g*(C a*P₀+C b*P₁)^2)) =
      binaryQ (E (W*g*(P₀*P₀))) (E (W*g*(P₀*P₁))) (E (W*g*(P₁*P₁))) a b := by
  have eq : W*(g*(C a*P₀+C b*P₁)^2) =
      C (a^2)*(W*g*(P₀*P₀))+C (2*a*b)*(W*g*(P₀*P₁))+C (b^2)*(W*g*(P₁*P₁)) := by
    simp only [map_mul,map_pow,Polynomial.C_ofNat]
    ring
  rw [eq]
  simp only [map_add,moment_C_mul,binaryQ]
  ring

private theorem lo_ww_0 :
    integral 0 1 ((w K*w K)*loCut K*(lo₀ K*lo₀ K)) = ((1:K)/770) := by
  rw [show (w K*w K)*loCut K*(lo₀ K*lo₀ K) =
      C (-1024:K)*X^11 + C (5888:K)*X^10 + C (-14784:K)*X^9
      + C (21264:K)*X^8 + C (-19296:K)*X^7 + C (11448:K)*X^6
      + C (-4436:K)*X^5 + C (1081:K)*X^4 + C (-150:K)*X^3
      + C (9:K)*X^2 by
    simp only [w,loCut,lo₀,lo₁,map_neg,Polynomial.C_ofNat,map_one]
    ring]
  simp only [map_add,int_C_mul_pow,one_pow]
  norm_num

private theorem lo_ww_1 :
    integral 0 1 ((w K*w K)*loCut K*(lo₀ K*lo₁ K)) = ((5:K)/6006) := by
  rw [show (w K*w K)*loCut K*(lo₀ K*lo₁ K) =
      C (-4096:K)*X^13 + C (27648:K)*X^12 + C (-83712:K)*X^11
      + C (150080:K)*X^10 + C (-177024:K)*X^9 + C (144240:K)*X^8
      + C (-82832:K)*X^7 + C (33516:K)*X^6 + C (-9360:K)*X^5
      + C (1717:K)*X^4 + C (-186:K)*X^3 + C (9:K)*X^2 by
    simp only [w,loCut,lo₀,lo₁,map_neg,Polynomial.C_ofNat,map_one]
    ring]
  simp only [map_add,int_C_mul_pow,one_pow]
  norm_num

private theorem lo_ww_2 :
    integral 0 1 ((w K*w K)*loCut K*(lo₁ K*lo₁ K)) = ((7:K)/12870) := by
  rw [show (w K*w K)*loCut K*(lo₁ K*lo₁ K) =
      C (-16384:K)*X^15 + C (126976:K)*X^14 + C (-449536:K)*X^13
      + C (962816:K)*X^12 + C (-1392128:K)*X^11 + C (1435136:K)*X^10
      + C (-1085312:K)*X^9 + C (609632:K)*X^8 + C (-254336:K)*X^7
      + C (77824:K)*X^6 + C (-16972:K)*X^5 + C (2497:K)*X^4
      + C (-222:K)*X^3 + C (9:K)*X^2 by
    simp only [w,loCut,lo₀,lo₁,map_neg,Polynomial.C_ofNat,map_one]
    ring]
  simp only [map_add,int_C_mul_pow,one_pow]
  norm_num

theorem lo_ww_pos {a b : K} (ab : a ≠ 0 ∨ b ≠ 0) :
    0 < integral 0 1 ((w K*w K)*(loCut K*(C a*lo₀ K+C b*lo₁ K)^2)) := by
  rw [binary_entries,lo_ww_0,lo_ww_1,lo_ww_2]
  exact binaryQ_pos_of_principal _ _ _ (by norm_num) (by norm_num) ab

private theorem lo_w_0 :
    integral 0 1 ((w K)*loCut K*(lo₀ K*lo₀ K)) = ((11:K)/630) := by
  rw [show (w K)*loCut K*(lo₀ K*lo₀ K) =
      C (1024:K)*X^9 + C (-4864:K)*X^8 + C (9920:K)*X^7
      + C (-11344:K)*X^6 + C (7952:K)*X^5 + C (-3496:K)*X^4
      + C (940:K)*X^3 + C (-141:K)*X^2 + C (9:K)*X^1 by
    simp only [w,loCut,lo₀,lo₁,map_neg,Polynomial.C_ofNat,map_one]
    ring]
  simp only [map_add,int_C_mul_pow,one_pow]
  norm_num

private theorem lo_w_1 :
    integral 0 1 ((w K)*loCut K*(lo₀ K*lo₁ K)) = ((17:K)/1386) := by
  rw [show (w K)*loCut K*(lo₀ K*lo₁ K) =
      C (4096:K)*X^11 + C (-23552:K)*X^10 + C (60160:K)*X^9
      + C (-89920:K)*X^8 + C (87104:K)*X^7 + C (-57136:K)*X^6
      + C (25696:K)*X^5 + C (-7820:K)*X^4 + C (1540:K)*X^3
      + C (-177:K)*X^2 + C (9:K)*X^1 by
    simp only [w,loCut,lo₀,lo₁,map_neg,Polynomial.C_ofNat,map_one]
    ring]
  simp only [map_add,int_C_mul_pow,one_pow]
  norm_num

private theorem lo_w_2 :
    integral 0 1 ((w K)*loCut K*(lo₁ K*lo₁ K)) = ((23:K)/2574) := by
  rw [show (w K)*loCut K*(lo₁ K*lo₁ K) =
      C (16384:K)*X^13 + C (-110592:K)*X^12 + C (338944:K)*X^11
      + C (-623872:K)*X^10 + C (768256:K)*X^9 + C (-666880:K)*X^8
      + C (418432:K)*X^7 + C (-191200:K)*X^6 + C (63136:K)*X^5
      + C (-14688:K)*X^4 + C (2284:K)*X^3 + C (-213:K)*X^2
      + C (9:K)*X^1 by
    simp only [w,loCut,lo₀,lo₁,map_neg,Polynomial.C_ofNat,map_one]
    ring]
  simp only [map_add,int_C_mul_pow,one_pow]
  norm_num

theorem lo_w_pos {a b : K} (ab : a ≠ 0 ∨ b ≠ 0) :
    0 < integral 0 1 ((w K)*(loCut K*(C a*lo₀ K+C b*lo₁ K)^2)) := by
  rw [binary_entries,lo_w_0,lo_w_1,lo_w_2]
  exact binaryQ_pos_of_principal _ _ _ (by norm_num) (by norm_num) ab

private theorem lo_left_0 :
    integral 0 1 ((w K*(1-X))*loCut K*(lo₀ K*lo₀ K)) = ((97:K)/4620) := by
  rw [show (w K*(1-X))*loCut K*(lo₀ K*lo₀ K) =
      C (-1024:K)*X^10 + C (5888:K)*X^9 + C (-14784:K)*X^8
      + C (21264:K)*X^7 + C (-19296:K)*X^6 + C (11448:K)*X^5
      + C (-4436:K)*X^4 + C (1081:K)*X^3 + C (-150:K)*X^2
      + C (9:K)*X^1 by
    simp only [w,loCut,lo₀,lo₁,map_neg,Polynomial.C_ofNat,map_one]
    ring]
  simp only [map_add,int_C_mul_pow,one_pow]
  norm_num

private theorem lo_left_1 :
    integral 0 1 ((w K*(1-X))*loCut K*(lo₀ K*lo₁ K)) = ((181:K)/12012) := by
  rw [show (w K*(1-X))*loCut K*(lo₀ K*lo₁ K) =
      C (-4096:K)*X^12 + C (27648:K)*X^11 + C (-83712:K)*X^10
      + C (150080:K)*X^9 + C (-177024:K)*X^8 + C (144240:K)*X^7
      + C (-82832:K)*X^6 + C (33516:K)*X^5 + C (-9360:K)*X^4
      + C (1717:K)*X^3 + C (-186:K)*X^2 + C (9:K)*X^1 by
    simp only [w,loCut,lo₀,lo₁,map_neg,Polynomial.C_ofNat,map_one]
    ring]
  simp only [map_add,int_C_mul_pow,one_pow]
  norm_num

private theorem lo_left_2 :
    integral 0 1 ((w K*(1-X))*loCut K*(lo₁ K*lo₁ K)) = ((289:K)/25740) := by
  rw [show (w K*(1-X))*loCut K*(lo₁ K*lo₁ K) =
      C (-16384:K)*X^14 + C (126976:K)*X^13 + C (-449536:K)*X^12
      + C (962816:K)*X^11 + C (-1392128:K)*X^10 + C (1435136:K)*X^9
      + C (-1085312:K)*X^8 + C (609632:K)*X^7 + C (-254336:K)*X^6
      + C (77824:K)*X^5 + C (-16972:K)*X^4 + C (2497:K)*X^3
      + C (-222:K)*X^2 + C (9:K)*X^1 by
    simp only [w,loCut,lo₀,lo₁,map_neg,Polynomial.C_ofNat,map_one]
    ring]
  simp only [map_add,int_C_mul_pow,one_pow]
  norm_num

theorem lo_left_pos {a b : K} (ab : a ≠ 0 ∨ b ≠ 0) :
    0 < integral 0 1 ((w K*(1-X))*(loCut K*(C a*lo₀ K+C b*lo₁ K)^2)) := by
  rw [binary_entries,lo_left_0,lo_left_1,lo_left_2]
  exact binaryQ_pos_of_principal _ _ _ (by norm_num) (by norm_num) ab

theorem hi_ww_pos :
    0 < integral 0 1 ((w K*w K)*(hiCut K*(hi K)^2)) := by
  rw [show (w K*w K)*(hiCut K*(hi K)^2) =
      C (1459595471048:K)*X^15 + C (-5730695793823:K)*X^14 + C (6816299577802:K)*X^13
      + C (1790726246023:K)*X^12 + C (-11214651244500:K)*X^11 + C (9192692249697:K)*X^10
      + C (-358666269962:K)*X^9 + C (-4185711757667:K)*X^8 + C (3197827216832:K)*X^7
      + C (-1191077766325:K)*X^6 + C (251901522102:K)*X^5 + C (-30025729107:K)*X^4
      + C (1830097908:K)*X^3 + C (-43820028:K)*X^2 by
    simp only [w,hiCut,hi,map_neg,Polynomial.C_ofNat,map_one]
    ring]
  simp only [map_add,int_C_mul_pow,one_pow]
  norm_num

theorem hi_left_pos :
    0 < integral 0 1 ((w K*(1-X))*(hiCut K*(hi K)^2)) := by
  rw [show (w K*(1-X))*(hiCut K*(hi K)^2) =
      C (1459595471048:K)*X^14 + C (-5730695793823:K)*X^13 + C (6816299577802:K)*X^12
      + C (1790726246023:K)*X^11 + C (-11214651244500:K)*X^10 + C (9192692249697:K)*X^9
      + C (-358666269962:K)*X^8 + C (-4185711757667:K)*X^7 + C (3197827216832:K)*X^6
      + C (-1191077766325:K)*X^5 + C (251901522102:K)*X^4 + C (-30025729107:K)*X^3
      + C (1830097908:K)*X^2 + C (-43820028:K)*X^1 by
    simp only [w,hiCut,hi,map_neg,Polynomial.C_ofNat,map_one]
    ring]
  simp only [map_add,int_C_mul_pow,one_pow]
  norm_num

theorem hi_right_pos :
    0 < integral 0 1 ((w K*X)*(hiCut K*(hi K)^2)) := by
  rw [show (w K*X)*(hiCut K*(hi K)^2) =
      C (-1459595471048:K)*X^14 + C (4271100322775:K)*X^13 + C (-2545199255027:K)*X^12
      + C (-4335925501050:K)*X^11 + C (6878725743450:K)*X^10 + C (-2313966506247:K)*X^9
      + C (-1955300236285:K)*X^8 + C (2230411521382:K)*X^7 + C (-967415695450:K)*X^6
      + C (223662070875:K)*X^5 + C (-28239451227:K)*X^4 + C (1786277880:K)*X^3
      + C (-43820028:K)*X^2 by
    simp only [w,hiCut,hi,map_neg,Polynomial.C_ofNat,map_one]
    ring]
  simp only [map_add,int_C_mul_pow,one_pow]
  norm_num

/-- The two left affine tests at 7/8 have a positive definite reference
form. This is the X-basis version of the scaled 1,Y matrix. -/
theorem cutoff_affine_pos (s : K) :
    0 < integral 0 (7/8) (w K*((X-C ((1:K)/4))*(X-C s)^2)) := by
  have moments (j : ℕ) (hj : j ≤ 2) :
    integral 0 ((7:K)/8) (w K*(X-C ((1:K)/4))*X^j) =
      if j=0 then 1813/49152 else if j=1 then 24353/983040 else 26411/1572864 := by
    have hp : w K*(X-C ((1:K)/4))*X^j =
        -C ((1:K)/4)*X^(j+1)+C ((5:K)/4)*X^(j+2)-X^(j+3) := by
      unfold w
      simp only [pow_add,pow_one]
      have e : C ((5:K)/4) = 1+C ((1:K)/4) := by
        rw [← map_one C, ← map_add]
        congr 1
        ring
      rw [e]
      ring
    rw [hp]
    simp only [neg_mul,map_sub,map_add,map_neg,int_C_mul_pow,int_pow]
    interval_cases j <;> norm_num
  have m₀ := moments 0 (by decide)
  have m₁ := moments 1 (by decide)
  have m₂ := moments 2 (by decide)
  norm_num only [pow_zero,pow_one,mul_one] at m₀ m₁ m₂
  have lin : (X-C s:K[X])=C (-s)*1+C (1:K)*X := by
    simp only [map_neg,map_one,mul_one,one_mul]
    ring
  rw [lin,binary_entries]
  simp only [one_mul,one_pow,mul_one,← pow_two]
  rw [m₀,m₁,m₂]
  exact binaryQ_pos_of_principal _ _ _ (by norm_num) (by norm_num) (Or.inr one_ne_zero)

end
end RKCert.ReviewedNative.CrossedNegativeReference
