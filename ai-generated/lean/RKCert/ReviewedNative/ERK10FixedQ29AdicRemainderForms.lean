module

public import RKCert.ReviewedNative.ERK10FixedQ29AdicPhaseExact
public import RKCert.ReviewedNative.ERK10FixedQ29AdicRemainderData
public import Mathlib.Algebra.Polynomial.Div
public import Mathlib.Algebra.Polynomial.OfFn

@[expose] public section

namespace RKResearch.Certified.ERK10FixedQ29Adic.Nonlinear
open Packed Polynomial
open scoped Ring BigOperators Polynomial

noncomputable section
set_option maxRecDepth 40000
set_option maxHeartbeats 0

def vCoordsF : List Form :=
  [75*cForm^3-108*cForm^2+45*cForm-5,
    -3*(175*cForm^3-244*cForm^2+97*cForm-10),
    3*(350*cForm^3-476*cForm^2+183*cForm-18),
    -15*(42*cForm^3-56*cForm^2+21*cForm-2)]

def tailFour {S : Type*} [Sub S] [Mul S] [OfNat S 0] [OfNat S 1]
    (R f g h : S) : List S :=
  polyLin h 0 (polyLin g 0 (polyLin f 0 (polyLin R 0 [1])))

def t4CoordsF : List Form := tailFour 15 (fr repF) 6 (fr repH)
def qnCoordsF : List Form :=
  [(6-fr repF)*fr repPhaseF-(fr repPhaseG-fr repPhaseF)*fr repF,
    fr repPhaseG-fr repPhaseF]
def quotCoordsF : List Form := [fr repQuot0,fr repQuot1,fr repQuot2,fr repQuot3]

def uCoeffF (i : ℕ) : Form :=
  (6-fr repF)*((0::vCoordsF)[i]?.getD 0-vCoordsF[i]?.getD 0) +
    fr repGamma*t4CoordsF[i]?.getD 0
def secondCoeffF (i : ℕ) : Form :=
  fr repCNu*((0::qnCoordsF)[i]?.getD 0-(0::0::qnCoordsF)[i]?.getD 0)
def exprRemainder (i : ℕ) : Form :=
  Form.sumFin (i+1) (fun j => fr (repMu j.val)*uCoeffF (i-j.val)) -
    secondCoeffF i -
  Form.sumFin (i+1) (fun j => fr (repD j.val)*quotCoordsF[i-j.val]?.getD 0)

section Actual
variable {R : Type*} [CommRing R]

def vCoords (c : R) : List R :=
  [75*c^3-108*c^2+45*c-5,
    -3*(175*c^3-244*c^2+97*c-10),
    3*(350*c^3-476*c^2+183*c-18),
    -15*(42*c^3-56*c^2+21*c-2)]

def actualV (c : R) : Polynomial R := fromCoeffs (vCoords c)
def actualT4 (c : R) : Polynomial R := fromCoeffs (tailFour 15 (fTail c) 6 (hTail c))
def gap (c : R) : R := 6-fTail c
def phaseDiff (c : R) : R := phaseValue c 6-phaseValue c (fTail c)
def qnCoords (c : R) : List R :=
  [gap c*phaseValue c (fTail c)-phaseDiff c*fTail c,phaseDiff c]
def actualQn (c : R) : Polynomial R := fromCoeffs (qnCoords c)
def actualQ1 (c : R) : Polynomial R := fromCoeffs [phaseIntercept c,phaseSlope c]

def actualUC (c : R) : Polynomial R :=
  C (gap c)*((X-1)*actualV c) + C (repGamma.val c)*actualT4 c
def actualSecond (c : R) : Polynomial R := C (cNu c)*(X*(1-X)*actualQn c)
def actualLHS (c : R) : Polynomial R := actualMu c*actualUC c-actualSecond c
def actualQuot (c : R) : Polynomial R :=
  fromCoeffs [repQuot0.val c,repQuot1.val c,repQuot2.val c,repQuot3.val c]

def actualU0 (c : R) : Polynomial R := (X-1)*actualV c*C ((cNu c)⁻¹ʳ)
def eRemainder (c : R) : Polynomial R :=
  (actualMu c*actualU0 c-X*(1-X)*actualQ1 c) %ₘ actualD7 c
def bRemainder (c : R) : Polynomial R := (actualMu c*actualT4 c) %ₘ actualD7 c

theorem actualV_eval (c y : R) : (actualV c).eval y = vCubic c y := by
  simp [actualV,vCoords,fromCoeffs,vCubic]
  ring

theorem actualT4_factor (c : R) :
    actualT4 c = (X-C 15)*(X-C (fTail c))*(X-C 6)*(X-C (hTail c)) := by
  simp [actualT4,tailFour,fromCoeffs_polyLin,fromCoeffs]
  ring

theorem fromCoeffs_X_mul (a : List R) : fromCoeffs (0::a) = X*fromCoeffs a := by
  simp [fromCoeffs]

theorem coeff_X_sub_one_fromCoeffs (a : List R) (i : ℕ) :
    (((X-1)*fromCoeffs a).coeff i) = (0::a)[i]?.getD 0-a[i]?.getD 0 := by
  rw [sub_mul,one_mul,←fromCoeffs_X_mul,coeff_sub,coeff_fromCoeffs,coeff_fromCoeffs]

theorem coeff_X_one_sub_X_fromCoeffs (a : List R) (i : ℕ) :
    (X*(1-X)*fromCoeffs a).coeff i = (0::a)[i]?.getD 0-(0::0::a)[i]?.getD 0 := by
  rw [mul_sub,mul_one,sub_mul,mul_assoc,←fromCoeffs_X_mul,←fromCoeffs_X_mul,
    coeff_sub,coeff_fromCoeffs,coeff_fromCoeffs]

theorem coeff_mul_fin (a b : Polynomial R) (i : ℕ) :
    (a*b).coeff i = ∑ k : Fin (i+1), a.coeff k.val*b.coeff (i-k.val) := by
  rw [coeff_mul,Finset.Nat.sum_antidiagonal_eq_sum_range_succ (fun x y => a.coeff x*b.coeff y),
    Finset.sum_range]

theorem natDegree_fromCoeffs (a : List R) : (fromCoeffs a).natDegree ≤ a.length-1 := by
  apply natDegree_le_iff_coeff_eq_zero.mpr
  intro i hi
  rw [coeff_fromCoeffs, List.getElem?_eq_none (by omega)]
  rfl

theorem length_polyLin {S : Type*} [Sub S] [Mul S] (z t : S) (a : List S) :
    (polyLin z t a).length = a.length+1 := by
  induction a generalizing t with
  | nil => rfl
  | cons a as ih => simp [polyLin,ih,Nat.add_assoc]

theorem natDegreeV (c : R) : (actualV c).natDegree ≤ 3 :=
  natDegree_fromCoeffs _

theorem natDegreeT4 (c : R) : (actualT4 c).natDegree ≤ 4 := by
  simpa [actualT4,tailFour,length_polyLin] using
    (natDegree_fromCoeffs (tailFour (15:R) (fTail c) 6 (hTail c)))

theorem natDegreeQn (c : R) : (actualQn c).natDegree ≤ 1 :=
  natDegree_fromCoeffs _

theorem natDegreeQuot (c : R) : (actualQuot c).natDegree ≤ 3 :=
  natDegree_fromCoeffs _

open scoped Classical

theorem actualMu_ofFn (c : R) :
    actualMu c = Polynomial.ofFn 7 (fun i => muCoeff c i.val) := by
  rw [Polynomial.ofFn_eq_sum_monomial,actualMu]
  simp only [C_mul_X_pow_eq_monomial]

theorem natDegreeMu (c : R) : (actualMu c).natDegree ≤ 6 := by
  have h := Polynomial.ofFn_natDegree_lt (by decide : 1≤7) (fun i => muCoeff c i.val)
  rw [actualMu_ofFn]
  omega

theorem coeff_mu_low (c : R) {i : ℕ} (hi : i<7) :
    (actualMu c).coeff i = muCoeff c i := by
  rw [actualMu_ofFn,Polynomial.ofFn_coeff_eq_val_of_lt _ hi]

theorem natDegreeD7 (c : R) : (actualD7 c).natDegree ≤ 7 := by
  have hs : (X^2-C (headSum c)*X+C (headProduct c)) =
      fromCoeffs [headProduct c,-headSum c,(1:R)] := by
    simp [fromCoeffs]; ring
  have hL : (fromCoeffs [headProduct c,-headSum c,(1:R)]).natDegree ≤ 2 := natDegree_fromCoeffs _
  have hR : (fromCoeffs (tailFive 26 (eTail c) (fTail c) 6 (hTail c))).natDegree ≤ 5 := by
    simpa [tailFive,length_polyLin] using
      (natDegree_fromCoeffs (tailFive (26:R) (eTail c) (fTail c) 6 (hTail c)))
  rw [actualD7,hs]
  exact (natDegree_mul_le ..).trans (Nat.add_le_add hL hR)

theorem monicD7 (c : R) : (actualD7 c).Monic := by
  apply monic_of_natDegree_le_of_coeff_eq_one 7 (natDegreeD7 c)
  rw [coeff_actualD7]
  simp [actualD,coeffD,tailFive,polyLin]

theorem natDegreeLHS (c : R) : (actualLHS c).natDegree ≤ 10 := by
  have hX₁ : (X-1 : Polynomial R).natDegree≤1 :=
    (natDegree_sub_le ..).trans (max_le natDegree_X_le (by simp))
  have h₁X : (1-X : Polynomial R).natDegree≤1 :=
    (natDegree_sub_le ..).trans (max_le (by simp) natDegree_X_le)
  have ha : (C (gap c)*((X-1)*actualV c)).natDegree ≤ 4 :=
    (natDegree_C_mul_le ..).trans ((natDegree_mul_le ..).trans (Nat.add_le_add hX₁ (natDegreeV c)))
  have hb : (C (repGamma.val c)*actualT4 c).natDegree ≤ 4 :=
    (natDegree_C_mul_le ..).trans (natDegreeT4 c)
  have hab : (actualUC c).natDegree ≤ 4 :=
    (natDegree_add_le ..).trans (max_le ha hb)
  have hf : (actualMu c*actualUC c).natDegree ≤ 10 :=
    (natDegree_mul_le ..).trans (Nat.add_le_add (natDegreeMu c) hab)
  have hX : (X : Polynomial R).natDegree ≤ 1 := natDegree_X_le
  have h2 : (X*(1-X):Polynomial R).natDegree ≤ 2 :=
    (natDegree_mul_le ..).trans (Nat.add_le_add hX h₁X)
  have hg : (actualSecond c).natDegree ≤ 3 :=
    (natDegree_C_mul_le ..).trans ((natDegree_mul_le ..).trans (Nat.add_le_add h2 (natDegreeQn c)))
  unfold actualLHS
  exact (natDegree_sub_le ..).trans (max_le hf (hg.trans (by decide)))

end Actual
end
end RKResearch.Certified.ERK10FixedQ29Adic.Nonlinear
