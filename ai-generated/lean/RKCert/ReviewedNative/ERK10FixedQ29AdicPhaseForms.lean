module

public import RKCert.ReviewedNative.ERK10FixedQ29AdicHeadForms
public import RKCert.ReviewedNative.ERK10FixedQ29AdicPhaseData
public import Mathlib.Tactic.IntervalCases

@[expose] public section

namespace RKResearch.Certified.ERK10FixedQ29Adic.Nonlinear
open Packed Polynomial
open scoped Ring BigOperators

set_option maxRecDepth 40000
set_option maxHeartbeats 0

noncomputable section

def polyLin {S : Type*} [Sub S] [Mul S] (z : S) : S → List S → List S
  | t, [] => [t]
  | t, a::as => (t-z*a)::polyLin z a as

def tailFive {S : Type*} [Sub S] [Mul S] [OfNat S 0] [OfNat S 1]
    (d e f g h : S) : List S :=
  polyLin h 0 (polyLin g 0 (polyLin f 0 (polyLin e 0 (polyLin d 0 [1]))))

def coeffD {S : Type*} [Add S] [Sub S] [Mul S] [OfNat S 0]
    (tail : List S) (s p : S) (i : ℕ) : S :=
  (0::0::tail)[i]?.getD 0-s*(0::tail)[i]?.getD 0+p*tail[i]?.getD 0

section Polynomials
variable {R : Type*} [CommRing R]

def fromCoeffs : List R → Polynomial R
  | [] => 0
  | a::as => C a + X*fromCoeffs as

theorem coeff_fromCoeffs (a : List R) (i : ℕ) :
    (fromCoeffs a).coeff i = a[i]?.getD 0 := by
  induction a generalizing i with
  | nil => simp [fromCoeffs]
  | cons a as ih =>
    cases i with
    | zero => simp [fromCoeffs, coeff_add]
    | succ i => simp [fromCoeffs, coeff_add, coeff_X_mul, ih]

theorem fromCoeffs_polyLin (z t : R) (a : List R) :
    fromCoeffs (polyLin z t a) = C t+(X-C z)*fromCoeffs a := by
  induction a generalizing t with
  | nil => simp [polyLin,fromCoeffs]
  | cons a as ih =>
    simp only [polyLin,fromCoeffs,ih,map_sub,map_mul]
    ring

theorem fromCoeffs_tailFive (d e f g h : R) :
    fromCoeffs (tailFive d e f g h) =
      (X-C d)*(X-C e)*(X-C f)*(X-C g)*(X-C h) := by
  simp [tailFive,fromCoeffs_polyLin,fromCoeffs]
  ring

def actualD7 (c : R) : Polynomial R :=
  (X^2-C (headSum c)*X+C (headProduct c))*
    fromCoeffs (tailFive 26 (eTail c) (fTail c) 6 (hTail c))

theorem actualD7_factor (c : R) :
    actualD7 c = headQuadratic c*(X-C 26)*(X-C (eTail c))*
      (X-C (fTail c))*(X-C 6)*(X-C (hTail c)) := by
  rw [actualD7,fromCoeffs_tailFive,headQuadratic]
  ring

def actualD (c : R) (i : ℕ) : R :=
  coeffD (tailFive 26 (eTail c) (fTail c) 6 (hTail c)) (headSum c) (headProduct c) i

theorem coeff_actualD7 (c : R) (i : ℕ) : (actualD7 c).coeff i = actualD c i := by
  let t := tailFive (26:R) (eTail c) (fTail c) 6 (hTail c)
  have hf : actualD7 c = fromCoeffs (0::0::t)-C (headSum c)*fromCoeffs (0::t)
      +C (headProduct c)*fromCoeffs t := by
    simp only [actualD7,fromCoeffs,C_0,zero_add,t]
    ring
  rw [hf]
  simp only [actualD,coeffD,coeff_add,coeff_sub,coeff_C_mul,coeff_fromCoeffs,t]

end Polynomials

section FormMaps
variable {R : Type*} [CommRing R]
theorem val_getD (x : R) (a : List Form) (i : ℕ) :
    (a[i]?.getD 0).val x = (a.map (Form.val x))[i]?.getD 0 := by
  induction a generalizing i with
  | nil => simp
  | cons a as ih => cases i <;> simp [ih]

theorem map_polyLin (x : R) (z t : Form) (a : List Form) :
    (polyLin z t a).map (Form.val x) =
    polyLin (z.val x) (t.val x) (a.map (Form.val x)) := by
  induction a generalizing t with
  | nil => simp [polyLin]
  | cons a as ih => simp [polyLin,ih]

theorem map_tailFive (x : R) (d e f g h : Form) :
    (tailFive d e f g h).map (Form.val x) =
    tailFive (d.val x) (e.val x) (f.val x) (g.val x) (h.val x) := by
  simp [tailFive,map_polyLin]

theorem val_coeffD (x : R) (t : List Form) (s p : Form) (i : ℕ) :
    (coeffD t s p i).val x = coeffD (t.map (Form.val x)) (s.val x) (p.val x) i := by
  simp [coeffD,val_getD]

end FormMaps

def exprD (i : ℕ) : Form :=
  coeffD (tailFive 26 (fr repE) (fr repF) 6 (fr repH)) (fr repS) (fr repQ) i

def exprM (i : ℕ) : Form := avgForm (fun y => y*(y-1)*(y-cForm)*y^i)
def actualM {R : Type*} [CommRing R] (c : R) (i : ℕ) : R :=
  avg (fun y => y*(y-1)*(y-c)*y^i)

def repD : ℕ → Rep
  | 0 => repD0
  | 1 => repD1
  | 2 => repD2
  | 3 => repD3
  | 4 => repD4
  | 5 => repD5
  | 6 => repD6
  | 7 => repD7
  | _ => repZero

def repM : ℕ → Rep
  | 0 => repM0
  | 1 => repM1
  | 2 => repM2
  | 3 => repM3
  | 4 => repM4
  | 5 => repM5
  | 6 => repM6
  | _ => repZero

def repMu : ℕ → Rep
  | 0 => repMu0
  | 1 => repMu1
  | 2 => repMu2
  | 3 => repMu3
  | 4 => repMu4
  | 5 => repMu5
  | 6 => repMu6
  | _ => repZero

def exprMu (i : ℕ) : Form :=
  Form.sumFin 8 (fun j => if i<j.val then fr (repD j.val)*fr (repM (j.val-1-i)) else 0)
def muCoeff {R : Type*} [CommRing R] (c : R) (i : ℕ) : R :=
  ∑ j : Fin 8, if i<j.val then actualD c j.val*actualM c (j.val-1-i) else 0

def muF (y : Form) : Form := Form.sumFin 7 (fun i => fr (repMu i.val)*y^i.val)
def muValue {R : Type*} [CommRing R] (c y : R) : R := ∑ i : Fin 7, muCoeff c i.val*y^i.val
def actualMu {R : Type*} [CommRing R] (c : R) : Polynomial R :=
  ∑ i : Fin 7, C (muCoeff c i.val)*X^i.val

@[simp] theorem actualMu_eval {R : Type*} [CommRing R] (c y : R) :
    (actualMu c).eval y = muValue c y := by
  unfold actualMu muValue
  change (evalRingHom y) (∑ i : Fin 7, C (muCoeff c i.val)*X^i.val) = _
  rw [map_sum]
  simp

def exprCNu : Form := (1-15)*vCubicF 15
def phaseF (y : Form) (r : Rep) : Form :=
  (y*fr repCNu)*fr r+muF y*vCubicF y
def exprPhaseF : Form := phaseF (fr repF) repPhaseF
def exprPhaseG : Form := phaseF 6 repPhaseG
def exprPhaseH : Form := phaseF (fr repH) repPhaseH
def exprAligned : Form :=
  (fr repPhaseH-fr repPhaseF)*(6-fr repF)-(fr repPhaseG-fr repPhaseF)*(fr repH-fr repF)

def phaseValue {R : Type*} [CommRing R] (c y : R) : R :=
  (-(muValue c y*vCubic c y))*(y*cNu c)⁻¹ʳ

def phaseSlope {R : Type*} [CommRing R] (c : R) : R :=
  (phaseValue c 6-phaseValue c (fTail c))*(6-fTail c)⁻¹ʳ

def phaseIntercept {R : Type*} [CommRing R] (c : R) : R :=
  phaseValue c (fTail c)-phaseSlope c*fTail c

end
end RKResearch.Certified.ERK10FixedQ29Adic.Nonlinear
