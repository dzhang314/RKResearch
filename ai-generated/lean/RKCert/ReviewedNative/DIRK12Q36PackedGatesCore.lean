module
public import RKCert.ReviewedNative.IntegerPolyPacking
public import RKCert.ReviewedNative.IntegerPolyClearDen
public import RKCert.ReviewedNative.DIRK12MidpointMomentTransfers
public import RKCert.ReviewedNative.DIRK12Q36MomentData
import Mathlib.Tactic.FinCases

@[expose] public section

/-! The two exact support relations are cubic in the physical fifth
clock. The three lower coefficient comparisons each suffice once the
monic fifth polynomial is paid, without division by any alleged root. -/
namespace RKResearch.Certified.DIRK12Q36Moments

open IntegerPolyRootReplay IntegerPolyRootReplay.Packing

def base : Nat := 2^3840

structure Affine where
  c0 : Expr
  c1 : Expr

structure Quad where
  c0 : Expr
  c1 : Expr
  c2 : Expr

structure Cubic where
  c0 : Expr
  c1 : Expr
  c2 : Expr
  c3 : Expr

def affine (x0 x1 : ZP) : Affine := ⟨.atom x0,.atom x1⟩

def prod2 (a b : Affine) : Quad :=
  ⟨.times a.c0 b.c0,.plus (.times a.c0 b.c1) (.times a.c1 b.c0),.times a.c1 b.c1⟩

def prod3 (a : Quad) (b : Affine) : Cubic :=
  ⟨.times a.c0 b.c0,.plus (.times a.c0 b.c1) (.times a.c1 b.c0),
   .plus (.times a.c1 b.c1) (.times a.c2 b.c0),.times a.c2 b.c1⟩

def qcomb (k : Int) (a : Quad) (l : Int) (b : Quad) : Quad :=
  ⟨.minus (.coeff k a.c0) (.coeff l b.c0),
   .minus (.coeff k a.c1) (.coeff l b.c1),
   .minus (.coeff k a.c2) (.coeff l b.c2)⟩

def ccomb (a : Cubic) (l : Int) (b : Cubic) : Cubic :=
  ⟨.minus a.c0 (.coeff l b.c0), .minus a.c1 (.coeff l b.c1),
    .minus a.c2 (.coeff l b.c2), .minus a.c3 (.coeff l b.c3)⟩

def N0 := affine nC0 nX0
def N1 := affine nC1 nX1
def N2 := affine nC2 nX2
def N3 := affine nC3 nX3
def N4 := affine nC4 nX4

def R3 := ccomb (prod3 (qcomb 3 (prod2 N1 N1) 1 (prod2 N0 N2)) N3) 2 (prod3 (prod2 N1 N2) N2)
def R4 := ccomb (prod3 (qcomb 9 (prod2 N1 N1) 4 (prod2 N0 N2)) N4) 5 (prod3 (prod2 N1 N2) N3)

def idx (p : Cubic) (j : Fin 3) : Expr := if j=0 then p.c0 else if j=1 then p.c1 else p.c2
def fCoeff (j : Fin 3) : ZP := if j=0 then F0 else if j=1 then F1 else F2
def gate (p : Cubic) (j : Fin 3) : Expr :=
  .minus (.coeff (fd:Int) (idx p j)) (.times p.c3 (.atom (fCoeff j)))

section
variable {K : Type*} [CommRing K]

def linEval (x f : K) (p : Affine) : K := read x p.c0 + f*read x p.c1

def qEval (x f : K) (p : Quad) : K := read x p.c0 + read x p.c1*f + read x p.c2*f^2

def cEval (x f : K) (p : Cubic) : K :=
  read x p.c0 + read x p.c1*f + read x p.c2*f^2 + read x p.c3*f^3

theorem mul2_correct (x f : K) (a b : Affine) :
    qEval x f (prod2 a b) = linEval x f a * linEval x f b := by
  simp only [qEval,prod2,linEval,Packing.read]
  ring

theorem mul3_correct (x f : K) (a : Quad) (b : Affine) :
    cEval x f (prod3 a b) = qEval x f a * linEval x f b := by
  simp only [cEval,prod3,qEval,linEval,Packing.read]
  ring

theorem qcomb_correct (x f : K) (u v : Int) (a b : Quad) :
    qEval x f (qcomb u a v b) = (u:K)*qEval x f a-(v:K)*qEval x f b := by
  simp only [qEval,qcomb,Packing.read]
  ring

theorem ccomb_correct (x f : K) (u : Int) (a b : Cubic) :
    cEval x f (ccomb a u b) = cEval x f a - (u:K)*cEval x f b := by
  simp only [cEval,ccomb,Packing.read]
  ring

theorem r3_read (x f : K) :
    cEval x f R3 = DIRK12MidpointMomentTransfers.rel3
      (linEval x f N0) (linEval x f N1) (linEval x f N2) (linEval x f N3) := by
  simp only [R3,ccomb_correct,mul3_correct,qcomb_correct,mul2_correct,
    DIRK12MidpointMomentTransfers.rel3,DIRK12MidpointMomentTransfers.B,Int.cast_ofNat]
  ring

theorem r4_read (x f : K) :
    cEval x f R4 = DIRK12MidpointMomentTransfers.rel4
      (linEval x f N0) (linEval x f N1) (linEval x f N2) (linEval x f N3) (linEval x f N4) := by
  simp only [R4,ccomb_correct,mul3_correct,qcomb_correct,mul2_correct,
    DIRK12MidpointMomentTransfers.rel4,DIRK12MidpointMomentTransfers.A,Int.cast_ofNat]
  ring

end

section
variable {K : Type*} [Field K] [CharZero K]

theorem from_coefficient_checks (x f : K) (p : Cubic) (dNZ : (fd:K) ≠ 0)
    (fRoot : eval F0 x + eval F1 x*f + eval F2 x*f^2 + (fd:K)*f^3=0)
    (checks : ∀ j : Fin 3, read x (gate p j)=0) : cEval x f p=0 := by
  apply cubic_transfer_of_three dNZ fRoot
  · simpa [gate,idx,fCoeff,Packing.read] using checks (0:Fin 3)
  · simpa [gate,idx,fCoeff,Packing.read] using checks (1:Fin 3)
  · simpa [gate,idx,fCoeff,Packing.read] using checks (2:Fin 3)

end

end RKResearch.Certified.DIRK12Q36Moments
