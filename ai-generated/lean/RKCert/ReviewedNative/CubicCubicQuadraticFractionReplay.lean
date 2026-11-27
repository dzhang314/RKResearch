module

public import RKCert.ReviewedNative.CubicCubicQuadraticReplay
public import Mathlib.Algebra.CharZero.Defs
public import Mathlib.Algebra.Field.Defs
import Mathlib.Tactic.FieldSimp
import Mathlib.Tactic.Ring

@[expose] public section

/-! Exact unreduced fractions over a monic integral three-layer
coefficient algebra. Equality receipts use cross multiplication, avoiding
a rational gcd at every printed coordinate during kernel reduction. -/
namespace RKResearch.Certified.CubicCubicQuadraticFractionReplay

open CubicCubicQuadraticReplay (Reductions Q3 C3 C9 val3 val9)
abbrev Raw := CubicCubicQuadraticReplay.C18
abbrev Roots {R : Type*} [CommRing R] := @CubicCubicQuadraticReplay.Roots R _

structure C18 where
  num : Raw
  dp : Nat
  deriving DecidableEq

def C18.den (a : C18) : Nat := a.dp+1
def dpMul (a b : C18) : Nat := a.dp*b.dp+a.dp+b.dp
def pack (a : Int) : C18 := ⟨CubicCubicQuadraticReplay.pack a,0⟩
def sc3 (s : Int) (v : C3) : C3 := (s*v.1,s*v.2.1,s*v.2.2)
def sc9 (s : Int) (v : C9) : C9 := (sc3 s v.1,sc3 s v.2.1,sc3 s v.2.2)
def content (s : Int) (v : Raw) : Raw := (sc9 s v.1, sc9 s v.2)

def add (a b : C18) : C18 :=
  if a.num = CubicCubicQuadraticReplay.pack 0 then b
  else if b.num = CubicCubicQuadraticReplay.pack 0 then a
  else if a.dp = b.dp then ⟨CubicCubicQuadraticReplay.add a.num b.num,a.dp⟩
  else ⟨CubicCubicQuadraticReplay.add (content b.den a.num) (content a.den b.num),dpMul a b⟩

def mul (D : Reductions) (a b : C18) : C18 :=
  ⟨CubicCubicQuadraticReplay.mul D a.num b.num,dpMul a b⟩

def eqf (a b : C18) : Bool :=
  if a.dp = b.dp then decide (a.num=b.num)
  else decide (content b.den a.num=content a.den b.num)

section Field

variable {R : Type*} [Field R] [CharZero R]

def val (x y z : R) (p : C18) : R :=
  CubicCubicQuadraticReplay.val x y z p.num / (p.den:R)

theorem den_ne (a : C18) : (a.den:R) ≠ 0 := by
  exact Nat.cast_ne_zero.mpr (Nat.succ_ne_zero a.dp)

theorem den_prod (a b : C18) :
    (((dpMul a b)+1 : Nat):R) = (a.den:R)*(b.den:R) := by
  simp only [dpMul,C18.den,Nat.cast_add,Nat.cast_mul,Nat.cast_one]
  ring

theorem val_sc3 (s : Int) (x : R) (v : C3) :
    val3 x (sc3 s v) = (s:R)*val3 x v := by
  unfold val3 CubicCubicQuadraticReplay.v3 sc3
  push_cast
  ring

theorem val_sc9 (s : Int) (x y : R) (v : C9) :
    val9 x y (sc9 s v) = (s:R)*val9 x y v := by
  simp only [sc9,val9,CubicCubicQuadraticReplay.v3,val_sc3]
  ring

theorem val_content (s : Int) (x y z : R) (v : Raw) :
    CubicCubicQuadraticReplay.val x y z (content s v) =
      (s:R)*CubicCubicQuadraticReplay.val x y z v := by
  simp only [content,CubicCubicQuadraticReplay.val,CubicCubicQuadraticReplay.v2,val_sc9]
  ring

@[simp] theorem val_pack (x y z : R) (i : Int) : val x y z (pack i)=i := by
  simp [val,pack,C18.den,CubicCubicQuadraticReplay.val_pack]

theorem val_add (x y z : R) (a b : C18) :
    val x y z (add a b) = val x y z a + val x y z b := by
  unfold add
  split
  next h0 => simp [val,h0,CubicCubicQuadraticReplay.val_pack]
  next =>
    split
    next h0 => simp [val,h0,CubicCubicQuadraticReplay.val_pack]
    next =>
      split
      next h =>
        have hd : a.den=b.den := by simp [C18.den,h]
        simp only [val,CubicCubicQuadraticReplay.val_add,C18.den] at *
        rw [h,add_div]
      next =>
        rw [val]
        change CubicCubicQuadraticReplay.val x y z
          (CubicCubicQuadraticReplay.add (content b.den a.num) (content a.den b.num)) /
          (((dpMul a b)+1:Nat):R) = _
        rw [CubicCubicQuadraticReplay.val_add,val_content,val_content,den_prod]
        simp only [val,Int.cast_natCast]
        field_simp [den_ne (R:=R) a,den_ne (R:=R) b] <;> ring

theorem val_mul {D : Reductions} {x y z : R} (h : Roots D x y z) (a b : C18) :
    val x y z (mul D a b) = val x y z a * val x y z b := by
  change CubicCubicQuadraticReplay.val x y z
    (CubicCubicQuadraticReplay.mul D a.num b.num) / (((dpMul a b)+1:Nat):R) = _
  rw [CubicCubicQuadraticReplay.val_mul h,den_prod]
  simp only [val,div_mul_div_comm]

theorem val_eqf {x y z : R} {a b : C18} (h : eqf a b=true) :
    val x y z a=val x y z b := by
  unfold eqf at h
  split at h
  next h0 =>
    have he := of_decide_eq_true h
    simp [val,he,C18.den,h0]
  next =>
    have he := congrArg (CubicCubicQuadraticReplay.val x y z) (of_decide_eq_true h)
    rw [val_content,val_content,Int.cast_natCast,Int.cast_natCast] at he
    apply (div_eq_div_iff (den_ne (R:=R) a) (den_ne (R:=R) b)).2
    simpa [mul_comm] using he

end Field

end RKResearch.Certified.CubicCubicQuadraticFractionReplay

#print axioms RKResearch.Certified.CubicCubicQuadraticFractionReplay.val_eqf
