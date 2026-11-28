module

public import Mathlib.Algebra.Ring.Defs
import Mathlib.Tactic.Ring

@[expose] public section

/-! Integer coordinates in a tower of four monic quadratic extensions.
The first three defining quadratics are square-root relations. -/
namespace RKResearch.Certified.QuadTowerIntReplay

abbrev Q (T : Type) := T × T
abbrev C2 := Q Int
abbrev C4 := Q C2
abbrev C8 := Q C4
abbrev C16 := Q C8

def pack2 (x : Int) : C2 := (x,0)
def pack4 (x : Int) : C4 := (pack2 x,pack2 0)
def pack8 (x : Int) : C8 := (pack4 x,pack4 0)
def pack (x : Int) : C16 := (pack8 x,pack8 0)

def addStep {T : Type} (f : T → T → T) (u v : Q T) : Q T :=
  (f u.1 v.1, f u.2 v.2)
def add2 : C2 → C2 → C2 := addStep Int.add
def add4 : C4 → C4 → C4 := addStep add2
def add8 : C8 → C8 → C8 := addStep add4
def add : C16 → C16 → C16 := addStep add8

def mulSqStep {T : Type} (plus times : T → T → T) (d : T) (a b : Q T) : Q T :=
  (plus (times a.1 b.1) (times d (times a.2 b.2)),
   plus (times a.1 b.2) (times a.2 b.1))
def mulStep {T : Type} (plus times : T → T → T) (d e : T) (a b : Q T) : Q T :=
  (plus (times a.1 b.1) (times d (times a.2 b.2)),
   plus (plus (times a.1 b.2) (times a.2 b.1)) (times e (times a.2 b.2)))

structure Reductions where
  first : Int
  second : C2
  third : C4
  fourth0 : C8
  fourth1 : C8

def mul2 (d : Reductions) : C2 → C2 → C2 := mulSqStep Int.add Int.mul d.first
def mul4 (d : Reductions) : C4 → C4 → C4 := mulSqStep add2 (mul2 d) d.second
def mul8 (d : Reductions) : C8 → C8 → C8 := mulSqStep add4 (mul4 d) d.third
def mul (d : Reductions) : C16 → C16 → C16 := mulStep add8 (mul8 d) d.fourth0 d.fourth1

def sc2 (n : Int) (v : C2) : C2 := (n*v.1,n*v.2)
def sc4 (n : Int) (v : C4) : C4 := (sc2 n v.1,sc2 n v.2)
def sc8 (n : Int) (v : C8) : C8 := (sc4 n v.1,sc4 n v.2)
def sc (n : Int) (v : C16) : C16 := (sc8 n v.1,sc8 n v.2)

section Semantics
variable {R : Type*} [CommRing R]
def atRoot {T : Type} (v : T → R) (r : R) (a : Q T) : R := v a.1 + r * v a.2
def val2 (x : R) : C2 → R := atRoot (fun i : Int => (i:R)) x
def val4 (x y : R) : C4 → R := atRoot (val2 x) y
def val8 (x y z : R) : C8 → R := atRoot (val4 x y) z
def val (x y z w : R) : C16 → R := atRoot (val8 x y z) w

structure Roots (d : Reductions) (x y z w : R) : Prop where
  first : x*x=d.first
  second : y*y=val2 x d.second
  third : z*z=val4 x y d.third
  fourth : w*w=val8 x y z d.fourth0 + w*val8 x y z d.fourth1

@[simp] theorem val_pack2 (x : R) (i : Int) : val2 x (pack2 i)=i := by simp [val2,atRoot,pack2]
@[simp] theorem val_pack4 (x y : R) (i : Int) : val4 x y (pack4 i)=i := by simp [val4,atRoot,pack4]
@[simp] theorem val_pack8 (x y z : R) (i : Int) : val8 x y z (pack8 i)=i := by simp [val8,atRoot,pack8]
@[simp] theorem val_pack (x y z w : R) (i : Int) : val x y z w (pack i)=i := by simp [val,atRoot,pack]

private theorem atRoot_add {T : Type} {f : T → T → T} {v : T → R} {x : R}
    (h : ∀ a b, v (f a b)=v a+v b) (a b : Q T) :
    atRoot v x (addStep f a b)=atRoot v x a+atRoot v x b := by
  simp only [atRoot,addStep,h]; ring

theorem val_add2 (x : R) (a b : C2) : val2 x (add2 a b)=val2 x a+val2 x b :=
  atRoot_add (fun a b => Int.cast_add a b) a b
theorem val_add4 (x y : R) (a b : C4) : val4 x y (add4 a b)=val4 x y a+val4 x y b :=
  atRoot_add (val_add2 x) a b
theorem val_add8 (x y z : R) (a b : C8) : val8 x y z (add8 a b)=val8 x y z a+val8 x y z b :=
  atRoot_add (val_add4 x y) a b
theorem val_add (x y z w : R) (a b : C16) : val x y z w (add a b)=val x y z w a+val x y z w b :=
  atRoot_add (val_add8 x y z) a b

private theorem atRoot_mul_sq {T : Type} {f g : T → T → T} {v : T → R} {d : T} {x : R}
    (h : x*x=v d) (ha : ∀ a b, v (f a b)=v a+v b)
    (hm : ∀ a b, v (g a b)=v a*v b) (a b : Q T) :
    atRoot v x (mulSqStep f g d a b)=atRoot v x a*atRoot v x b := by
  simp only [atRoot,mulSqStep,ha,hm]; rw [←h]; ring

private theorem atRoot_mul {T : Type} {f g : T → T → T} {v : T → R} {d e : T} {x : R}
    (h : x*x=v d+x*v e) (ha : ∀ a b, v (f a b)=v a+v b)
    (hm : ∀ a b, v (g a b)=v a*v b) (a b : Q T) :
    atRoot v x (mulStep f g d e a b)=atRoot v x a*atRoot v x b := by
  simp only [atRoot,mulStep,ha,hm]
  calc
    _ = v a.1*v b.1 + x*(v a.1*v b.2+v a.2*v b.1) + (v d+x*v e)*(v a.2*v b.2) := by ring
    _ = _ := by rw [←h]; ring

theorem val_mul2 {d : Reductions} {x : R} (h : x*x=d.first) (a b : C2) :
    val2 x (mul2 d a b)=val2 x a*val2 x b :=
  atRoot_mul_sq h (fun a b => Int.cast_add a b) (fun a b => Int.cast_mul a b) a b
theorem val_mul4 {d : Reductions} {x y : R} (h : x*x=d.first) (hy : y*y=val2 x d.second) (a b : C4) :
    val4 x y (mul4 d a b)=val4 x y a*val4 x y b :=
  atRoot_mul_sq hy (val_add2 x) (val_mul2 h) a b
theorem val_mul8 {d : Reductions} {x y z : R} (h : x*x=d.first) (hy : y*y=val2 x d.second)
    (hz : z*z=val4 x y d.third) (a b : C8) : val8 x y z (mul8 d a b)=val8 x y z a*val8 x y z b :=
  atRoot_mul_sq hz (val_add4 x y) (val_mul4 h hy) a b
theorem val_mul {d : Reductions} {x y z w : R} (h : Roots d x y z w) (a b : C16) :
    val x y z w (mul d a b)=val x y z w a*val x y z w b :=
  atRoot_mul h.fourth (val_add8 x y z) (val_mul8 h.first h.second h.third) a b

theorem val_sc2 (x : R) (n : Int) (a : C2) : val2 x (sc2 n a)=(n:R)*val2 x a := by
  simp only [val2,atRoot,sc2,Int.cast_mul]; ring
theorem val_sc4 (x y : R) (n : Int) (a : C4) : val4 x y (sc4 n a)=(n:R)*val4 x y a := by
  simp only [val4,atRoot,sc4,val_sc2]; ring
theorem val_sc8 (x y z : R) (n : Int) (a : C8) : val8 x y z (sc8 n a)=(n:R)*val8 x y z a := by
  simp only [val8,atRoot,sc8,val_sc4]; ring
theorem val_sc (x y z w : R) (n : Int) (a : C16) : val x y z w (sc n a)=(n:R)*val x y z w a := by
  simp only [val,atRoot,sc,val_sc8]; ring
end Semantics

end RKResearch.Certified.QuadTowerIntReplay
