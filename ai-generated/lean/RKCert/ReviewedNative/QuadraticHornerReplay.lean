module

public import RKCert.ReviewedNative.IntegerHornerCertificate
public import Mathlib.Data.Matrix.Mul
public import Mathlib.Algebra.BigOperators.Fin

import Mathlib.Tactic.Ring

@[expose] public section

/-! # Packed quadratic coefficients over an integer polynomial root

The second generator satisfies `y² = U(x)y - V(x)`. A pair of integer
polynomial expressions has an honest scalar interpretation at these roots.
Finite dot products and coordinate comparisons are checked without
constructing or computing in a quotient field. -/

namespace RKCert.ReviewedNative.QuadraticHornerReplay

open IntegerHornerCertificate
open scoped Matrix

structure QExpr where
  re : Expr
  im : Expr

namespace QExpr

def atom (re im : List ℤ) : QExpr := ⟨.atom re,.atom im⟩
def const (n : ℤ) : QExpr := atom [n] []
def zero : QExpr := atom [] []

def val {R : Type*} [CommRing R] (x y : R) (a : QExpr) : R :=
  a.re.val x + y*a.im.val x

def add (a b : QExpr) : QExpr := ⟨.add a.re b.re,.add a.im b.im⟩

def scale (c : Expr) (a : QExpr) : QExpr := ⟨.mul c a.re,.mul c a.im⟩

def mul (U V : Expr) (a b : QExpr) : QExpr :=
  let h := Expr.mul a.im b.im
  ⟨Expr.sub (.mul a.re b.re) (.mul V h),
   .add (.add (.mul a.re b.im) (.mul a.im b.re)) (.mul U h)⟩

theorem val_zero {R : Type*} [CommRing R] (x y : R) : zero.val x y = 0 := by
  simp [zero,atom,val,Expr.val,coeval,horner]

theorem val_const {R : Type*} [CommRing R] (x y : R) (n : ℤ) :
    (const n).val x y = (n:R) := by
  simp [const,atom,val,Expr.val,coeval,horner]

theorem val_add {R : Type*} [CommRing R] (x y : R) (a b : QExpr) :
    (a.add b).val x y = a.val x y+b.val x y := by
  simp only [add,val,Expr.val]
  ring

theorem val_scale {R : Type*} [CommRing R] (x y : R) (c : Expr) (a : QExpr) :
    (a.scale c).val x y = c.val x*a.val x y := by
  simp only [scale,val,Expr.val]
  ring

theorem val_mul {R : Type*} [CommRing R] (x y : R) (U V : Expr)
    (h : y^2 = U.val x*y-V.val x) (a b : QExpr) :
    (mul U V a b).val x y = a.val x y*b.val x y := by
  simp only [mul,Expr.sub,val,Expr.val]
  calc
    _ = a.re.val x*b.re.val x +
        y*(a.re.val x*b.im.val x + a.im.val x*b.re.val x) +
        (U.val x*y-V.val x)*(a.im.val x*b.im.val x) := by ring
    _ = _ := by rw [←h]; ring

def eqMod (P : List ℤ) (digits : ℕ) (a b : QExpr) : Bool :=
  checkLocal P digits (a.re.sub b.re) && checkLocal P digits (a.im.sub b.im)

theorem eqMod_sound {R : Type*} [CommRing R] {P : List ℤ} {digits : ℕ}
    {a b : QExpr} (h : eqMod P digits a b = true) {x y : R}
    (hx : coeval P x = 0) : a.val x y = b.val x y := by
  obtain ⟨hre,him⟩ := Bool.and_eq_true_iff.mp h
  have hr := checkLocal_sound hre hx
  have hi := checkLocal_sound him hx
  change a.re.val x + -b.re.val x = 0 at hr
  change a.im.val x + -b.im.val x = 0 at hi
  rw [←sub_eq_add_neg,sub_eq_zero] at hr hi
  simp only [val,hr,hi]

/-- Dot product with a fixed stage dimension and a checked quadratic law. -/
def dot (U V : Expr) : (n : ℕ) → (Fin n → QExpr) → (Fin n → QExpr) → QExpr
  | 0, _, _ => zero
  | n+1, a, b => (mul U V (a 0) (b 0)).add (dot U V n (a ∘ Fin.succ) (b ∘ Fin.succ))

theorem val_dot {R : Type*} [CommRing R] (x y : R) (U V : Expr)
    (hy : y^2 = U.val x*y-V.val x) (n : ℕ) (a b : Fin n→QExpr) :
    (dot U V n a b).val x y = (val x y ∘ a) ⬝ᵥ (val x y ∘ b) := by
  induction n with
  | zero => simp [dot,val_zero,dotProduct]
  | succ n ih =>
    simp only [dot,val_add,val_mul x y U V hy,ih,dotProduct,Fin.sum_univ_succ,Function.comp_apply]

def checkVec {n : ℕ} (P : List ℤ) (d : ℕ) (a b : Fin n → QExpr) : Bool :=
  (List.finRange n).all fun i => eqMod P d (a i) (b i)

theorem checkVec_sound {R : Type*} [CommRing R] {n d : ℕ}
    {P : List ℤ} {a b : Fin n→QExpr} (h : checkVec P d a b = true) {x y : R}
    (hx : coeval P x = 0) :
    val x y ∘ a = val x y ∘ b := by
  funext i
  exact eqMod_sound ((List.all_eq_true.mp h) i (List.mem_finRange i)) hx

end QExpr

end RKCert.ReviewedNative.QuadraticHornerReplay
