module

public import RKCert.ReviewedNative.ERKQuadraticIntegerReplay
import Mathlib.Algebra.BigOperators.Fin
import Mathlib.Tactic.Ring
import Mathlib.Tactic.NormNum

@[expose] public section

/-! Integer arithmetic on eight nested radical coordinates. The evaluator
requires only the three square relations, not an ordered target, a field,
or linear independence of the eight products. -/

namespace RKResearch.Certified.ERKNestedRadicalReplay


abbrev Quad (T : Type*) := T × T
abbrev C4 := Quad ERKQuadraticIntegerReplay.Pair
abbrev C8 := Quad C4

def withConst {T : Type*} (pack : ℤ → T) (a : ℤ) : Quad T := (pack a, pack 0)
def withAdd {T : Type*} (add : T → T → T) (p q : Quad T) : Quad T :=
  (add p.1 q.1, add p.2 q.2)
def withMul {T : Type*} (add mul : T → T → T) (sq : T) (p q : Quad T) : Quad T :=
  (add (mul p.1 q.1) (mul sq (mul p.2 q.2)), add (mul p.1 q.2) (mul p.2 q.1))

def pack4 := withConst ERKQuadraticIntegerReplay.pack
def add4 := withAdd ERKQuadraticIntegerReplay.add
def mul4 := withMul ERKQuadraticIntegerReplay.add (ERKQuadraticIntegerReplay.mul 3) (ERKQuadraticIntegerReplay.pack 7)
def pack := withConst pack4
def add := withAdd add4
def mul := withMul add4 mul4 (((147,0),(42,0)) : C4)

variable {R : Type*} [CommRing R]

def withVal {T : Type*} (val : T → R) (s : R) (p : Quad T) : R :=
  val p.1 + s * val p.2

theorem withVal_pack {T : Type*} {vp : T → R} {pk : ℤ → T}
    (hp : ∀ a, vp (pk a) = a) (s : R) (a : ℤ) :
    withVal vp s (withConst pk a) = (a : R) := by
  simp [withVal, withConst, hp]

theorem withVal_add {T : Type*} {vp : T → R} {ad : T → T → T}
    (hp : ∀ p q, vp (ad p q) = vp p + vp q) (s : R) (p q : Quad T) :
    withVal vp s (withAdd ad p q) = withVal vp s p + withVal vp s q := by
  simp only [withVal, withAdd, hp]
  ring

theorem withVal_mul {T : Type*} {vp : T → R} {ad ml : T → T → T} {sq : T} {s : R}
    (ha : ∀ p q, vp (ad p q) = vp p + vp q)
    (hm : ∀ p q, vp (ml p q) = vp p * vp q)
    (hs : s*s = vp sq) (p q : Quad T) :
    withVal vp s (withMul ad ml sq p q) = withVal vp s p * withVal vp s q := by
  simp only [withVal, withMul, ha, hm, ← hs]
  ring

def val4 (x y : R) := withVal (ERKQuadraticIntegerReplay.val x) y
def val (x y z : R) := withVal (val4 x y) z

theorem val4_pack (x y : R) (a : ℤ) : val4 x y (pack4 a) = (a : R) :=
  withVal_pack (ERKQuadraticIntegerReplay.val_pack x) y a
theorem val4_add (x y : R) (p q : C4) : val4 x y (add4 p q) = val4 x y p + val4 x y q :=
  withVal_add (ERKQuadraticIntegerReplay.val_add x) y p q
theorem val4_mul {x y : R} (hx : x*x = 3) (hy : y*y = 7) (p q : C4) :
    val4 x y (mul4 p q) = val4 x y p * val4 x y q := by
  apply withVal_mul (ERKQuadraticIntegerReplay.val_add x) (ERKQuadraticIntegerReplay.val_mul (δ := 3) (by simpa using hx))
  rw [ERKQuadraticIntegerReplay.val_pack]
  simpa using hy

theorem val_pack (x y z : R) (a : ℤ) : val x y z (pack a) = (a : R) :=
  withVal_pack (val4_pack x y) z a
theorem val_add (x y z : R) (p q : C8) : val x y z (add p q) = val x y z p + val x y z q :=
  withVal_add (val4_add x y) z p q

structure Roots (x y z : R) : Prop where
  x_sq : x*x = 3
  y_sq : y*y = 7
  z_sq : z*z = 147+42*y

theorem val_mul {x y z : R} (h : Roots x y z) (p q : C8) :
    val x y z (mul p q) = val x y z p * val x y z q := by
  apply withVal_mul (val4_add x y) (val4_mul h.x_sq h.y_sq)
  unfold val4 withVal ERKQuadraticIntegerReplay.val
  norm_num [h.z_sq]; ring

/-- The direct evaluator skips exact zero taps before entering the expensive
extension arithmetic. Equality with the mathematical dot product is proved
after evaluating into the coefficient ring. -/
def dot : (n : ℕ) → (Fin n → C8) → (Fin n → C8) → C8
  | 0, _, _ => pack 0
  | n+1, a, b => add (if a 0 = pack 0 then pack 0 else mul (a 0) (b 0))
    (dot n (a ∘ Fin.succ) (b ∘ Fin.succ))

open scoped Matrix

theorem val_dot {x y z : R} (h : Roots x y z) (n : ℕ) (a b : Fin n → C8) :
    val x y z (dot n a b) =
      (fun i => val x y z (a i)) ⬝ᵥ (fun i => val x y z (b i)) := by
  induction n with
  | zero => simp [dot, val_pack, dotProduct]
  | succ n ih =>
    simp only [dot, val_add, ih, dotProduct, Fin.sum_univ_succ, Function.comp_apply]
    split
    next H => simp [H, val_pack]
    next H => rw [val_mul h]

def pow (p : C8) : ℕ → C8
  | 0 => pack 1
  | n+1 => mul (pow p n) p

theorem val_pow {x y z : R} (h : Roots x y z) (p : C8) (n : ℕ) :
    val x y z (pow p n) = val x y z p ^ n := by
  induction n with
  | zero => simp [pow, val_pack]
  | succ n ih => rw [pow, val_mul h, ih, pow_succ]

end RKResearch.Certified.ERKNestedRadicalReplay
