module

public import Mathlib.Algebra.BigOperators.Group.Finset.Basic
public import Mathlib.Data.Rat.Cast.Order
public import Mathlib.Data.Rat.Floor

import Mathlib.Tactic.NormNum

@[expose] public section

namespace RKCert.ReviewedNative.DyadicBox64

open scoped BigOperators

/-- Exact rational endpoints. An interval is used only through its
enclosure proposition; that proposition implies the endpoints are ordered. -/
structure Box where
  lo : ℚ
  hi : ℚ
  deriving DecidableEq

def encloses {K : Type*} [Field K] [LinearOrder K] (B : Box) (x : K) : Prop :=
  (B.lo:K) ≤ x ∧ x ≤ (B.hi:K)

def scale : ℚ := (2:ℚ)^64

theorem scale_pos : 0 < scale := by norm_num [scale]

def roundLo (q : ℚ) : ℚ := ((⌊q*scale⌋ : ℤ) : ℚ)/scale
def roundHi (q : ℚ) : ℚ := ((⌈q*scale⌉ : ℤ) : ℚ)/scale

theorem roundLo_le (q : ℚ) : roundLo q ≤ q :=
  (div_le_iff₀ scale_pos).2 (Int.floor_le (q*scale))

theorem le_roundHi (q : ℚ) : q ≤ roundHi q :=
  (le_div_iff₀ scale_pos).2 (Int.le_ceil (q*scale))

def point (q : ℚ) : Box := ⟨q,q⟩
def add (A B : Box) : Box := ⟨A.lo+B.lo,A.hi+B.hi⟩
def sub (A B : Box) : Box := ⟨A.lo-B.hi,A.hi-B.lo⟩

def lowerProduct (A B : Box) : ℚ :=
  min (min (A.lo*B.lo) (A.lo*B.hi)) (min (A.hi*B.lo) (A.hi*B.hi))

def upperProduct (A B : Box) : ℚ :=
  max (max (A.lo*B.lo) (A.lo*B.hi)) (max (A.hi*B.lo) (A.hi*B.hi))

def rawMul (A B : Box) : Box := ⟨lowerProduct A B,upperProduct A B⟩

def outward (B : Box) : Box := ⟨roundLo B.lo,roundHi B.hi⟩

def mul (A B : Box) : Box := outward (rawMul A B)

def divideNat (B : Box) (n : ℕ) : Box :=
  outward ⟨B.lo/(n:ℚ),B.hi/(n:ℚ)⟩

def powBox (B : Box) : ℕ → Box
  | 0 => point 1
  | n+1 => mul (powBox B n) B

def sumBox (A : ℕ → Box) : ℕ → Box
  | 0 => point 0
  | n+1 => add (sumBox A n) (A n)

section Sound

variable {K : Type*} [Field K] [LinearOrder K] [IsStrictOrderedRing K]

theorem point_encloses (q : ℚ) : encloses (point q) (q:K) :=
  ⟨le_rfl,le_rfl⟩

theorem zero_encloses : encloses (point 0) (0:K) := by
  simpa only [Rat.cast_zero] using point_encloses (K:=K) 0

theorem one_encloses : encloses (point 1) (1:K) := by
  simpa only [Rat.cast_one] using point_encloses (K:=K) 1

theorem add_encloses {A B : Box} {x y : K}
    (hx : encloses A x) (hy : encloses B y) : encloses (add A B) (x+y) := by
  simpa only [encloses,add,Rat.cast_add] using
    And.intro (add_le_add hx.1 hy.1) (add_le_add hx.2 hy.2)

theorem sub_encloses {A B : Box} {x y : K}
    (hx : encloses A x) (hy : encloses B y) : encloses (sub A B) (x-y) := by
  simpa only [encloses,sub,Rat.cast_sub] using
    And.intro (sub_le_sub hx.1 hy.2) (sub_le_sub hx.2 hy.1)

private theorem between_mul_right {B : Box} {lo hi x y : K}
    (hl : lo ≤ x) (hh : x ≤ hi)
    (blo : encloses B (lo*y)) (bhi : encloses B (hi*y)) :
    encloses B (x*y) := by
  by_cases hy : 0 ≤ y
  · exact ⟨blo.1.trans (mul_le_mul_of_nonneg_right hl hy),
      (mul_le_mul_of_nonneg_right hh hy).trans bhi.2⟩
  · have hn : y ≤ 0 := le_of_not_ge hy
    exact ⟨bhi.1.trans (mul_le_mul_of_nonpos_right hh hn),
      (mul_le_mul_of_nonpos_right hl hn).trans blo.2⟩

private theorem between_mul_left {B : Box} {lo hi x y : K}
    (hl : lo ≤ x) (hh : x ≤ hi)
    (blo : encloses B (y*lo)) (bhi : encloses B (y*hi)) :
    encloses B (y*x) := by
  have bl : encloses B (lo*y) := by rw [mul_comm]; exact blo
  have bh : encloses B (hi*y) := by rw [mul_comm]; exact bhi
  rw [mul_comm]
  exact between_mul_right hl hh bl bh

theorem rawMul_encloses {A B : Box} {x y : K}
    (hx : encloses A x) (hy : encloses B y) : encloses (rawMul A B) (x*y) := by
  have corner (a b : ℚ) (hl : lowerProduct A B ≤ a*b)
      (hh : a*b ≤ upperProduct A B) : encloses (rawMul A B) ((a:K)*(b:K)) := by
    rw [← Rat.cast_mul]
    exact ⟨Rat.cast_mono hl,Rat.cast_mono hh⟩
  have c00 := corner A.lo B.lo
    ((min_le_left _ _).trans (min_le_left _ _))
    ((le_max_left _ _).trans (le_max_left _ _))
  have c01 := corner A.lo B.hi
    ((min_le_left _ _).trans (min_le_right _ _))
    ((le_max_right _ _).trans (le_max_left _ _))
  have c10 := corner A.hi B.lo
    ((min_le_right _ _).trans (min_le_left _ _))
    ((le_max_left _ _).trans (le_max_right _ _))
  have c11 := corner A.hi B.hi
    ((min_le_right _ _).trans (min_le_right _ _))
    ((le_max_right _ _).trans (le_max_right _ _))
  exact between_mul_right hx.1 hx.2
    (between_mul_left hy.1 hy.2 c00 c01) (between_mul_left hy.1 hy.2 c10 c11)

theorem outward_encloses {B : Box} {x : K} (h : encloses B x) :
    encloses (outward B) x :=
  ⟨(Rat.cast_mono (roundLo_le _)).trans h.1,h.2.trans (Rat.cast_mono (le_roundHi _))⟩

theorem mul_encloses {A B : Box} {x y : K}
    (hx : encloses A x) (hy : encloses B y) : encloses (mul A B) (x*y) :=
  outward_encloses (rawMul_encloses hx hy)

theorem divideNat_encloses {B : Box} {x : K}
    (hx : encloses B x) (n : ℕ) : encloses (divideNat B n) (x/(n:K)) := by
  have hn : 0 ≤ (n:K) := Nat.cast_nonneg n
  have hl : ((B.lo/(n:ℚ):ℚ):K) ≤ x/(n:K) := by
    rw [Rat.cast_div,Rat.cast_natCast]
    exact div_le_div_of_nonneg_right hx.1 hn
  have hh : x/(n:K) ≤ ((B.hi/(n:ℚ):ℚ):K) := by
    rw [Rat.cast_div,Rat.cast_natCast]
    exact div_le_div_of_nonneg_right hx.2 hn
  exact outward_encloses ⟨hl,hh⟩

theorem powBox_encloses {B : Box} {x : K} (hx : encloses B x) (n : ℕ) :
    encloses (powBox B n) (x^n) := by
  induction n with
  | zero => simpa only [powBox,pow_zero] using one_encloses (K:=K)
  | succ n ih => simpa only [powBox,pow_succ] using mul_encloses ih hx

theorem sumBox_encloses {A : ℕ → Box} {f : ℕ → K}
    (hf : ∀ n, encloses (A n) (f n)) (k : ℕ) :
    encloses (sumBox A k) (∑ n ∈ Finset.range k, f n) := by
  induction k with
  | zero => simpa [sumBox] using zero_encloses (K:=K)
  | succ n ih => simpa only [sumBox,Finset.sum_range_succ] using add_encloses ih (hf n)

theorem sign_pos {B : Box} {x : K} (h : encloses B x) (hlo : 0 < B.lo) :
    0 < x := (Rat.cast_pos.mpr hlo).trans_le h.1

theorem sign_neg {B : Box} {x : K} (h : encloses B x) (hhi : B.hi < 0) :
    x < 0 := h.2.trans_lt (Rat.cast_lt_zero.mpr hhi)

end Sound

end RKCert.ReviewedNative.DyadicBox64
