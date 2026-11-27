module

public import Mathlib.Algebra.Ring.Int.Defs
import Mathlib.Tactic.LinearCombination
import Mathlib.Tactic.Ring

@[expose] public section

/-! Fixed degree 3×3×2 integer coordinates, with an interpretation
theorem under three monic relations. This implementation never assumes
an irreducible modulus or an injective interpretation. The sound
arithmetic bridge is reusable for a degree-eighteen order certificate. -/
namespace RKResearch.Certified.CubicCubicQuadraticReplay

abbrev Q2 (T : Type*) := T × T
abbrev Q3 (T : Type*) := T × T × T
abbrev C3 := Q3 Int
abbrev C9 := Q3 C3
abbrev C18 := Q2 C9

def c2 {T : Type*} (pk : Int → T) (i : Int) : Q2 T := (pk i, pk 0)
def c3 {T : Type*} (pk : Int → T) (i : Int) : Q3 T := (pk i, pk 0, pk 0)
def a2 {T : Type*} (add : T → T → T) (p q : Q2 T) : Q2 T :=
  (add p.1 q.1, add p.2 q.2)
def a3 {T : Type*} (add : T → T → T) (p q : Q3 T) : Q3 T :=
  (add p.1 q.1, add p.2.1 q.2.1, add p.2.2 q.2.2)

/-- Remainder of a product under x² = r₀+r₁x. -/
def m2 {T : Type*} (add mul : T → T → T) (r p q : Q2 T) : Q2 T :=
  let h := mul p.2 q.2
  (add (mul p.1 q.1) (mul r.1 h),
   add (add (mul p.1 q.2) (mul p.2 q.1)) (mul r.2 h))

/-- Remainder of a product under x³ = r₀+r₁x+r₂x².
The degree-four contribution is reduced before the degree-three one. -/
def m3 {T : Type*} (add mul : T → T → T) (r p q : Q3 T) : Q3 T :=
  let h4 := mul p.2.2 q.2.2
  let h3 := add (add (mul p.2.1 q.2.2) (mul p.2.2 q.2.1)) (mul r.2.2 h4)
  (add (mul p.1 q.1) (mul r.1 h3),
   add (add (mul p.1 q.2.1) (mul p.2.1 q.1))
     (add (mul r.1 h4) (mul r.2.1 h3)),
   add (add (add (mul p.1 q.2.2) (mul p.2.1 q.2.1)) (mul p.2.2 q.1))
     (add (mul r.2.1 h4) (mul r.2.2 h3)))

structure Reductions where
  inner : C3
  middle : C9
  outer : C18

def pack3 := c3 (fun i => i)
def pack9 := c3 pack3
def pack := c2 pack9
def add3 : C3 → C3 → C3 := a3 Int.add
def add9 : C9 → C9 → C9 := a3 add3
def add : C18 → C18 → C18 := a2 add9
def mul3 (D : Reductions) : C3 → C3 → C3 := m3 Int.add Int.mul D.inner
def mul9 (D : Reductions) : C9 → C9 → C9 := m3 add3 (mul3 D) D.middle
def mul (D : Reductions) : C18 → C18 → C18 := m2 add9 (mul9 D) D.outer

section Soundness

variable {R : Type*} [CommRing R]

def v2 {T : Type*} (ev : T → R) (x : R) (p : Q2 T) : R :=
  ev p.1 + x * ev p.2

def v3 {T : Type*} (ev : T → R) (x : R) (p : Q3 T) : R :=
  ev p.1 + x * ev p.2.1 + x^2 * ev p.2.2

theorem v2_c2 {T : Type*} {ev : T → R} {pk : Int → T}
    (h : ∀ i, ev (pk i) = (i:R)) (x : R) (i : Int) :
    v2 ev x (c2 pk i)=i := by simp [v2,c2,h]

theorem v3_c3 {T : Type*} {ev : T → R} {pk : Int → T}
    (h : ∀ i, ev (pk i) = (i:R)) (x : R) (i : Int) :
    v3 ev x (c3 pk i)=i := by simp [v3,c3,h]

theorem v2_a2 {T : Type*} {ev : T → R} {ad : T → T → T}
    (h : ∀ p q, ev (ad p q)=ev p+ev q) (x : R) (p q : Q2 T) :
    v2 ev x (a2 ad p q)=v2 ev x p+v2 ev x q := by
  simp only [v2,a2,h]
  ring

theorem v3_a3 {T : Type*} {ev : T → R} {ad : T → T → T}
    (h : ∀ p q, ev (ad p q)=ev p+ev q) (x : R) (p q : Q3 T) :
    v3 ev x (a3 ad p q)=v3 ev x p+v3 ev x q := by
  simp only [v3,a3,h]
  ring

theorem v2_m2 {T : Type*} {ev : T → R} {ad ml : T → T → T}
    (ha : ∀ p q, ev (ad p q)=ev p+ev q) (hm : ∀ p q, ev (ml p q)=ev p*ev q)
    {x : R} {r : Q2 T} (hx : x^2=v2 ev x r) (p q : Q2 T) :
    v2 ev x (m2 ad ml r p q)=v2 ev x p*v2 ev x q := by
  simp only [v2] at hx
  simp only [v2,m2,ha,hm]
  linear_combination -(ev p.2*ev q.2)*hx

theorem v3_m3 {T : Type*} {ev : T → R} {ad ml : T → T → T}
    (ha : ∀ p q, ev (ad p q)=ev p+ev q) (hm : ∀ p q, ev (ml p q)=ev p*ev q)
    {x : R} {r : Q3 T} (hx : x^3=v3 ev x r) (p q : Q3 T) :
    v3 ev x (m3 ad ml r p q)=v3 ev x p*v3 ev x q := by
  simp only [v3] at hx
  have hh : x^4 = ev r.2.2*ev r.1 +
      x*(ev r.1+ev r.2.2*ev r.2.1) +
      x^2*(ev r.2.1+ev r.2.2^2) := by
    linear_combination (x+ev r.2.2)*hx
  simp only [v3,m3,ha,hm]
  linear_combination -(ev p.2.1*ev q.2.2+ev p.2.2*ev q.2.1)*hx
    -(ev p.2.2*ev q.2.2)*hh

def val3 (x : R) : C3 → R := v3 (fun i : Int => (i:R)) x
def val9 (x y : R) : C9 → R := v3 (val3 x) y
def val (x y z : R) : C18 → R := v2 (val9 x y) z

structure Roots (D : Reductions) (x y z : R) : Prop where
  inner : x^3=val3 x D.inner
  middle : y^3=val9 x y D.middle
  outer : z^2=val x y z D.outer

theorem val3_pack (x : R) (i : Int) : val3 x (pack3 i)=i := v3_c3 (fun _ => rfl) _ _
theorem val9_pack (x y : R) (i : Int) : val9 x y (pack9 i)=i := v3_c3 (val3_pack x) _ _
theorem val_pack (x y z : R) (i : Int) : val x y z (pack i)=i := v2_c2 (val9_pack x y) _ _
theorem val3_add (x : R) (p q : C3) : val3 x (add3 p q)=val3 x p+val3 x q :=
  v3_a3 (fun a b => Int.cast_add (R:=R) a b) x p q
theorem val9_add (x y : R) (p q : C9) : val9 x y (add9 p q)=val9 x y p+val9 x y q :=
  v3_a3 (val3_add x) y p q
theorem val_add (x y z : R) (p q : C18) : val x y z (add p q)=val x y z p+val x y z q :=
  v2_a2 (val9_add x y) z p q

theorem val3_mul {D : Reductions} {x : R} (h : x^3=val3 x D.inner) (p q : C3) :
    val3 x (mul3 D p q)=val3 x p*val3 x q :=
  v3_m3 (fun a b => Int.cast_add (R:=R) a b) (fun a b => Int.cast_mul (α:=R) a b) h p q

theorem val9_mul {D : Reductions} {x y : R} (hx : x^3=val3 x D.inner)
    (hy : y^3=val9 x y D.middle) (p q : C9) :
    val9 x y (mul9 D p q)=val9 x y p*val9 x y q :=
  v3_m3 (val3_add x) (val3_mul hx) hy p q

theorem val_mul {D : Reductions} {x y z : R} (h : Roots D x y z) (p q : C18) :
    val x y z (mul D p q)=val x y z p*val x y z q :=
  v2_m2 (val9_add x y) (val9_mul h.inner h.middle) h.outer p q

end Soundness

end RKResearch.Certified.CubicCubicQuadraticReplay

#print axioms RKResearch.Certified.CubicCubicQuadraticReplay.val_mul
