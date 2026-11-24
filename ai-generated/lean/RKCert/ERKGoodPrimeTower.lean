module

public import RKCert.ERKGoodPrimeSmallNorm
public import Mathlib.Tactic.LinearCombination

@[expose] public section

/-! # The ordered-root tower of a monic quartic

The three layers have ranks 4, 3, and 2. Synthetic division by a known
root is used only in the descending degrees of the explicit equations.
The soundness statement is valid even for a tuple with repeated roots
in the specialized tower. -/
namespace RKCert.GoodPrimeDense

structure Box {A : Type*} (o : Operations A) where
  value : A

namespace Box

variable {A : Type*} {o : Operations A}

instance (n : ℕ) : OfNat (Box o) n := ⟨⟨o.int (Int.ofNat n)⟩⟩
instance : Add (Box o) := ⟨fun a b => ⟨o.add a.value b.value⟩⟩
instance : Mul (Box o) := ⟨fun a b => ⟨o.mul a.value b.value⟩⟩
instance : Neg (Box o) := ⟨fun a => ⟨o.neg a.value⟩⟩
instance : Sub (Box o) := ⟨fun a b => a + -b⟩
instance : HPow (Box o) ℕ (Box o) := ⟨fun a n => ⟨pow o a.value n⟩⟩

variable {R : Type*} [CommRing R] {f : A → R} (s : Sound o f)

include s

theorem cast_num (n : ℕ) :
    f ((OfNat.ofNat n : Box o).value) = (n : R) := by
  exact (s.int (Int.ofNat n)).trans (Int.cast_natCast n)

theorem cast_add (a b : Box o) :
    f ((a+b).value) = f a.value + f b.value := s.add _ _

theorem cast_mul (a b : Box o) :
    f ((a*b).value) = f a.value * f b.value := s.mul _ _

theorem cast_neg (a : Box o) :
    f ((-a).value) = -f a.value := s.neg _

theorem cast_sub (a b : Box o) :
    f ((a-b).value) = f a.value - f b.value := by rw [sub_eq_add_neg]; exact (s.add _ _).trans (congrArg (fun x => f a.value + x) (cast_neg s b))

theorem cast_pow (a : Box o) (n : ℕ) :
    f ((a^n).value) = f a.value ^ n := read_pow s _ _

end Box

structure Four (A : Type*) where
  a : A
  b : A
  c : A
  d : A

structure Three (A : Type*) where
  a : A
  b : A
  c : A

structure Two (A : Type*) where
  a : A
  b : A

variable {A B R : Type*}

def Four.map (f : A → B) (q : Four A) : Four B := ⟨f q.a,f q.b,f q.c,f q.d⟩
def Three.map (f : A → B) (q : Three A) : Three B := ⟨f q.a,f q.b,f q.c⟩
def Two.map (f : A → B) (q : Two A) : Two B := ⟨f q.a,f q.b⟩

def Four.shifted [Add A] [Mul A] (q : Four A) (h : A) : Three A :=
  let c := q.d + h
  let b := q.c + h*c
  let a := q.b + h*b
  ⟨a,b,c⟩

def Three.shifted [Add A] [Mul A] (q : Three A) (u : A) : Two A :=
  let b := q.c + u
  let a := q.b + u*b
  ⟨a,b⟩

def Four.rel (o : Operations A) (q : Four A) : List A :=
  [o.neg q.a,o.neg q.b,o.neg q.c,o.neg q.d]

def Three.rel (o : Operations A) (q : Three A) : List A :=
  [o.neg q.a,o.neg q.b,o.neg q.c]

def Two.rel (o : Operations A) (q : Two A) : List A :=
  [o.neg q.a,o.neg q.b]

def Four.eval [CommRing A] (q : Four A) (x : A) : A :=
  x^4+q.d*x^3+q.c*x^2+q.b*x+q.a

def Three.eval [CommRing A] (q : Three A) (x : A) : A :=
  x^3+q.c*x^2+q.b*x+q.a

def Two.eval [CommRing A] (q : Two A) (x : A) : A :=
  x^2+q.b*x+q.a

structure RootSystem [CommRing R] (q : Four R) (h u v : R) : Prop where
  four : q.eval h = 0
  three : (q.shifted h).eval u = 0
  two : ((q.shifted h).shifted u).eval v = 0

variable [CommRing R]

theorem Four.eval_div (q : Four R) (h x : R) :
    q.eval x = (x-h)*(q.shifted h).eval x + q.eval h := by
  simp [Four.eval,Four.shifted,Three.eval]
  ring

theorem Three.eval_div (q : Three R) (u x : R) :
    q.eval x = (x-u)*(q.shifted u).eval x + q.eval u := by
  simp [Three.eval,Three.shifted,Two.eval]
  ring

theorem rootSystem_of_distinct [IsDomain R] {q : Four R} {h u v : R}
    (hk : q.eval h = 0) (uk : q.eval u = 0) (vk : q.eval v = 0)
    (hu : u ≠ h) (hv : v ≠ h) (uv : v ≠ u) : RootSystem q h u v := by
  have f (x : R) (hx : q.eval x = 0) (nx : x ≠ h) : (q.shifted h).eval x = 0 := by
    have z := q.eval_div h x
    rw [hk,hx,add_zero,eq_comm] at z
    exact (mul_eq_zero.mp z).resolve_left (sub_ne_zero.mpr nx)
  have u₁ := f u uk hu
  have v₁ := f v vk hv
  have e := (q.shifted h).eval_div u v
  rw [v₁,u₁,add_zero,eq_comm] at e
  exact ⟨hk,u₁,(mul_eq_zero.mp e).resolve_left (sub_ne_zero.mpr uv)⟩

section Tower

structure Tower (A : Type*) where
  ops : Operations A
  four : Four A

abbrev L1 (A : Type*) := List A
abbrev L2 (A : Type*) := List (List A)
abbrev L3 (A : Type*) := List (List (List A))

variable (t : Tower A)

def Tower.relH : L1 A := t.four.rel t.ops
def Tower.atH : Operations (L1 A) := quotient t.ops t.relH
def Tower.cubic : Three (L1 A) :=
  let q := t.four.map (fun a => (⟨constant t.ops a⟩ : Box t.atH))
  ((q.shifted (⟨generator t.ops⟩ : Box t.atH)).map Box.value)

def Tower.relU : L2 A := t.cubic.rel t.atH
def Tower.atU : Operations (L2 A) := quotient t.atH t.relU
def Tower.quad : Two (L2 A) :=
  let q := t.cubic.map (fun a => (⟨constant t.atH a⟩ : Box t.atU))
  ((q.shifted (⟨generator t.atH⟩ : Box t.atU)).map Box.value)

def Tower.relV : L3 A := t.quad.rel t.atU
def Tower.atV : Operations (L3 A) := quotient t.atU t.relV

def Tower.coe (a : A) : L3 A :=
  constant t.atU (constant t.atH (constant t.ops a))

def Tower.h : L3 A := constant t.atU (constant t.atH (generator t.ops))
def Tower.u : L3 A := constant t.atU (generator t.atH)
def Tower.v : L3 A := generator t.atU

def Tower.relativeNorm (w : L3 A) : A :=
  norm t.ops 4 t.relH (norm t.atH 3 t.relU (norm t.atU 2 t.relV w))

variable {t} {f : A→R} (s : Sound t.ops f) (h u v : R)

include s

theorem Tower.soundH (hk : (t.four.map f).eval h = 0) : Sound t.atH (read f h) := by
  apply Sound.quotient s h (by change 0<4; decide)
  simp only [Tower.relH,Four.rel,read,s.neg,mul_zero,add_zero]
  simp only [Four.eval,Four.map] at hk
  change _ = h^4
  linear_combination -hk

theorem Tower.read_cubic (hk : (t.four.map f).eval h=0) :
    t.cubic.map (read f h) = (t.four.map f).shifted h := by
  have sh := Tower.soundH s h hk
  simp [Tower.cubic,Three.map,Four.map,Four.shifted,Box.cast_add sh,Box.cast_mul sh,
    read_constant s,read_generator s]

theorem Tower.soundU (hk : (t.four.map f).eval h=0)
    (uk : ((t.four.map f).shifted h).eval u=0) :
    Sound t.atU (read (read f h) u) := by
  have sh := Tower.soundH s h hk
  apply Sound.quotient sh u (by change 0<3; decide)
  simp only [Tower.relU,Three.rel,read,sh.neg,mul_zero,add_zero]
  rw [←Tower.read_cubic s h hk] at uk
  simp only [Three.eval,Three.map] at uk
  change _ = u^3
  linear_combination -uk

theorem Tower.read_quad (hk : (t.four.map f).eval h=0)
    (uk : ((t.four.map f).shifted h).eval u=0) :
    t.quad.map (read (read f h) u) = ((t.four.map f).shifted h).shifted u := by
  have sh := Tower.soundH s h hk
  have su := Tower.soundU s h u hk uk
  rw [←Tower.read_cubic s h hk]
  simp [Tower.quad,Two.map,Three.map,Three.shifted,Box.cast_add su,Box.cast_mul su,
    read_constant sh,read_generator sh]

theorem Tower.soundV (p : RootSystem (t.four.map f) h u v) :
    Sound t.atV (read (read (read f h) u) v) := by
  have su := Tower.soundU s h u p.four p.three
  apply Sound.quotient su v (by change 0<2; decide)
  simp only [Tower.relV,Two.rel,read,su.neg,mul_zero,add_zero]
  have vk := p.two
  rw [←Tower.read_quad s h u p.four p.three] at vk
  simp only [Two.eval,Two.map] at vk
  change _ = v^2
  linear_combination -vk

theorem Tower.readCoe (p : RootSystem (t.four.map f) h u v) (a : A) :
    read (read (read f h) u) v (t.coe a) = f a := by
  have sh := Tower.soundH s h p.four
  have su := Tower.soundU s h u p.four p.three
  simp [Tower.coe,read_constant s,read_constant sh,read_constant su]

theorem Tower.readH (p : RootSystem (t.four.map f) h u v) :
    read (read (read f h) u) v t.h = h := by
  have sh := Tower.soundH s h p.four
  have su := Tower.soundU s h u p.four p.three
  simp [Tower.h,read_generator s,read_constant sh,read_constant su]

theorem Tower.readU (p : RootSystem (t.four.map f) h u v) :
    read (read (read f h) u) v t.u = u := by
  have sh := Tower.soundH s h p.four
  have su := Tower.soundU s h u p.four p.three
  simp [Tower.u,read_generator sh,read_constant su]

theorem Tower.readV (p : RootSystem (t.four.map f) h u v) :
    read (read (read f h) u) v t.v = v := by
  exact read_generator (Tower.soundU s h u p.four p.three) v

theorem Tower.norm_zero [IsDomain R] (p : RootSystem (t.four.map f) h u v) (w : L3 A)
    (z : read (read (read f h) u) v w = 0) :
    f (t.relativeNorm w) = 0 := by
  have sh := Tower.soundH s h p.four
  have su := Tower.soundU s h u p.four p.three
  have vEq : read (read (read f h) u) v t.relV = v^2 := by
    simp only [Tower.relV,Two.rel,read,su.neg,mul_zero,add_zero]
    have hv := p.two
    rw [←Tower.read_quad s h u p.four p.three] at hv
    simp only [Two.eval,Two.map] at hv
    linear_combination -hv
  have uEq : read (read f h) u t.relU = u^3 := by
    simp only [Tower.relU,Three.rel,read,sh.neg,mul_zero,add_zero]
    have hu := p.three
    rw [←Tower.read_cubic s h p.four] at hu
    simp only [Three.eval,Three.map] at hu
    linear_combination -hu
  have hEq : read f h t.relH = h^4 := by
    simp only [Tower.relH,Four.rel,read,s.neg,mul_zero,add_zero]
    have hh := p.four
    simp only [Four.eval,Four.map] at hh
    linear_combination -hh
  exact read_norm_eq_zero s h (n:=4) (by decide) rfl hEq _
    (read_norm_eq_zero sh u (n:=3) (by decide) rfl uEq _
      (read_norm_eq_zero su v (n:=2) (by decide) rfl vEq _ z))

end Tower

end RKCert.GoodPrimeDense
