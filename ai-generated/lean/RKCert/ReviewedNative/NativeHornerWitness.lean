module

public import Mathlib.Algebra.Ring.Hom.Defs
import Mathlib.Tactic.Ring

@[expose] public section

/-! # Small dense Horner witnesses in several variables

An encoded coefficient need not form a ring. We require only that its three
executable operations have the stated values in a target ring. Iteration
therefore supports independent polynomial variables without any quotient
ring computations or classical noncomputable polynomial operations. -/
namespace RKResearch.Certified.Graded.NativeHornerWitness

universe u v

structure Ops (D : Type u) where
  zero : D
  add : D → D → D
  mul : D → D → D

def ringOps (D : Type u) [CommRing D] : Ops D := ⟨0,(·+·),(·*·)⟩

structure Sound {D : Type u} {K : Type v} [CommRing K] (s : Ops D) (f : D → K) : Prop where
  zero : f s.zero = 0
  add : ∀ a b, f (s.add a b) = f a + f b
  mul : ∀ a b, f (s.mul a b) = f a * f b

theorem ringHom_sound {D K : Type*} [CommRing D] [CommRing K] (q : D →+* K) :
    Sound (ringOps D) (fun x => q x) := ⟨q.map_zero, q.map_add, q.map_mul⟩

def horner {D K : Type*} [CommRing K] (f : D → K) (z : K) : List D → K
  | [] => 0
  | a::l => f a + z * horner f z l

namespace Ops

variable {D : Type u} (s : Ops D) [DecidableEq D]

/-- Drop only a trailing zero. Least-degree coefficients come first. -/
def cons (a : D) : List D → List D
  | [] => if a = s.zero then [] else [a]
  | h::t => a::h::t

def ladd : List D → List D → List D
  | [], b => b
  | a::t, [] => a::t
  | a::t, b::v => s.cons (s.add a b) (ladd t v)

def scale (a : D) : List D → List D
  | [] => []
  | b::t => s.cons (s.mul a b) (scale a t)

def times : List D → List D → List D
  | [], _ => []
  | a::t, b => s.ladd (s.scale a b) (s.cons s.zero (times t b))

def poly : Ops (List D) := ⟨[],s.ladd,s.times⟩

variable {K : Type v} [CommRing K] {f : D → K} (h : Sound s f) (z : K)

include h

theorem horner_cons (a : D) (l : List D) :
    horner f z (s.cons a l) = f a + z*horner f z l := by
  cases l with
  | nil =>
    by_cases ha : a = s.zero
    · subst a
      simp [cons,horner,h.zero]
    · simp [cons,horner,ha]
  | cons b t => rfl

theorem horner_add (a b : List D) :
    horner f z (s.ladd a b) = horner f z a + horner f z b := by
  induction a generalizing b with
  | nil => simp [ladd,horner]
  | cons v t ih =>
    cases b with
    | nil => simp [ladd,horner]
    | cons w u =>
      simp only [ladd,horner_cons s h z, h.add,ih,horner]
      ring

theorem horner_scale (a : D) (b : List D) :
    horner f z (s.scale a b) = f a * horner f z b := by
  induction b with
  | nil => simp [scale,horner]
  | cons w t ih =>
    simp only [scale,horner_cons s h z,h.mul,ih,horner]
    ring

theorem horner_times (a b : List D) :
    horner f z (s.times a b) = horner f z a * horner f z b := by
  induction a with
  | nil => simp [times,horner]
  | cons w u ih =>
    simp only [times,horner_add s h z,horner_scale s h z,horner_cons s h z,h.zero,ih,horner]
    ring

theorem poly_sound : Sound s.poly (horner f z) :=
  ⟨rfl,horner_add s h z,horner_times s h z⟩

end Ops

/-- An executable polynomial identity lifts to evaluations at *all* points
of every target ring, including points of every field extension. -/
theorem bezout3_ne_zero {D K : Type*} [CommRing K] [Nontrivial K]
    (s : Ops D) (f : D → K) (hs : Sound s f)
    (one v h qr r qa a qp p : D) (oneval : f one = 1)
    (w : s.mul v h = s.add one (s.add (s.mul qr r) (s.add (s.mul qa a) (s.mul qp p))))
    (rz : f r = 0) (az : f a = 0) (pz : f p = 0) : f h ≠ 0 := by
  intro hz
  have e := congrArg f w
  simpa only [hs.mul,hs.add,oneval,rz,az,pz,hz,mul_zero,add_zero,zero_ne_one] using e

theorem inverse_ne_zero {D K : Type*} [CommRing K] [Nontrivial K]
    (s : Ops D) (f : D → K) (hs : Sound s f)
    (one lc i qr r : D) (oneval : f one = 1)
    (w : s.mul lc i = s.add one (s.mul qr r)) (rz : f r = 0) : f lc ≠ 0 := by
  intro hz
  have e := congrArg f w
  simpa only [hs.mul,hs.add,oneval,rz,hz,zero_mul,mul_zero,add_zero,zero_ne_one] using e

end RKResearch.Certified.Graded.NativeHornerWitness
