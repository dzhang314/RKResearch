module

public import RKCert.ReviewedNative.NativeHornerWitness

@[expose] public section

/-! # Definitional checkpoints for polynomial arithmetic

Each equation makes exactly *one* constructor step of the already verified
Horner implementation. The kernel checks recursive results against named,
closed literals; it never has to evaluate the complete nested product. -/
namespace RKResearch.Certified.Graded.NativeHornerCheckpoints
open NativeHornerWitness
variable {D : Type*} [DecidableEq D] (s : Ops D)

theorem add_cons {a b v : D} {as bs vs answer : List D}
    (c : s.add a b=v) (d : s.ladd as bs=vs) (finish : s.cons v vs=answer) :
    s.ladd (a::as) (b::bs)=answer := by
  change s.cons (s.add a b) (s.ladd as bs)=answer
  rw [c,d,finish]

theorem scale_cons {a b v : D} {bs vs answer : List D}
    (c : s.mul a b=v) (d : s.scale a bs=vs) (finish : s.cons v vs=answer) :
    s.scale a (b::bs)=answer := by
  change s.cons (s.mul a b) (s.scale a bs)=answer
  rw [c,d,finish]

theorem mul_cons {a : D} {as b v w shift answer : List D}
    (tail : s.times as b=v) (scaled : s.scale a b=w)
    (shifted : s.cons s.zero v=shift) (finish : s.ladd w shift=answer) :
    s.times (a::as) b=answer := by
  change s.ladd (s.scale a b) (s.cons s.zero (s.times as b))=answer
  rw [tail,scaled,shifted,finish]

end RKResearch.Certified.Graded.NativeHornerCheckpoints
