module

public import Mathlib.Algebra.Field.Basic
import Mathlib.Tactic.LinearCombination
import Mathlib.Tactic.Ring

@[expose] public section

/-! # Literal three-stage overlap: degenerate local Volterra geometries

The outer diagonals are zero. Leading and trailing kernel values are
not normalized. The middle diagonal and both neighboring taps are
required unless the overlap is already of two-clock/one-primitive type.
-/
namespace RKResearch.Certified.Graded.ThreeStageOverlap
variable {K : Type*} [Field K]

structure Packet (K : Type*) where
  x : K
  y : K
  z : K
  d : K
  p : K
  q : K
  w : K
  f : K
  g : K
  h : K
  alpha : K
  beta : K
  gamma : K

def Packet.plain (E : Packet K) (k : Nat) : K :=
  E.alpha*E.f*E.x^k + E.beta*E.g*E.y^k + E.gamma*E.h*E.z^k

def Packet.primitive (E : Packet K) (j k : Nat) : K :=
  E.beta*E.y^k*(E.p*E.x^j*E.f + E.d*E.y^j*E.g)
    + E.gamma*E.z^k*(E.w*E.x^j*E.f + E.q*E.y^j*E.g)

/-- The exact local restriction of the two Volterra kernel equations. -/
structure KernelCut (E : Packet K) : Prop where
  front : E.f≠0
  back : E.gamma≠0
  rm : E.p*(E.y-E.x-E.d)*E.f - E.d^2*E.g=0
  lm : E.q*(E.z-E.y-E.d)*E.gamma - E.d^2*E.beta=0
  re : ((E.z-E.x)*E.w-E.q*E.p)*E.f + E.q*(E.z-E.y-E.d)*E.g=0

/-- At most two ordinary clocks, one of which supports every primitive. -/
def Packet.Geometric (E : Packet K) : Prop :=
  ∃ x eta T U S : K,
    (∀ k : Nat, E.plain k = T*x^k+U*eta^k)
    ∧ (∀ j k : Nat, E.primitive j k = S*x^(j+k))

def Packet.NoPrimitive (E : Packet K) : Prop := ∀ j k : Nat, E.primitive j k=0

theorem same_clocks (E : Packet K) (hy : E.y=E.x) (hz : E.z=E.x) :
    E.Geometric := by
  refine ⟨E.x,E.x,E.alpha*E.f+E.beta*E.g+E.gamma*E.h,0,
    E.beta*(E.p*E.f+E.d*E.g)+E.gamma*(E.w*E.f+E.q*E.g),?_,?_⟩
  · intro k
    rw [Packet.plain,hy,hz]
    ring
  · intro j k
    rw [Packet.primitive,hy,hz,pow_add]
    ring

theorem split_if_zero_middle (E : Packet K) (H : KernelCut E) (d0 : E.d=0) :
    E.NoPrimitive ∨ E.Geometric := by
  have ep : E.p*(E.y-E.x)=0 := by
    apply (mul_eq_zero.mp _).resolve_right H.front
    linear_combination H.rm + (E.p*E.f+E.d*E.g)*d0
  have eq : E.q*(E.z-E.y)=0 := by
    apply (mul_eq_zero.mp _).resolve_right H.back
    linear_combination H.lm + (E.q*E.gamma+E.d*E.beta)*d0
  have ew : (E.z-E.x)*E.w-E.q*E.p=0 := by
    apply (mul_eq_zero.mp _).resolve_right H.front
    linear_combination H.re - E.g*eq + (E.q*E.g)*d0
  by_cases hp : E.p=0
  · by_cases hq : E.q=0
    · by_cases hw : E.w=0
      · exact Or.inl (fun j k=>by rw [Packet.primitive,hp,hq,hw,d0]; ring)
      · have zx : E.z=E.x := by
          rw [hq,zero_mul,sub_zero] at ew
          exact sub_eq_zero.mp ((mul_eq_zero.mp ew).resolve_right hw)
        right
        refine ⟨E.x,E.y,E.alpha*E.f+E.gamma*E.h,E.beta*E.g,E.gamma*E.w*E.f,?_,?_⟩
        · intro k
          rw [Packet.plain,zx]
          ring
        · intro j k
          rw [Packet.primitive,hp,hq,d0,zx,pow_add]
          ring
    · have zy : E.z=E.y := sub_eq_zero.mp ((mul_eq_zero.mp eq).resolve_left hq)
      by_cases hw : E.w=0
      · right
        refine ⟨E.y,E.x,E.beta*E.g+E.gamma*E.h,E.alpha*E.f,E.gamma*E.q*E.g,?_,?_⟩
        · intro k
          rw [Packet.plain,zy]
          ring
        · intro j k
          rw [Packet.primitive,hp,hw,d0,zy,pow_add]
          ring
      · have zx : E.z=E.x := by
          rw [hp,mul_zero,sub_zero] at ew
          exact sub_eq_zero.mp ((mul_eq_zero.mp ew).resolve_right hw)
        exact Or.inr (same_clocks E (zy.symm.trans zx) zx)
  · have yx : E.y=E.x := sub_eq_zero.mp ((mul_eq_zero.mp ep).resolve_left hp)
    have hq : E.q=0 := by
      by_contra Q
      have zy : E.z=E.y := sub_eq_zero.mp ((mul_eq_zero.mp eq).resolve_left Q)
      rw [zy,yx,sub_self,zero_mul,zero_sub] at ew
      exact (mul_ne_zero Q hp) (neg_eq_zero.mp ew)
    by_cases hw : E.w=0
    · right
      refine ⟨E.x,E.z,E.alpha*E.f+E.beta*E.g,E.gamma*E.h,E.beta*E.p*E.f,?_,?_⟩
      · intro k
        rw [Packet.plain,yx]
        ring
      · intro j k
        rw [Packet.primitive,hq,d0,hw,yx,pow_add]
        ring
    · have zx : E.z=E.x := by
        rw [hq,zero_mul,sub_zero] at ew
        exact sub_eq_zero.mp ((mul_eq_zero.mp ew).resolve_right hw)
      exact Or.inr (same_clocks E yx zx)

theorem split_if_hop_missing (E : Packet K) (H : KernelCut E) (dn : E.d≠0)
    (missing : E.p=0 ∨ E.q=0) : E.NoPrimitive ∨ E.Geometric := by
  have ew (r : (E.z-E.x)*E.w*E.f=0) : (E.z-E.x)*E.w=0 :=
    (mul_eq_zero.mp r).resolve_right H.front
  rcases missing with hp|hq
  · have rg := H.rm
    rw [hp,zero_mul,zero_mul,zero_sub] at rg
    have gg : E.g=0 := (mul_eq_zero.mp (neg_eq_zero.mp rg)).resolve_left (pow_ne_zero 2 dn)
    have R := H.re
    rw [hp,gg,mul_zero,mul_zero,sub_zero,add_zero] at R
    by_cases ww : E.w=0
    · exact Or.inl (fun j k=>by rw [Packet.primitive,hp,gg,ww]; ring)
    · have zx : E.z=E.x := sub_eq_zero.mp ((mul_eq_zero.mp (ew R)).resolve_right ww)
      right
      refine ⟨E.x,E.x,E.alpha*E.f+E.gamma*E.h,0,E.gamma*E.w*E.f,?_,?_⟩
      · intro k
        rw [Packet.plain,gg,zx]
        ring
      · intro j k
        rw [Packet.primitive,hp,gg,zx,pow_add]
        ring
  · have lb := H.lm
    rw [hq,zero_mul,zero_mul,zero_sub] at lb
    have bb : E.beta=0 := (mul_eq_zero.mp (neg_eq_zero.mp lb)).resolve_left (pow_ne_zero 2 dn)
    have R := H.re
    rw [hq,zero_mul,sub_zero,zero_mul,zero_mul,add_zero] at R
    by_cases ww : E.w=0
    · exact Or.inl (fun j k=>by rw [Packet.primitive,hq,bb,ww]; ring)
    · have zx : E.z=E.x := sub_eq_zero.mp ((mul_eq_zero.mp (ew R)).resolve_right ww)
      right
      refine ⟨E.x,E.x,E.alpha*E.f+E.gamma*E.h,0,E.gamma*E.w*E.f,?_,?_⟩
      · intro k
        rw [Packet.plain,bb,zx]
        ring
      · intro j k
        rw [Packet.primitive,hq,bb,zx,pow_add]
        ring

/-- A same-clock first pair either makes all clocks equal or makes every
primitive read vanish; the kernel identities use the true middle diagonal. -/
theorem split_if_first_repeat (E : Packet K) (H : KernelCut E) (dn : E.d≠0)
    (yx : E.y=E.x) : E.NoPrimitive ∨ E.Geometric := by
  by_cases zx : E.z=E.x
  · exact Or.inr (same_clocks E yx zx)
  · have r0 := H.rm
    rw [yx] at r0
    have z0 : E.d*(E.p*E.f+E.d*E.g)=0 := by linear_combination -r0
    have z1 := (mul_eq_zero.mp z0).resolve_left dn
    have r1 := H.re
    rw [yx] at r1
    have z2 : (E.z-E.x)*(E.w*E.f+E.q*E.g)=0 := by linear_combination r1+E.q*z1
    have z3 := (mul_eq_zero.mp z2).resolve_left (sub_ne_zero.mpr zx)
    left
    intro j k
    rw [Packet.primitive,yx]
    linear_combination (E.beta*E.x^k*E.x^j)*z1+(E.gamma*E.z^k*E.x^j)*z3

theorem split_if_last_repeat (E : Packet K) (H : KernelCut E) (dn : E.d≠0)
    (zy : E.z=E.y) : E.NoPrimitive ∨ E.Geometric := by
  by_cases yx : E.y=E.x
  · exact Or.inr (same_clocks E yx (zy.trans yx))
  · have r0 := H.lm
    rw [zy] at r0
    have z0 : E.d*(E.d*E.beta+E.q*E.gamma)=0 := by linear_combination -r0
    have z1 := (mul_eq_zero.mp z0).resolve_left dn
    have r1 := H.re
    rw [zy] at r1
    have z2 : (E.y-E.x)*(E.d*E.w-E.q*E.p)*E.f=0 := by
      linear_combination E.d*r1-E.q*H.rm
    have z3 := (mul_eq_zero.mp ((mul_eq_zero.mp z2).resolve_right H.front)).resolve_left
      (sub_ne_zero.mpr yx)
    have z4 : E.d*(E.beta*E.p+E.gamma*E.w)=0 := by
      linear_combination E.p*z1+E.gamma*z3
    have z5 := (mul_eq_zero.mp z4).resolve_left dn
    left
    intro j k
    rw [Packet.primitive,zy]
    linear_combination (E.y^k*E.y^j*E.g)*z1+(E.y^k*E.x^j*E.f)*z5

/-- A live two-hop return to the first clock forces the middle clock
to coincide as well, by the literal Volterra Schur relation. -/
theorem middle_eq_of_outer_repeat (E : Packet K) (H : KernelCut E)
    (pn : E.p≠0) (qn : E.q≠0) (zx : E.z=E.x) : E.y=E.x := by
  have r1 := H.re
  rw [zx] at r1
  have z : E.p*E.q*(E.y-E.x)^2*E.f=0 := by
    linear_combination -E.d^2*r1-(E.q*(E.x-E.y-E.d))*H.rm
  have q := (mul_eq_zero.mp ((mul_eq_zero.mp z).resolve_right H.front)).resolve_left (mul_ne_zero pn qn)
  exact sub_eq_zero.mp (sq_eq_zero_iff.mp q)

end RKResearch.Certified.Graded.ThreeStageOverlap
