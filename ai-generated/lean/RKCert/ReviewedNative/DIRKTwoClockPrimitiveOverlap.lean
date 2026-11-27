module

public import RKCert.ReviewedNative.DIRKCrossedCubicPivot
public import Mathlib.Algebra.Field.Basic
import Mathlib.Tactic.LinearCombination
import Mathlib.Tactic.Ring

@[expose] public section

/-! # Short crossed-cubic overlap: one primitive clock and at most two plain clocks
The elementary profile pair cannot have these exact paid reads over
any field. The proof detects the first repeated-root obstruction
without imposing a nodal order or relying on sign patterns.
-/
namespace RKResearch.Certified.Graded.TwoClockPrimitive
open CrossedCubicPivot

variable {K : Type*} [Field K]

def plain (a b d : K) (M : Nat → K) (k : Nat) :=
  a*M (k+1)+b*M (k+2)+d*M (k+3)

/-- Six cleared single-primitive reads on one clock. The denominators
are paid; no assumption on the two weights in the plain reads is used. -/
structure Geometric (a b d : K) (M : Nat → K) (S x : K) : Prop where
  p00 : 6*(a*M 2)+4*(b*M 3)+3*(d*M 4)=12*S
  p01 : 6*(a*M 3)+4*(b*M 4)+3*(d*M 5)=12*S*x
  p10 : 20*(a*M 3)+15*(b*M 4)+12*(d*M 5)=60*S*x
  p02 : 6*(a*M 4)+4*(b*M 5)+3*(d*M 6)=12*S*x^2
  p11 : 20*(a*M 4)+15*(b*M 5)+12*(d*M 6)=60*S*x^2
  p20 : 15*(a*M 4)+12*(b*M 5)+10*(d*M 6)=60*S*x^2

private theorem top_three {a b d : K} {M : Nat → K} {S x : K}
    (E : Geometric a b d M S x) :
    a*M 4=12*S*x^2 ∧ b*M 5= -60*S*x^2 ∧ d*M 6=60*S*x^2 := by
  constructor
  · linear_combination 6*E.p02 - 4*E.p11 + 3*E.p20
  constructor
  · linear_combination -20*E.p02 + 15*E.p11 - 12*E.p20
  · linear_combination 15*E.p02 - 12*E.p11 + 10*E.p20

private theorem paid_nz (mu : Nat → K) (pay : ∀ n, n<10 → ((n+1:Nat):K)*mu n=1)
    (n : Nat) (hn : n<10) : ((n+1:Nat):K)≠0 :=
  (IsUnit.of_mul_eq_one _ (pay n hn)).ne_zero

private theorem detect_three (mu : Nat → K) (pay : ∀ n, n<10 → ((n+1:Nat):K)*mu n=1)
    (h l m : K) {e : Nat} (he : 2≤e ∧ e≤4)
    (p0 : moment mu h l m e=0) (p1 : moment mu h l m (e+1)=0)
    (p2 : moment mu h l m (e+2)=0) : h=0 ∧ l=0 ∧ m=0 :=
  endpoint_moments_detect mu h l m e he
    (fun t ht => by rw [Lean.Grind.Semiring.ofNat_eq_natCast]; exact pay t ht) p0 p1 p2

private def beta4 (mu : Nat→K) (a b c d : K) (n : Nat) : K :=
  a*(mu n-mu (n+1))+b*(mu (n+1)-mu (n+2))
    +c*(mu (n+2)-mu (n+3))+d*(mu (n+3)-mu (n+4))

private theorem detect_beta_four (mu : Nat→K) (pay : ∀ n, n<10 → ((n+1:Nat):K)*mu n=1)
    (a b c d : K) (h2 : beta4 mu a b c d 2=0) (h3 : beta4 mu a b c d 3=0)
    (h4 : beta4 mu a b c d 4=0) (h5 : beta4 mu a b c d 5=0) :
    a=0 ∧ b=0 ∧ c=0 ∧ d=0 := by
  let g (n : Nat) := mu n-mu (n+1)
  have p2 : (12:K)*g 2=1 := by
    have m : (3:K)*mu 2=1 := pay 2 (by decide)
    have n : (4:K)*mu 3=1 := pay 3 (by decide)
    dsimp only [g]
    linear_combination 4*m - 3*n
  have p3 : (20:K)*g 3=1 := by
    have m : (4:K)*mu 3=1 := pay 3 (by decide)
    have n : (5:K)*mu 4=1 := pay 4 (by decide)
    dsimp only [g]
    linear_combination 5*m - 4*n
  have p4 : (30:K)*g 4=1 := by
    have m : (5:K)*mu 4=1 := pay 4 (by decide)
    have n : (6:K)*mu 5=1 := pay 5 (by decide)
    dsimp only [g]
    linear_combination 6*m - 5*n
  have p5 : (42:K)*g 5=1 := by
    have m : (6:K)*mu 5=1 := pay 5 (by decide)
    have n : (7:K)*mu 6=1 := pay 6 (by decide)
    dsimp only [g]
    linear_combination 7*m - 6*n
  have p6 : (56:K)*g 6=1 := by
    have m : (7:K)*mu 6=1 := pay 6 (by decide)
    have n : (8:K)*mu 7=1 := pay 7 (by decide)
    dsimp only [g]
    linear_combination 8*m - 7*n
  have p7 : (72:K)*g 7=1 := by
    have m : (8:K)*mu 7=1 := pay 7 (by decide)
    have n : (9:K)*mu 8=1 := pay 8 (by decide)
    dsimp only [g]
    linear_combination 9*m - 8*n
  have p8 : (90:K)*g 8=1 := by
    have m : (9:K)*mu 8=1 := pay 8 (by decide)
    have n : (10:K)*mu 9=1 := pay 9 (by decide)
    dsimp only [g]
    linear_combination 10*m - 9*n
  have id : (-12600:K)*beta4 mu a b c d 2+88200*beta4 mu a b c d 3
      -176400*beta4 mu a b c d 4+105840*beta4 mu a b c d 5=d := by
    calc
      _ = a*((-1050)*(12*g 2) + (4410)*(20*g 3) + (-5880)*(30*g 4) + (2520)*(42*g 5))
        + b*((-630)*(20*g 3) + (2940)*(30*g 4) + (-4200)*(42*g 5) + (1890)*(56*g 6))
        + c*((-420)*(30*g 4) + (2100)*(42*g 5) + (-3150)*(56*g 6) + (1470)*(72*g 7))
        + d*((-300)*(42*g 5) + (1575)*(56*g 6) + (-2450)*(72*g 7) + (1176)*(90*g 8)) := by dsimp only [g,beta4]; ring
      _ = d := by rw [p2,p3,p4,p5,p6,p7,p8]; ring
  rw [h2,h3,h4,h5] at id
  have dz : d=0 := by linear_combination -id
  rw [dz] at h2 h3 h4
  have zz := detect_three mu pay a b c (e:=2) (by decide)
    (by simpa only [beta4,moment,zero_mul,add_zero] using h2)
    (by simpa only [beta4,moment,zero_mul,add_zero] using h3)
    (by simpa only [beta4,moment,zero_mul,add_zero] using h4)
  exact ⟨zz.1,zz.2.1,zz.2.2,dz⟩

private theorem shifted_moment (mu : Nat→K) (h l m x : K) (n : Nat) :
    beta4 mu (-x*h) (h-x*l) (l-x*m) m n =
      moment mu h l m (n+1) - x*moment mu h l m n := by
  simp only [beta4,moment,Nat.add_assoc]
  ring

private theorem zero_clock (mu : Nat→K) (pay : ∀ n, n<10 → ((n+1:Nat):K)*mu n=1)
    (a b d h l m S : K) (live : a≠0 ∨ b≠0 ∨ d≠0)
    (E : Geometric a b d (moment mu h l m) S 0)
    (eta T U : K) (read : ∀ k, k≤3 →
      plain a b d (moment mu h l m) k=T*(0:K)^k+U*eta^k) :
    h=0 ∧ l=0 ∧ m=0 := by
  let M := moment mu h l m
  have z := top_three E
  change a*M 4=12*S*(0:K)^2 ∧ b*M 5= -60*S*(0:K)^2 ∧ d*M 6=60*S*(0:K)^2 at z
  simp only [zero_pow (by decide : (2:Nat)≠0),mul_zero] at z
  have p3 : plain a b d M 3=0 := by unfold plain; rw [z.1,z.2.1,z.2.2]; ring
  have o : U*eta=0 := by
    have H := read 3 (by decide)
    change plain a b d M 3=T*(0:K)^3+U*eta^3 at H
    rw [p3,zero_pow (by decide : (3:Nat)≠0),mul_zero,zero_add] at H
    rcases mul_eq_zero.mp H.symm with u|t
    · rw [u,zero_mul]
    · rw [show eta=0 from eq_zero_of_pow_eq_zero t, mul_zero]
  have p1 : plain a b d M 1=0 := by
    have H := read 1 (by decide)
    linear_combination H + o
  have p2 : plain a b d M 2=0 := by
    have H := read 2 (by decide)
    linear_combination H + eta*o
  have w1 : a*M 3=0 := by unfold plain at p2; linear_combination 3*E.p01 - E.p10 + 3*p2
  have w2 : b*M 4=0 := by unfold plain at p2; linear_combination -8*E.p01 + 3*E.p10 - 12*p2
  have w3 : d*M 5=0 := by unfold plain at p2; linear_combination 5*E.p01 - 2*E.p10 + 10*p2
  have Close (n : Nat) (hn : 2≤n ∧ n≤4)
      (m0 : M n=0) (m1 : M (n+1)=0) (m2 : M (n+2)=0) : h=0 ∧ l=0 ∧ m=0 :=
    detect_three mu pay h l m hn m0 m1 m2
  have kill {u v : K} (un : u≠0) (z : u*v=0) : v=0 :=
    (mul_eq_zero.mp z).resolve_left un
  by_cases ha : a=0
  · by_cases hb : b=0
    · have hd : d≠0 := (live.resolve_left (not_not_intro ha)).resolve_left (not_not_intro hb)
      have t : d*M 4=0 := by unfold plain at p1; rw [ha,hb] at p1; linear_combination p1
      exact Close 4 (by decide) (kill hd t) (kill hd w3) (kill hd z.2.2)
    · by_cases hd : d=0
      · have t : b*M 3=0 := by unfold plain at p1; rw [ha,hd] at p1; linear_combination p1
        exact Close 3 (by decide) (kill hb t) (kill hb w2) (kill hb z.2.1)
      · exact Close 4 (by decide) (kill hb w2) (kill hb z.2.1) (kill hd z.2.2)
  · by_cases hb : b=0
    · by_cases hd : d=0
      · have t : a*M 2=0 := by unfold plain at p1; rw [hb,hd] at p1; linear_combination p1
        exact Close 2 (by decide) (kill ha t) (kill ha w1) (kill ha z.1)
      · exact Close 3 (by decide) (kill ha w1) (kill ha z.1) (kill hd w3)
    · exact Close 3 (by decide) (kill ha w1) (kill ha z.1) (kill hb z.2.1)

private theorem nonzero_clock (mu : Nat→K) (pay : ∀ n, n<10 → ((n+1:Nat):K)*mu n=1)
    (a b d h l m S x : K) (Sn : S≠0) (xn : x≠0)
    (E : Geometric a b d (moment mu h l m) S x)
    (eta T U : K) (read : ∀ k, k≤3 →
      plain a b d (moment mu h l m) k=T*x^k+U*eta^k) :
    h=0 ∧ l=0 ∧ m=0 := by
  let M := moment mu h l m
  let F := plain a b d M
  let A1 := a*M 3
  let B1 := b*M 4
  let C1 := d*M 5
  let B0 := b*M 3
  let C0 := d*M 4
  have z := top_three E
  change a*M 4=12*S*x^2 ∧ b*M 5= -60*S*x^2 ∧ d*M 6=60*S*x^2 at z
  have n2 : (2:K)≠0 := paid_nz mu pay 1 (by decide)
  have n3 : (3:K)≠0 := paid_nz mu pay 2 (by decide)
  have n5 : (5:K)≠0 := paid_nz mu pay 4 (by decide)
  have n6 : (6:K)≠0 := paid_nz mu pay 5 (by decide)
  have n10 : (10:K)≠0 := paid_nz mu pay 9 (by decide)
  have n12 : (12:K)≠0 := by
    rw [show (12:K)=2*6 by ring]
    exact mul_ne_zero n2 n6
  have n60 : (60:K)≠0 := by
    rw [show (60:K)=6*10 by ring]
    exact mul_ne_zero n6 n10
  have liveA : a≠0 := by
    intro ha
    rw [ha,zero_mul] at z
    exact (mul_ne_zero (mul_ne_zero n12 Sn) (pow_ne_zero 2 xn)) z.1.symm
  have liveB : b≠0 := by
    intro hb
    rw [hb,zero_mul] at z
    exact (mul_ne_zero (mul_ne_zero (neg_ne_zero.mpr n60) Sn) (pow_ne_zero 2 xn)) z.2.1.symm
  have liveD : d≠0 := by
    intro hd
    rw [hd,zero_mul] at z
    exact (mul_ne_zero (mul_ne_zero n60 Sn) (pow_ne_zero 2 xn)) z.2.2.symm
  have pair1 : 10*A1 - 3*C1 +60*S*x=0 := by
    dsimp only [A1,C1,M]
    linear_combination 15*E.p01 - 4*E.p10
  have pair2 : 5*B1+6*C1-60*S*x=0 := by
    dsimp only [B1,C1,M]
    linear_combination -10*E.p01 + 3*E.p10
  have pure0 : 6*F 1-12*S-2*B0-3*C0=0 := by
    dsimp only [F,plain,B0,C0,M]
    linear_combination E.p00
  have p1 : A1*B1 - 12*S*x^2*B0 =0 := by
    dsimp only [A1,B1,B0]
    linear_combination (b*M 3)*z.1
  have p2 : B1*C1 + 60*S*x^2*C0=0 := by
    dsimp only [B1,C1,C0]
    linear_combination (d*M 4)*z.2.1
  have comm : (60*S*x)*(6*x*F 1-12*S*x+B1)=0 := by
    linear_combination (60*S*x^2)*pure0 - 10*p1 +3*p2 + B1*pair1
  have l1 : 6*x*F 1-12*S*x+B1=0 :=
    (mul_eq_zero.mp comm).resolve_left (mul_ne_zero (mul_ne_zero n60 Sn) xn)
  have l1' : 5*x*F 1=C1 := by
    have v : (6:K)*(5*x*F 1-C1)=0 := by linear_combination 5*l1-pair2
    exact sub_eq_zero.mp ((mul_eq_zero.mp v).resolve_left n6)
  have l2 : 10*F 2-C1-60*S*x=0 := by
    change 10*(A1+B1+C1)-C1-60*S*x=0
    linear_combination pair1+2*pair2
  have l3 : F 3=12*S*x^2 := by
    change a*M 4 + b*M 5+d*M 6=12*S*x^2
    linear_combination z.1+z.2.1+z.2.2
  have lstep : F 3-2*x*F 2+x^2*F 1=0 := by
    have e : (5:K)*(F 3-2*x*F 2+x^2*F 1)=0 := by
      linear_combination 5*l3-x*l2+x*l1'
    exact (mul_eq_zero.mp e).resolve_left n5
  have spec : (U*eta)*(eta-x)^2=0 := by
    change plain a b d M 3-2*x*plain a b d M 2+x^2*plain a b d M 1=0 at lstep
    rw [read 3 (by decide),read 2 (by decide),read 1 (by decide)] at lstep
    linear_combination lstep
  have spec1 : (U*eta)*(eta-x)=0 := by
    rcases mul_eq_zero.mp spec with z|z
    · rw [z,zero_mul]
    · rw [sq_eq_zero_iff.mp z,mul_zero]
  have paidStep : F 2-x*F 1=0 := by
    change plain a b d M 2-x*plain a b d M 1=0
    rw [read 2 (by decide),read 1 (by decide)]
    linear_combination spec1
  have ww : C1=60*S*x := by linear_combination -10*paidStep+l2-2*l1'
  have aa : A1=12*S*x := by
    have t : (10:K)*(A1-12*S*x)=0 := by linear_combination pair1+3*ww
    exact sub_eq_zero.mp ((mul_eq_zero.mp t).resolve_left n10)
  have bb : B1= -60*S*x := by
    have t : (5:K)*(B1+60*S*x)=0 := by linear_combination pair2-6*ww
    have e := (mul_eq_zero.mp t).resolve_left n5; linear_combination e
  have r6 : M 6 - x*M 5=0 := by
    have q : d*(M 6-x*M 5)=0 := by dsimp only [C1] at ww; linear_combination z.2.2-x*ww
    exact (mul_eq_zero.mp q).resolve_left liveD
  have r5 : M 5 - x*M 4=0 := by
    have q : b*(M 5-x*M 4)=0 := by dsimp only [B1] at bb; linear_combination z.2.1-x*bb
    exact (mul_eq_zero.mp q).resolve_left liveB
  have r4 : M 4 - x*M 3=0 := by
    have q : a*(M 4-x*M 3)=0 := by dsimp only [A1] at aa; linear_combination z.1-x*aa
    exact (mul_eq_zero.mp q).resolve_left liveA
  have hB : b*M 3= -60*S := by
    have q : x*(b*M 3+60*S)=0 := by
      dsimp only [B1] at bb
      linear_combination bb-b*r4
    have e := (mul_eq_zero.mp q).resolve_left xn; linear_combination e
  have hD : d*M 4=60*S := by
    have q : x*(d*M 4-60*S)=0 := by
      dsimp only [C1] at ww
      linear_combination ww-d*r5
    exact sub_eq_zero.mp ((mul_eq_zero.mp q).resolve_left xn)
  have r3 : M 3 - x*M 2=0 := by
    have y : (6:K)*(a*M 2-12*S)=0 := by linear_combination E.p00-4*hB-3*hD
    have y := (mul_eq_zero.mp y).resolve_left n6
    have q : a*(M 3-x*M 2)=0 := by
      dsimp only [A1] at aa
      linear_combination aa-x*y
    exact (mul_eq_zero.mp q).resolve_left liveA
  have close (k : Nat) (r : M (k+1)-x*M k=0) :
      beta4 mu (-x*h) (h-x*l) (l-x*m) m k=0 := (shifted_moment mu h l m x k).trans r
  have ans := detect_beta_four mu pay (-x*h) (h-x*l) (l-x*m) m
    (close 2 r3) (close 3 r4) (close 4 r5) (close 5 r6)
  have zm := ans.2.2.2
  have zl : l=0 := by linear_combination ans.2.2.1 + x*zm
  have zh : h=0 := by linear_combination ans.2.1 + x*zl
  exact ⟨zh,zl,zm⟩

/-- One primitive clock and at most two ordinary clocks (one being the
primitive clock) cannot support two nonzero endpoint-factored cubics. -/
theorem no_two_clock_geometric (mu : Nat→K) (pay : ∀ n, n<10 → ((n+1:Nat):K)*mu n=1)
    (a b d h l m S x eta T U : K) (Sn : S≠0) (live : a≠0 ∨ b≠0 ∨ d≠0)
    (E : Geometric a b d (moment mu h l m) S x)
    (read : ∀ k, k≤3 → plain a b d (moment mu h l m) k = T*x^k+U*eta^k) :
    h=0 ∧ l=0 ∧ m=0 := by
  by_cases xz : x=0
  · subst x
    exact zero_clock mu pay a b d h l m S live E eta T U read
  · exact nonzero_clock mu pay a b d h l m S x Sn xz E eta T U read

end RKResearch.Certified.Graded.TwoClockPrimitive
