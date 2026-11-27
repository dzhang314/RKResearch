module

public import Init.Grind

@[expose] public section

/-! # The scalar obstruction to overlapping zero-diagonal debut cuts

A reverse cubic profile vanishing at the reflected origin has form
`Q(x) = (1-x)*(h+l*x+m*x²)`. If the forward nonconstant cubic seed
has no physical room before the reverse pivot, their genuine mixed
primitive probes vanish. This file proves that no two nonzero scalar
profiles can have those paid zero probes. It also applies when `Q`
is a cubic nodal mask containing the physical endpoint clock 1.
-/
namespace RKResearch.Certified.Graded.CrossedCubicPivot
open Lean.Grind

variable {K : Type} [CommRing K]

/-- The signed moments of the reverse cubic profile as a density in the
original clock variable. -/
def moment (mu : Nat → K) (h l m : K) (t : Nat) : K :=
  h*(mu t-mu (t+1)) + l*(mu (t+1)-mu (t+2)) + m*(mu (t+2)-mu (t+3))

/-- Clearing the genuine mixed primitive moments at total `t=j+k`,
for `j=0,1,2`. The budget needed is exactly `t≤2`. -/
structure Tests (a b c : K) (M : Nat → K) : Prop where
  j0 : ∀ t, t ≤ 2 →
    6*(a*M (t+2)) + 4*(b*M (t+3)) + 3*(c*M (t+4)) = 0
  j1 : ∀ t, 1 ≤ t → t ≤ 2 →
    20*(a*M (t+2)) + 15*(b*M (t+3)) + 12*(c*M (t+4)) = 0
  j2 : 15*(a*M 4) + 12*(b*M 5) + 10*(c*M 6) = 0

theorem top (a b c : K) (M : Nat → K) (T : Tests a b c M) :
    a*M 4 = 0 ∧ b*M 5 = 0 ∧ c*M 6 = 0 := by
  let x := a*M 4
  let y := b*M 5
  let z := c*M 6
  let r0 := 6*x + 4*y + 3*z
  let r1 := 20*x + 15*y + 12*z
  let r2 := 15*x + 12*y + 10*z
  have h0 : r0=0 := T.j0 2 (by decide)
  have h1 : r1=0 := T.j1 2 (by decide) (by decide)
  have h2 : r2=0 := T.j2
  change x=0 ∧ y=0 ∧ z=0
  have hx : x = 6*r0-4*r1+3*r2 := by dsimp only [r0,r1,r2]; grind only
  have hy : y = -20*r0+15*r1-12*r2 := by dsimp only [r0,r1,r2]; grind only
  have hz : z = 15*r0-12*r1+10*r2 := by dsimp only [r0,r1,r2]; grind only
  rw [h0,h1,h2] at hx hy hz
  grind

/-- One Cauchy-window inversion multiplies cleared rows and avoids
reasoning about divisions in small or positive characteristic. -/
private theorem inverseStep (G : Nat → K) (h l m : K)
    (e : Nat) (v0 v1 v2 L u0 u1 u2 : K)
    (g0 g1 g2 g3 g4 : K)
    (p0 : g0*G e=1) (p1 : g1*G (e+1)=1) (p2 : g2*G (e+2)=1)
    (p3 : g3*G (e+3)=1) (p4 : g4*G (e+4)=1)
    (q0 : v0 = u0*g0) (q1 : v1=u1*g1) (q2 : v2=u2*g2)
    (r0 r1 r2 s0 s1 s2 : K)
    (q3 : v0=r0*g1) (q4 : v1=r1*g2) (q5 : v2=r2*g3)
    (q6 : v0=s0*g2) (q7 : v1=s1*g3) (q8 : v2=s2*g4)
    (w0 : h*G e+l*G (e+1)+m*G (e+2)=0)
    (w1 : h*G (e+1)+l*G (e+2)+m*G (e+3)=0)
    (w2 : h*G (e+2)+l*G (e+3)+m*G (e+4)=0)
    (res : L = h*(u0+u1+u2) + l*(r0+r1+r2) + m*(s0+s1+s2)) : L=0 := by
  calc
    L = h*(u0*(g0*G e)+u1*(g1*G (e+1))+u2*(g2*G (e+2)))
      + l*(r0*(g1*G (e+1))+r1*(g2*G (e+2))+r2*(g3*G (e+3)))
      + m*(s0*(g2*G (e+2))+s1*(g3*G (e+3))+s2*(g4*G (e+4))) := by
        rw [p0,p1,p2,p3,p4,res]; grind only
    _ = (u0*g0)*(h*G e) + (u1*g1)*(h*G (e+1)) + (u2*g2)*(h*G (e+2))
      + (r0*g1)*(l*G (e+1)) + (r1*g2)*(l*G (e+2)) + (r2*g3)*(l*G (e+3))
      + (s0*g2)*(m*G (e+2)) + (s1*g3)*(m*G (e+3)) + (s2*g4)*(m*G (e+4)) := by grind only
    _ = v0*(h*G e+l*G (e+1)+m*G (e+2))
      + v1*(h*G (e+1)+l*G (e+2)+m*G (e+3))
      + v2*(h*G (e+2)+l*G (e+3)+m*G (e+4)) := by
        rw [←q0,←q1,←q2,←q3,←q4,←q5,←q6,←q7,←q8]; grind only
    _ = 0 := by rw [w0,w1,w2]; grind only

/-- Detect the endpoint-factored cubic from three consecutive paid moments.
The only divided integers in the inverse tables use primes paid at order ten. -/
theorem endpoint_moments_detect (mu : Nat → K) (h l m : K) (e : Nat) (he : 2 ≤ e ∧ e ≤ 4)
    (pay : ∀ t, t < 10 → (OfNat.ofNat (α := K) (t+1)) * mu t = 1)
    (w0 : moment mu h l m e=0) (w1 : moment mu h l m (e+1)=0)
    (w2 : moment mu h l m (e+2)=0) :
    h=0 ∧ l=0 ∧ m=0 := by
  let G : Nat → K := fun t => mu t-mu (t+1)
  change h*G e+l*G (e+1)+m*G (e+2)=0 at w0
  change h*G (e+1)+l*G (e+2)+m*G (e+3)=0 at w1
  change h*G (e+2)+l*G (e+3)+m*G (e+4)=0 at w2
  have p2 : (12:K)*G 2=1 := by
    have i : (3:K)*mu 2=1 := pay 2 (by decide)
    have n : (4:K)*mu 3=1 := pay 3 (by decide)
    calc
      _ = 4*(3*mu 2)-3*(4*mu 3) := by dsimp only [G]; grind only
      _ = 1 := by rw [i,n]; grind only
  have p3 : (20:K)*G 3=1 := by
    have i : (4:K)*mu 3=1 := pay 3 (by decide)
    have n : (5:K)*mu 4=1 := pay 4 (by decide)
    calc
      _ = 5*(4*mu 3)-4*(5*mu 4) := by dsimp only [G]; grind only
      _ = 1 := by rw [i,n]; grind only
  have p4 : (30:K)*G 4=1 := by
    have i : (5:K)*mu 4=1 := pay 4 (by decide)
    have n : (6:K)*mu 5=1 := pay 5 (by decide)
    calc
      _ = 6*(5*mu 4)-5*(6*mu 5) := by dsimp only [G]; grind only
      _ = 1 := by rw [i,n]; grind only
  have p5 : (42:K)*G 5=1 := by
    have i : (6:K)*mu 5=1 := pay 5 (by decide)
    have n : (7:K)*mu 6=1 := pay 6 (by decide)
    calc
      _ = 7*(6*mu 5)-6*(7*mu 6) := by dsimp only [G]; grind only
      _ = 1 := by rw [i,n]; grind only
  have p6 : (56:K)*G 6=1 := by
    have i : (7:K)*mu 6=1 := pay 6 (by decide)
    have n : (8:K)*mu 7=1 := pay 7 (by decide)
    calc
      _ = 8*(7*mu 6)-7*(8*mu 7) := by dsimp only [G]; grind only
      _ = 1 := by rw [i,n]; grind only
  have p7 : (72:K)*G 7=1 := by
    have i : (8:K)*mu 7=1 := pay 7 (by decide)
    have n : (9:K)*mu 8=1 := pay 8 (by decide)
    calc
      _ = 9*(8*mu 7)-8*(9*mu 8) := by dsimp only [G]; grind only
      _ = 1 := by rw [i,n]; grind only
  have p8 : (90:K)*G 8=1 := by
    have i : (9:K)*mu 8=1 := pay 8 (by decide)
    have n : (10:K)*mu 9=1 := pay 9 (by decide)
    calc
      _ = 10*(9*mu 8)-9*(10*mu 9) := by dsimp only [G]; grind only
      _ = 1 := by rw [i,n]; grind only
  have cases : e=2 ∨ e=3 ∨ e=4 := by omega
  rcases cases with rfl | rfl | rfl
  · have zh : h=0 := by
      exact inverseStep G h l m 2 600 (-2100) 1680 _ 50 (-105) 56
        12 20 30 42 56 p2 p3 p4 p5 p6
        (by grind only) (by grind only) (by grind only)
        30 (-70) 40 20 (-50) 30
        (by grind only) (by grind only) (by grind only)
        (by grind only) (by grind only) (by grind only)
        w0 w1 w2 (by grind only)
    have zl : l=0 := by
      exact inverseStep G h l m 2 (-2100) 7980 (-6720) _ (-175) 399 (-224)
        12 20 30 42 56 p2 p3 p4 p5 p6
        (by grind only) (by grind only) (by grind only)
        (-105) 266 (-160) (-70) 190 (-120)
        (by grind only) (by grind only) (by grind only)
        (by grind only) (by grind only) (by grind only)
        w0 w1 w2 (by grind only)
    have zm : m=0 := by
      exact inverseStep G h l m 2 1680 (-6720) 5880 _ 140 (-336) 196
        12 20 30 42 56 p2 p3 p4 p5 p6
        (by grind only) (by grind only) (by grind only)
        84 (-224) 140 56 (-160) 105
        (by grind only) (by grind only) (by grind only)
        (by grind only) (by grind only) (by grind only)
        w0 w1 w2 (by grind only)
    exact ⟨zh,zl,zm⟩
  · have zh : h=0 := by
      exact inverseStep G h l m 3 2100 (-6720) 5040 _ 105 (-224) 120
        20 30 42 56 72 p3 p4 p5 p6 p7
        (by grind only) (by grind only) (by grind only)
        70 (-160) 90 50 (-120) 70
        (by grind only) (by grind only) (by grind only)
        (by grind only) (by grind only) (by grind only)
        w0 w1 w2 (by grind only)
    have zl : l=0 := by
      exact inverseStep G h l m 3 (-6720) 22680 (-17640) _ (-336) 756 (-420)
        20 30 42 56 72 p3 p4 p5 p6 p7
        (by grind only) (by grind only) (by grind only)
        (-224) 540 (-315) (-160) 405 (-245)
        (by grind only) (by grind only) (by grind only)
        (by grind only) (by grind only) (by grind only)
        w0 w1 w2 (by grind only)
    have zm : m=0 := by
      exact inverseStep G h l m 3 5040 (-17640) 14112 _ 252 (-588) 336
        20 30 42 56 72 p3 p4 p5 p6 p7
        (by grind only) (by grind only) (by grind only)
        168 (-420) 252 120 (-315) 196
        (by grind only) (by grind only) (by grind only)
        (by grind only) (by grind only) (by grind only)
        w0 w1 w2 (by grind only)
    exact ⟨zh,zl,zm⟩
  · have zh : h=0 := by
      exact inverseStep G h l m 4 5880 (-17640) 12600 _ 196 (-420) 225
        30 42 56 72 90 p4 p5 p6 p7 p8
        (by grind only) (by grind only) (by grind only)
        140 (-315) 175 105 (-245) 140
        (by grind only) (by grind only) (by grind only)
        (by grind only) (by grind only) (by grind only)
        w0 w1 w2 (by grind only)
    have zl : l=0 := by
      exact inverseStep G h l m 4 (-17640) 54936 (-40320) _ (-588) 1308 (-720)
        30 42 56 72 90 p4 p5 p6 p7 p8
        (by grind only) (by grind only) (by grind only)
        (-420) 981 (-560) (-315) 763 (-448)
        (by grind only) (by grind only) (by grind only)
        (by grind only) (by grind only) (by grind only)
        w0 w1 w2 (by grind only)
    have zm : m=0 := by
      exact inverseStep G h l m 4 12600 (-40320) 30240 _ 420 (-960) 540
        30 42 56 72 90 p4 p5 p6 p7 p8
        (by grind only) (by grind only) (by grind only)
        300 (-720) 420 225 (-560) 336
        (by grind only) (by grind only) (by grind only)
        (by grind only) (by grind only) (by grind only)
        w0 w1 w2 (by grind only)
    exact ⟨zh,zl,zm⟩

end RKResearch.Certified.Graded.CrossedCubicPivot

namespace RKResearch.Certified.Graded.CrossedCubicPivot
open Lean.Grind
variable {K : Type} [Field K]

private theorem cancel {x y : K} (hx : x ≠ 0) (h : x*y=0) : y=0 :=
  (Field.of_mul_eq_zero h).resolve_left hx

/-- A nonzero origin-factored cubic cannot have all its paid primitive
tests vanish against a nonzero endpoint-factored cubic. -/
theorem no_crossed (mu : Nat → K)
    (pay : ∀ t, t < 10 → (OfNat.ofNat (α := K) (t+1))*mu t=1)
    (a b c h l m : K) (live : a≠0 ∨ b≠0 ∨ c≠0)
    (T : Tests a b c (moment mu h l m)) : h=0 ∧ l=0 ∧ m=0 := by
  let M := moment mu h l m
  have close (e : Nat) (he : 2 ≤ e ∧ e ≤ 4)
      (u : M e=0) (v : M (e+1)=0) (w : M (e+2)=0) : h=0 ∧ l=0 ∧ m=0 :=
    endpoint_moments_detect mu h l m e he pay u v w
  have h3 : (3:K) ≠ 0 := by
    have hp : (3:K)*mu 2=1 := pay 2 (by decide)
    intro hz; rw [hz] at hp; have hz' := Field.zero_ne_one (α := K); grind
  have h4 : (4:K) ≠ 0 := by
    have hp : (4:K)*mu 3=1 := pay 3 (by decide)
    intro hz; rw [hz] at hp; have hz' := Field.zero_ne_one (α := K); grind
  have h6 : (6:K) ≠ 0 := by
    have hp : (6:K)*mu 5=1 := pay 5 (by decide)
    intro hz; rw [hz] at hp; have hz' := Field.zero_ne_one (α := K); grind
  have z := top a b c M T
  have o : 6*(a*M 3)+4*(b*M 4)+3*(c*M 5)=0 := T.j0 1 (by decide)
  have q : 20*(a*M 3)+15*(b*M 4)+12*(c*M 5)=0 := T.j1 1 (by decide) (by decide)
  by_cases ha : a=0
  · by_cases hb : b=0
    · have cn : c ≠ 0 := (live.resolve_left (not_not_intro ha)).resolve_left (not_not_intro hb)
      have kill (t : Nat) (ht : t ≤ 2) : M (t+4)=0 := by
        have e := T.j0 t ht
        change 6*(a*M (t+2))+4*(b*M (t+3))+3*(c*M (t+4))=0 at e
        rw [ha,hb] at e
        apply cancel cn; apply cancel h3; grind
      exact close 4 (by decide) (kill 0 (by decide)) (kill 1 (by decide)) (kill 2 (by decide))
    · by_cases hc : c=0
      · have kill (t : Nat) (ht : t ≤ 2) : M (t+3)=0 := by
          have e := T.j0 t ht
          change 6*(a*M (t+2))+4*(b*M (t+3))+3*(c*M (t+4))=0 at e
          rw [ha,hc] at e
          apply cancel hb; apply cancel h4; grind
        exact close 3 (by decide) (kill 0 (by decide)) (kill 1 (by decide)) (kill 2 (by decide))
      · have k5 := cancel hb z.2.1
        have k6 := cancel hc z.2.2
        have k4 : M 4=0 := by
          rw [ha,k5] at o
          apply cancel hb; apply cancel h4; grind
        exact close 4 (by decide) k4 k5 k6
  · have k4 := cancel ha z.1
    by_cases hb : b=0
    · by_cases hc : c=0
      · have kill (t : Nat) (ht : t ≤ 2) : M (t+2)=0 := by
          have e := T.j0 t ht
          change 6*(a*M (t+2))+4*(b*M (t+3))+3*(c*M (t+4))=0 at e
          rw [hb,hc] at e
          apply cancel ha; apply cancel h6; grind
        exact close 2 (by decide) (kill 0 (by decide)) (kill 1 (by decide)) (kill 2 (by decide))
      · have k3 : M 3=0 := by
          let s := 6*(a*M 3)+3*(c*M 5)
          let t := 20*(a*M 3)+12*(c*M 5)
          have r0 : s=0 := by rw [hb] at o; dsimp [s]; grind
          have r1 : t=0 := by rw [hb] at q; dsimp [t]; grind
          have hst : 4*(a*M 3)=4*s-t := by dsimp only [s,t]; grind only
          rw [r0,r1] at hst
          apply cancel ha; apply cancel h4; grind
        have k5 : M 5=0 := by
          rw [hb,k3] at o
          apply cancel hc; apply cancel h3; grind
        exact close 3 (by decide) k3 k4 k5
    · have k5 := cancel hb z.2.1
      by_cases hc : c=0
      · have k3 : M 3=0 := by
          rw [k4,hc] at o
          apply cancel ha; apply cancel h6; grind
        exact close 3 (by decide) k3 k4 k5
      · exact close 4 (by decide) k4 k5 (cancel hc z.2.2)

end RKResearch.Certified.Graded.CrossedCubicPivot
