module

public import Mathlib.Algebra.Field.Basic
import Mathlib.Tactic.LinearCombination
import Mathlib.Tactic.Ring
import Mathlib.Tactic.NormNum

@[expose] public section

/-! # A rank-one obstruction for an adjacent crossed cubic pair

Rows one through three come from the pure clock reads, and rows four
through eight from the single-primitive reads. Each has its own integer
clearing factor. The field proof does not use characteristic zero or
positivity: the only canceled integer factors divide products of
2, 3, 5, 7.
-/
namespace RKResearch.Certified.Graded.AdjacentCubicScalar

section Field
variable {K : Type*} [Field K]

/-- All four primes are paid by actual order ten. -/
structure Paid (K : Type*) [Field K] : Prop where
  two : (2:K) ≠ 0
  three : (3:K) ≠ 0
  five : (5:K) ≠ 0
  seven : (7:K) ≠ 0

private theorem nz1 (_ : Paid K) : (1:K) ≠ 0 := one_ne_zero

private theorem nz2 (P : Paid K) : (2:K) ≠ 0 := P.two

private theorem nz3 (P : Paid K) : (3:K) ≠ 0 := P.three

private theorem nz4 (P : Paid K) : (4:K) ≠ 0 := by
  rw [show (4:K) = (2:K)^2 by ring]
  exact (pow_ne_zero 2 P.two)

private theorem nz6 (P : Paid K) : (6:K) ≠ 0 := by
  rw [show (6:K) = (2:K)^1 * (3:K)^1 by ring]
  exact (mul_ne_zero (pow_ne_zero 1 P.two) (pow_ne_zero 1 P.three))

private theorem nz10 (P : Paid K) : (10:K) ≠ 0 := by
  rw [show (10:K) = (2:K)^1 * (5:K)^1 by ring]
  exact (mul_ne_zero (pow_ne_zero 1 P.two) (pow_ne_zero 1 P.five))

private theorem nz14 (P : Paid K) : (14:K) ≠ 0 := by
  rw [show (14:K) = (2:K)^1 * (7:K)^1 by ring]
  exact (mul_ne_zero (pow_ne_zero 1 P.two) (pow_ne_zero 1 P.seven))

private theorem nz21 (P : Paid K) : (21:K) ≠ 0 := by
  rw [show (21:K) = (3:K)^1 * (7:K)^1 by ring]
  exact (mul_ne_zero (pow_ne_zero 1 P.three) (pow_ne_zero 1 P.seven))

private theorem nz49 (P : Paid K) : (49:K) ≠ 0 := by
  rw [show (49:K) = (7:K)^2 by ring]
  exact (pow_ne_zero 2 P.seven)

private theorem nz98 (P : Paid K) : (98:K) ≠ 0 := by
  rw [show (98:K) = (2:K)^1 * (7:K)^2 by ring]
  exact (mul_ne_zero (pow_ne_zero 1 P.two) (pow_ne_zero 2 P.seven))

private theorem nz105 (P : Paid K) : (105:K) ≠ 0 := by
  rw [show (105:K) = (3:K)^1 * (5:K)^1 * (7:K)^1 by ring]
  exact (mul_ne_zero (mul_ne_zero (pow_ne_zero 1 P.three) (pow_ne_zero 1 P.five)) (pow_ne_zero 1 P.seven))

private theorem nz315 (P : Paid K) : (315:K) ≠ 0 := by
  rw [show (315:K) = (3:K)^2 * (5:K)^1 * (7:K)^1 by ring]
  exact (mul_ne_zero (mul_ne_zero (pow_ne_zero 2 P.three) (pow_ne_zero 1 P.five)) (pow_ne_zero 1 P.seven))

private theorem nz420 (P : Paid K) : (420:K) ≠ 0 := by
  rw [show (420:K) = (2:K)^2 * (3:K)^1 * (5:K)^1 * (7:K)^1 by ring]
  exact (mul_ne_zero (mul_ne_zero (mul_ne_zero (pow_ne_zero 2 P.two) (pow_ne_zero 1 P.three)) (pow_ne_zero 1 P.five)) (pow_ne_zero 1 P.seven))

private theorem nz490 (P : Paid K) : (490:K) ≠ 0 := by
  rw [show (490:K) = (2:K)^1 * (5:K)^1 * (7:K)^2 by ring]
  exact (mul_ne_zero (mul_ne_zero (pow_ne_zero 1 P.two) (pow_ne_zero 1 P.five)) (pow_ne_zero 2 P.seven))

private theorem nz686 (P : Paid K) : (686:K) ≠ 0 := by
  rw [show (686:K) = (2:K)^1 * (7:K)^3 by ring]
  exact (mul_ne_zero (pow_ne_zero 1 P.two) (pow_ne_zero 3 P.seven))


def row0 (x : K) (u : Fin 9 → K) : K :=
  (-70*(2*x - 1)) * u 0 + (-14*(5*x - 3)) * u 1 + (-14*(3*x - 2)) * u 2 + (-14*(5*x - 3)) * u 3 + (-14*(3*x - 2)) * u 4 + (-4*(7*x - 5)) * u 5 + (-14*(3*x - 2)) * u 6 + (-4*(7*x - 5)) * u 7 + (-5*(4*x - 3)) * u 8

def row1 (x : K) (u : Fin 9 → K) : K :=
  (-42*(5*x - 3)) * u 0 + (-42*(3*x - 2)) * u 1 + (-12*(7*x - 5)) * u 2 + (-42*(3*x - 2)) * u 3 + (-12*(7*x - 5)) * u 4 + (-15*(4*x - 3)) * u 5 + (-12*(7*x - 5)) * u 6 + (-15*(4*x - 3)) * u 7 + (-5*(9*x - 7)) * u 8

def row2 (x : K) (u : Fin 9 → K) : K :=
  (-42*(3*x - 2)) * u 0 + (-12*(7*x - 5)) * u 1 + (-15*(4*x - 3)) * u 2 + (-12*(7*x - 5)) * u 3 + (-15*(4*x - 3)) * u 4 + (-5*(9*x - 7)) * u 5 + (-15*(4*x - 3)) * u 6 + (-5*(9*x - 7)) * u 7 + (-7*(5*x - 4)) * u 8

def row3 (x : K) (u : Fin 9 → K) : K :=
  (-84*(5*x - 3)) * u 0 + (-84*(3*x - 2)) * u 1 + (-24*(7*x - 5)) * u 2 + (-56*(3*x - 2)) * u 3 + (-16*(7*x - 5)) * u 4 + (-20*(4*x - 3)) * u 5 + (-12*(7*x - 5)) * u 6 + (-15*(4*x - 3)) * u 7 + (-5*(9*x - 7)) * u 8

def row4 (_x : K) (u : Fin 9 → K) : K :=
  (-84) * u 0 + (-56) * u 1 + (-40) * u 2 + (-28) * u 3 + (-20) * u 4 + (-15) * u 5 + (-12) * u 6 + (-9) * u 7 + (-7) * u 8

def row5 (x : K) (u : Fin 9 → K) : K :=
  (-252*(3*x - 2)) * u 0 + (-72*(7*x - 5)) * u 1 + (-90*(4*x - 3)) * u 2 + (-48*(7*x - 5)) * u 3 + (-60*(4*x - 3)) * u 4 + (-20*(9*x - 7)) * u 5 + (-45*(4*x - 3)) * u 6 + (-15*(9*x - 7)) * u 7 + (-21*(5*x - 4)) * u 8

def row6 (_x : K) (u : Fin 9 → K) : K :=
  (-840) * u 0 + (-600) * u 1 + (-450) * u 2 + (-300) * u 3 + (-225) * u 4 + (-175) * u 5 + (-135) * u 6 + (-105) * u 7 + (-84) * u 8

def row7 (_x : K) (u : Fin 9 → K) : K :=
  (-252) * u 0 + (-180) * u 1 + (-135) * u 2 + (-96) * u 3 + (-72) * u 4 + (-56) * u 5 + (-45) * u 6 + (-35) * u 7 + (-28) * u 8

structure Tests (x : K) (u : Fin 9 → K) : Prop where
  ok0 : row0 x u=0
  ok1 : row1 x u=0
  ok2 : row2 x u=0
  ok3 : row3 x u=0
  ok4 : row4 x u=0
  ok5 : row5 x u=0
  ok6 : row6 x u=0
  ok7 : row7 x u=0

/-- Only five minors of the 3 by 3 coefficient-product array are needed. -/
structure RankOne (u : Fin 9 → K) : Prop where
  m00 : u 0 * u 4 = u 1 * u 3
  m01 : u 0 * u 5 = u 2 * u 3
  m02 : u 1 * u 5 = u 2 * u 4
  m10 : u 0 * u 7 = u 1 * u 6
  m20 : u 3 * u 7 = u 4 * u 6

def disc (x : K) : K := x^2*(x-1)^2*(2*x-1)

private theorem generic (P : Paid K) (x : K) (u : Fin 9 → K)
    (T : Tests x u) (O : RankOne u) (hdisc : disc x ≠ 0) : ∀ i, u i=0 := by
  have h0 := T.ok0
  have h1 := T.ok1
  have h2 := T.ok2
  have h3 := T.ok3
  have h4 := T.ok4
  have h5 := T.ok5
  have h6 := T.ok6
  have h7 := T.ok7
  dsimp only [row0,row1,row2,row3,row4,row5,row6,row7] at h0 h1 h2 h3 h4 h5 h6 h7
  have p1 : (6:K)*disc x*(10*u 1 - (-35)*u 0)=0 := by
    unfold disc
    linear_combination (15*x^3*(4*x - 3)) * h0 + (-5*x^2*(3*x - 1)*(4*x - 3)) * h1 + (-5*x*(6*x^3 - 24*x^2 + 23*x - 6)) * h2 + (-15*x^3*(4*x - 3)) * h3 + (-45*x^2*(6*x^3 - 22*x^2 + 20*x - 5)) * h4 + (5*x*(2*x - 1)*(10*x^2 - 15*x + 6)) * h5 + (5*x*(2*x - 1)*(12*x^3 - 34*x^2 + 27*x - 6)) * h6 + (-5*x*(4*x - 3)*(24*x^3 - 60*x^2 + 45*x - 10)) * h7
  have E1 : 10*u 1=(-35:K)*u 0 :=
    sub_eq_zero.mp ((mul_eq_zero.mp p1).resolve_left (mul_ne_zero (nz6 P) hdisc))
  have p2 : (3:K)*disc x*(10*u 2 - (28)*u 0)=0 := by
    unfold disc
    linear_combination (-6*x^3*(7*x - 5)) * h0 + (2*x^2*(3*x - 1)*(7*x - 5)) * h1 + (2*x*(9*x^3 - 39*x^2 + 38*x - 10)) * h2 + (6*x^3*(7*x - 5)) * h3 + (6*x^2*(29*x^3 - 110*x^2 + 100*x - 25)) * h4 + (-2*x*(2*x - 1)*(17*x^2 - 25*x + 10)) * h5 + (-2*x*(2*x - 1)*(3*x - 5)*(7*x^2 - 8*x + 2)) * h6 + (2*x*(7*x - 5)*(24*x^3 - 60*x^2 + 45*x - 10)) * h7
  have E2 : 10*u 2=(28:K)*u 0 :=
    sub_eq_zero.mp ((mul_eq_zero.mp p2).resolve_left (mul_ne_zero (nz3 P) hdisc))
  have p3 : (6:K)*disc x*(10*u 3 - (-105)*u 0)=0 := by
    unfold disc
    linear_combination (15*x^2*(36*x^2 - 55*x + 20)) * h0 + (-5*x*(48*x^3 - 51*x^2 - 5*x + 10)) * h1 + (-5*(30*x^4 - 132*x^3 + 165*x^2 - 74*x + 10)) * h2 + (-15*x*(56*x^3 - 105*x^2 + 60*x - 10)) * h3 + (45*x^2*(66*x^3 - 130*x^2 + 80*x - 15)) * h4 + (5*(2*x - 1)^2*(25*x^2 - 34*x + 10)) * h5 + (-5*(2*x - 1)*(12*x^4 + 26*x^3 - 81*x^2 + 54*x - 10)) * h6 + (-5*(144*x^5 - 720*x^4 + 1260*x^3 - 1005*x^2 + 370*x - 50)) * h7
  have E3 : 10*u 3=(-105:K)*u 0 :=
    sub_eq_zero.mp ((mul_eq_zero.mp p3).resolve_left (mul_ne_zero (nz6 P) hdisc))
  have p4 : (3:K)*disc x*(10*u 4 - (336)*u 0)=0 := by
    unfold disc
    linear_combination (-6*x^2*(189*x^2 - 255*x + 80)) * h0 + (2*x*(327*x^3 - 354*x^2 + 15*x + 40)) * h1 + (2*(153*x^4 - 708*x^3 + 846*x^2 - 345*x + 40)) * h2 + (6*x*(269*x^3 - 455*x^2 + 240*x - 40)) * h3 + (-18*x^2*(239*x^3 - 380*x^2 + 180*x - 25)) * h4 + (-2*(2*x - 1)*(294*x^3 - 505*x^2 + 265*x - 40)) * h5 + (-2*(2*x - 1)*(42*x^4 - 378*x^3 + 547*x^2 - 265*x + 40)) * h6 + (2*(1386*x^5 - 5535*x^4 + 8100*x^3 - 5490*x^2 + 1725*x - 200)) * h7
  have E4 : 10*u 4=(336:K)*u 0 :=
    sub_eq_zero.mp ((mul_eq_zero.mp p4).resolve_left (mul_ne_zero (nz3 P) hdisc))
  have p5 : (1:K)*disc x*(10*u 5 - (-252)*u 0)=0 := by
    unfold disc
    linear_combination (12*x^2*(28*x^2 - 35*x + 10)) * h0 + (-4*x*(54*x^3 - 58*x^2 + 5*x + 5)) * h1 + (-2*(42*x^4 - 207*x^3 + 244*x^2 - 95*x + 10)) * h2 + (-12*x*(38*x^3 - 60*x^2 + 30*x - 5)) * h3 + (36*x^3*(28*x^2 - 35*x + 10)) * h4 + (2*(2*x - 1)*(91*x^3 - 150*x^2 + 75*x - 10)) * h5 + (2*(2*x - 1)*(x^2 - 4*x + 1)*(28*x^2 - 35*x + 10)) * h6 + (-2*(28*x^2 - 35*x + 10)*(18*x^3 - 45*x^2 + 30*x - 5)) * h7
  have E5 : 10*u 5=(-252:K)*u 0 :=
    sub_eq_zero.mp ((mul_eq_zero.mp p5).resolve_left (by simpa only [one_mul] using hdisc))
  have p6 : (3:K)*disc x*(10*u 6 - (196)*u 0)=0 := by
    unfold disc
    linear_combination (-6*x^2*(179*x^2 - 280*x + 105)) * h0 + (2*x*(257*x^3 - 319*x^2 + 35*x + 35)) * h1 + (2*(93*x^4 - 478*x^3 + 626*x^2 - 280*x + 35)) * h2 + (6*x*(249*x^3 - 455*x^2 + 245*x - 35)) * h3 + (-6*x^2*(887*x^3 - 1715*x^2 + 1015*x - 175)) * h4 + (-2*(2*x - 1)*(214*x^3 - 385*x^2 + 210*x - 35)) * h5 + (2*(2*x - 1)*(63*x^4 + 88*x^3 - 322*x^2 + 210*x - 35)) * h6 + (2*(546*x^5 - 2835*x^4 + 5000*x^3 - 3940*x^2 + 1400*x - 175)) * h7
  have E6 : 10*u 6=(196:K)*u 0 :=
    sub_eq_zero.mp ((mul_eq_zero.mp p6).resolve_left (mul_ne_zero (nz3 P) hdisc))
  have p7 : (1:K)*disc x*(10*u 7 - (-588)*u 0)=0 := by
    unfold disc
    linear_combination (18*x^2*(68*x^2 - 100*x + 35)) * h0 + (-2*x*(332*x^3 - 404*x^2 + 55*x + 35)) * h1 + (-2*(98*x^4 - 543*x^3 + 701*x^2 - 300*x + 35)) * h2 + (-6*x*(274*x^3 - 475*x^2 + 245*x - 35)) * h3 + (54*x^2*(98*x^3 - 175*x^2 + 95*x - 15)) * h4 + (2*(2*x - 1)*(259*x^3 - 445*x^2 + 230*x - 35)) * h5 + (-2*(2*x - 1)*(28*x^4 + 203*x^3 - 417*x^2 + 230*x - 35)) * h6 + (-2*(896*x^5 - 3990*x^4 + 6325*x^3 - 4565*x^2 + 1500*x - 175)) * h7
  have E7 : 10*u 7=(-588:K)*u 0 :=
    sub_eq_zero.mp ((mul_eq_zero.mp p7).resolve_left (by simpa only [one_mul] using hdisc))
  have p8 : (1:K)*disc x*(10*u 8 - (420)*u 0)=0 := by
    unfold disc
    linear_combination (-30*x^2*(32*x^2 - 45*x + 15)) * h0 + (10*x*(56*x^3 - 67*x^2 + 10*x + 5)) * h1 + (10*(14*x^4 - 84*x^3 + 108*x^2 - 45*x + 5)) * h2 + (30*x*(42*x^3 - 70*x^2 + 35*x - 5)) * h3 + (-90*x^2*(42*x^3 - 70*x^2 + 35*x - 5)) * h4 + (-10*(2*x - 1)*(42*x^3 - 70*x^2 + 35*x - 5)) * h5 + (10*(2*x - 1)*(42*x^3 - 70*x^2 + 35*x - 5)) * h6 + (10*(4*x^2 - 10*x + 5)*(42*x^3 - 70*x^2 + 35*x - 5)) * h7
  have E8 : 10*u 8=(420:K)*u 0 :=
    sub_eq_zero.mp ((mul_eq_zero.mp p8).resolve_left (by simpa only [one_mul] using hdisc))
  have hmin : (10*u 0)*(10*u 4)-(10*u 1)*(10*u 3)=0 := by
    linear_combination 100 * O.m00
  rw [E1,E3,E4] at hmin
  have p0 : (315:K)*(u 0)^2=0 := by linear_combination -hmin
  have u0 : u 0=0 := sq_eq_zero_iff.mp ((mul_eq_zero.mp p0).resolve_left (nz315 P))
  intro i
  have idx : ∀ i : Fin 9, i=0 ∨ i=1 ∨ i=2 ∨ i=3 ∨ i=4 ∨ i=5 ∨ i=6 ∨ i=7 ∨ i=8 := by decide
  rcases idx i with rfl|rfl|rfl|rfl|rfl|rfl|rfl|rfl|rfl
  · exact u0
  · rw [u0,mul_zero] at E1
    exact (mul_eq_zero.mp E1).resolve_left (nz10 P)
  · rw [u0,mul_zero] at E2
    exact (mul_eq_zero.mp E2).resolve_left (nz10 P)
  · rw [u0,mul_zero] at E3
    exact (mul_eq_zero.mp E3).resolve_left (nz10 P)
  · rw [u0,mul_zero] at E4
    exact (mul_eq_zero.mp E4).resolve_left (nz10 P)
  · rw [u0,mul_zero] at E5
    exact (mul_eq_zero.mp E5).resolve_left (nz10 P)
  · rw [u0,mul_zero] at E6
    exact (mul_eq_zero.mp E6).resolve_left (nz10 P)
  · rw [u0,mul_zero] at E7
    exact (mul_eq_zero.mp E7).resolve_left (nz10 P)
  · rw [u0,mul_zero] at E8
    exact (mul_eq_zero.mp E8).resolve_left (nz10 P)

private theorem exceptional0 (P : Paid K) (u : Fin 9 → K) (T : Tests 0 u) (O : RankOne u) : ∀ i, u i=0 := by
  have h0 : (70) * u 0 + (42) * u 1 + (28) * u 2 + (42) * u 3 + (28) * u 4 + (20) * u 5 + (28) * u 6 + (20) * u 7 + (15) * u 8=0 := by
    have e := T.ok0
    unfold row0 at e
    linear_combination e
  have h1 : (126) * u 0 + (84) * u 1 + (60) * u 2 + (84) * u 3 + (60) * u 4 + (45) * u 5 + (60) * u 6 + (45) * u 7 + (35) * u 8=0 := by
    have e := T.ok1
    unfold row1 at e
    linear_combination e
  have h2 : (84) * u 0 + (60) * u 1 + (45) * u 2 + (60) * u 3 + (45) * u 4 + (35) * u 5 + (45) * u 6 + (35) * u 7 + (28) * u 8=0 := by
    have e := T.ok2
    unfold row2 at e
    linear_combination e
  have h3 : (252) * u 0 + (168) * u 1 + (120) * u 2 + (112) * u 3 + (80) * u 4 + (60) * u 5 + (60) * u 6 + (45) * u 7 + (35) * u 8=0 := by
    have e := T.ok3
    unfold row3 at e
    linear_combination e
  have h4 : (-84) * u 0 + (-56) * u 1 + (-40) * u 2 + (-28) * u 3 + (-20) * u 4 + (-15) * u 5 + (-12) * u 6 + (-9) * u 7 + (-7) * u 8=0 := by
    have e := T.ok4
    unfold row4 at e
    linear_combination e
  have h5 : (504) * u 0 + (360) * u 1 + (270) * u 2 + (240) * u 3 + (180) * u 4 + (140) * u 5 + (135) * u 6 + (105) * u 7 + (84) * u 8=0 := by
    have e := T.ok5
    unfold row5 at e
    linear_combination e
  have h6 : (-840) * u 0 + (-600) * u 1 + (-450) * u 2 + (-300) * u 3 + (-225) * u 4 + (-175) * u 5 + (-135) * u 6 + (-105) * u 7 + (-84) * u 8=0 := by
    have e := T.ok6
    unfold row6 at e
    linear_combination e
  let s := (5:K)*u 5
  let t := (2:K)*u 8
  have E0 : (420:K)*u 0 = (-10)*s+(-10)*t := by
    have y : (1:K)*((420:K)*u 0-((-10)*s+(-10)*t))=0 := by
      dsimp only [s,t]
      linear_combination (300) * h0 + (-50) * h1 + (-120) * h2 + (-450) * h3 + (-900) * h4 + (200) * h5 + (80) * h6
    exact sub_eq_zero.mp ((mul_eq_zero.mp y).resolve_left (nz1 P))
  have E1 : (420:K)*u 1 = (35)*s+(35)*t := by
    have y : (1:K)*((420:K)*u 1-((35)*s+(35)*t))=0 := by
      dsimp only [s,t]
      linear_combination (-1050) * h0 + (490) * h1 + (945) * h3 + (1575) * h4 + (-420) * h5 + (-140) * h6
    exact sub_eq_zero.mp ((mul_eq_zero.mp y).resolve_left (nz1 P))
  have E2 : (420:K)*u 2 = (-28)*s+(-28)*t := by
    have y : (1:K)*((420:K)*u 2-((-28)*s+(-28)*t))=0 := by
      dsimp only [s,t]
      linear_combination (840) * h0 + (-560) * h1 + (252) * h2 + (-420) * h3 + (-420) * h4 + (168) * h5 + (28) * h6
    exact sub_eq_zero.mp ((mul_eq_zero.mp y).resolve_left (nz1 P))
  have E3 : (420:K)*u 3 = (35)*s+(0)*t := by
    have y : (1:K)*((420:K)*u 3-((35)*s+(0)*t))=0 := by
      dsimp only [s,t]
      linear_combination (-1260) * h1 + (1680) * h2 + (2205) * h3 + (4725) * h4 + (-980) * h5 + (-420) * h6
    exact sub_eq_zero.mp ((mul_eq_zero.mp y).resolve_left (nz1 P))
  have E4 : (420:K)*u 4 = (-112)*s+(0)*t := by
    have y : (1:K)*((420:K)*u 4-((-112)*s+(0)*t))=0 := by
      dsimp only [s,t]
      linear_combination (1680) * h1 + (-2352) * h2 + (-2940) * h3 + (-6300) * h4 + (1372) * h5 + (588) * h6
    exact sub_eq_zero.mp ((mul_eq_zero.mp y).resolve_left (nz1 P))
  have E5 : (420:K)*u 5 = (84)*s+(0)*t := by
    dsimp only [s,t]
    ring
  have E6 : (420:K)*u 6 = (0)*s+(98)*t := by
    have y : (1:K)*((420:K)*u 6-((0)*s+(98)*t))=0 := by
      dsimp only [s,t]
      linear_combination (1960) * h1 + (-2520) * h2 + (-2940) * h3 + (-5880) * h4 + (1260) * h5 + (504) * h6
    exact sub_eq_zero.mp ((mul_eq_zero.mp y).resolve_left (nz1 P))
  have E7 : (420:K)*u 7 = (0)*s+(-294)*t := by
    have y : (1:K)*((420:K)*u 7-((0)*s+(-294)*t))=0 := by
      dsimp only [s,t]
      linear_combination (-2520) * h1 + (3360) * h2 + (3780) * h3 + (7560) * h4 + (-1680) * h5 + (-672) * h6
    exact sub_eq_zero.mp ((mul_eq_zero.mp y).resolve_left (nz1 P))
  have E8 : (420:K)*u 8 = (0)*s+(210)*t := by
    dsimp only [s,t]
    ring

  have q00 : (105:K)*s*(s+t)=0 := by
    have e : (420*u 0)*(420*u 4)-(420*u 1)*(420*u 3)=0 := by
      linear_combination 176400*O.m00
    rw [E0,E4,E1,E3] at e
    linear_combination -e
  have q10 : (490:K)*t*(s+t)=0 := by
    have e : (420*u 0)*(420*u 7)-(420*u 1)*(420*u 6)=0 := by
      linear_combination 176400*O.m10
    rw [E0,E7,E1,E6] at e
    linear_combination -e
  have q20 : (686:K)*s*t=0 := by
    have e : (420*u 3)*(420*u 7)-(420*u 4)*(420*u 6)=0 := by
      linear_combination 176400*O.m20
    rw [E3,E7,E4,E6] at e
    linear_combination e
  have zst := (mul_eq_zero.mp (show (686:K)*(s*t)=0 by simpa only [mul_assoc] using q20)).resolve_left (nz686 P)
  have z : s=0 ∧ t=0 := by
    rcases mul_eq_zero.mp zst with hs|ht
    · rw [hs,zero_add] at q10
      have t0 : t*t=0 := (mul_eq_zero.mp (show (490:K)*(t*t)=0 by simpa only [mul_assoc] using q10)).resolve_left (nz490 P)
      exact ⟨hs,(mul_eq_zero.mp t0).elim id id⟩
    · rw [ht,add_zero] at q00
      have s0 : s*s=0 := (mul_eq_zero.mp (show (105:K)*(s*s)=0 by simpa only [mul_assoc] using q00)).resolve_left (nz105 P)
      exact ⟨(mul_eq_zero.mp s0).elim id id,ht⟩
  intro i
  have idx : ∀ i : Fin 9, i=0 ∨ i=1 ∨ i=2 ∨ i=3 ∨ i=4 ∨ i=5 ∨ i=6 ∨ i=7 ∨ i=8 := by decide
  rcases idx i with rfl|rfl|rfl|rfl|rfl|rfl|rfl|rfl|rfl
  · have y := E0
    simp only [z.1,z.2,mul_zero,add_zero] at y
    exact (mul_eq_zero.mp y).resolve_left (nz420 P)
  · have y := E1
    simp only [z.1,z.2,mul_zero,add_zero] at y
    exact (mul_eq_zero.mp y).resolve_left (nz420 P)
  · have y := E2
    simp only [z.1,z.2,mul_zero,add_zero] at y
    exact (mul_eq_zero.mp y).resolve_left (nz420 P)
  · have y := E3
    simp only [z.1,z.2,mul_zero,add_zero] at y
    exact (mul_eq_zero.mp y).resolve_left (nz420 P)
  · have y := E4
    simp only [z.1,z.2,mul_zero,add_zero] at y
    exact (mul_eq_zero.mp y).resolve_left (nz420 P)
  · have y := E5
    simp only [z.1,z.2,mul_zero,add_zero] at y
    exact (mul_eq_zero.mp y).resolve_left (nz420 P)
  · have y := E6
    simp only [z.1,z.2,mul_zero,add_zero] at y
    exact (mul_eq_zero.mp y).resolve_left (nz420 P)
  · have y := E7
    simp only [z.1,z.2,mul_zero,add_zero] at y
    exact (mul_eq_zero.mp y).resolve_left (nz420 P)
  · have y := E8
    simp only [z.1,z.2,mul_zero,add_zero] at y
    exact (mul_eq_zero.mp y).resolve_left (nz420 P)

private theorem exceptional1 (P : Paid K) (u : Fin 9 → K) (T : Tests 1 u) (O : RankOne u) : ∀ i, u i=0 := by
  have h0 : (-70) * u 0 + (-28) * u 1 + (-14) * u 2 + (-28) * u 3 + (-14) * u 4 + (-8) * u 5 + (-14) * u 6 + (-8) * u 7 + (-5) * u 8=0 := by
    have e := T.ok0
    unfold row0 at e
    linear_combination e
  have h1 : (-84) * u 0 + (-42) * u 1 + (-24) * u 2 + (-42) * u 3 + (-24) * u 4 + (-15) * u 5 + (-24) * u 6 + (-15) * u 7 + (-10) * u 8=0 := by
    have e := T.ok1
    unfold row1 at e
    linear_combination e
  have h2 : (-42) * u 0 + (-24) * u 1 + (-15) * u 2 + (-24) * u 3 + (-15) * u 4 + (-10) * u 5 + (-15) * u 6 + (-10) * u 7 + (-7) * u 8=0 := by
    have e := T.ok2
    unfold row2 at e
    linear_combination e
  have h3 : (-168) * u 0 + (-84) * u 1 + (-48) * u 2 + (-56) * u 3 + (-32) * u 4 + (-20) * u 5 + (-24) * u 6 + (-15) * u 7 + (-10) * u 8=0 := by
    have e := T.ok3
    unfold row3 at e
    linear_combination e
  have h4 : (-84) * u 0 + (-56) * u 1 + (-40) * u 2 + (-28) * u 3 + (-20) * u 4 + (-15) * u 5 + (-12) * u 6 + (-9) * u 7 + (-7) * u 8=0 := by
    have e := T.ok4
    unfold row4 at e
    linear_combination e
  have h5 : (-252) * u 0 + (-144) * u 1 + (-90) * u 2 + (-96) * u 3 + (-60) * u 4 + (-40) * u 5 + (-45) * u 6 + (-30) * u 7 + (-21) * u 8=0 := by
    have e := T.ok5
    unfold row5 at e
    linear_combination e
  have h6 : (-840) * u 0 + (-600) * u 1 + (-450) * u 2 + (-300) * u 3 + (-225) * u 4 + (-175) * u 5 + (-135) * u 6 + (-105) * u 7 + (-84) * u 8=0 := by
    have e := T.ok6
    unfold row6 at e
    linear_combination e
  let s := (5:K)*u 7
  let t := (2:K)*u 8
  have E0 : (420:K)*u 0 = (-4)*s+(-9)*t := by
    have y : (1:K)*((420:K)*u 0-((-4)*s+(-9)*t))=0 := by
      dsimp only [s,t]
      linear_combination (-450) * h0 + (500) * h1 + (-380) * h2 + (300) * h3 + (-540) * h4 + (-160) * h5 + (48) * h6
    exact sub_eq_zero.mp ((mul_eq_zero.mp y).resolve_left (nz1 P))
  have E1 : (420:K)*u 1 = (7)*s+(7)*t := by
    have y : (1:K)*((420:K)*u 1-((7)*s+(7)*t))=0 := by
      dsimp only [s,t]
      linear_combination (2100) * h0 + (-2100) * h1 + (1400) * h2 + (-1575) * h3 + (2520) * h4 + (840) * h5 + (-224) * h6
    exact sub_eq_zero.mp ((mul_eq_zero.mp y).resolve_left (nz1 P))
  have E2 : (420:K)*u 2 = (0)*s+(14)*t := by
    have y : (1:K)*((420:K)*u 2-((0)*s+(14)*t))=0 := by
      dsimp only [s,t]
      linear_combination (-2100) * h0 + (1960) * h1 + (-1260) * h2 + (1680) * h3 + (-2940) * h4 + (-840) * h5 + (252) * h6
    exact sub_eq_zero.mp ((mul_eq_zero.mp y).resolve_left (nz1 P))
  have E3 : (420:K)*u 3 = (35)*s+(70)*t := by
    have y : (1:K)*((420:K)*u 3-((35)*s+(70)*t))=0 := by
      dsimp only [s,t]
      linear_combination (2100) * h0 + (-2450) * h1 + (1960) * h2 + (-1575) * h3 + (3150) * h4 + (840) * h5 + (-280) * h6
    exact sub_eq_zero.mp ((mul_eq_zero.mp y).resolve_left (nz1 P))
  have E4 : (420:K)*u 4 = (-56)*s+(-28)*t := by
    have y : (1:K)*((420:K)*u 4-((-56)*s+(-28)*t))=0 := by
      dsimp only [s,t]
      linear_combination (-8400) * h0 + (8960) * h1 + (-6160) * h2 + (6720) * h3 + (-11340) * h4 + (-3780) * h5 + (1036) * h6
    exact sub_eq_zero.mp ((mul_eq_zero.mp y).resolve_left (nz1 P))
  have E5 : (420:K)*u 5 = (0)*s+(-126)*t := by
    have y : (1:K)*((420:K)*u 5-((0)*s+(-126)*t))=0 := by
      dsimp only [s,t]
      linear_combination (7560) * h0 + (-7560) * h1 + (5040) * h2 + (-6300) * h3 + (11340) * h4 + (3360) * h5 + (-1008) * h6
    exact sub_eq_zero.mp ((mul_eq_zero.mp y).resolve_left (nz1 P))
  have E6 : (420:K)*u 6 = (-56)*s+(-98)*t := by
    have y : (1:K)*((420:K)*u 6-((-56)*s+(-98)*t))=0 := by
      dsimp only [s,t]
      linear_combination (-280) * h2 + (-840) * h4 + (140) * h5 + (56) * h6
    exact sub_eq_zero.mp ((mul_eq_zero.mp y).resolve_left (nz1 P))
  have E7 : (420:K)*u 7 = (84)*s+(0)*t := by
    dsimp only [s,t]
    ring
  have E8 : (420:K)*u 8 = (0)*s+(210)*t := by
    dsimp only [s,t]
    ring

  have q00 : (7:K)*(34*t^2+17*s*t+3*s^2)=0 := by
    have e : (420*u 0)*(420*u 4)-(420*u 1)*(420*u 3)=0 := by
      linear_combination 176400*O.m00
    rw [E0,E4,E1,E3] at e
    linear_combination -e
  have q01 : (14:K)*t*(11*t+s)=0 := by
    have e : (420*u 0)*(420*u 5)-(420*u 2)*(420*u 3)=0 := by
      linear_combination 176400*O.m01
    rw [E0,E5,E2,E3] at e
    linear_combination e
  have q02 : (98:K)*t*(5*t+s)=0 := by
    have e : (420*u 1)*(420*u 5)-(420*u 2)*(420*u 4)=0 := by
      linear_combination 176400*O.m02
    rw [E1,E5,E2,E4] at e
    linear_combination -e
  have zt : t=0 := by
    by_contra tn
    have e1 := (mul_eq_zero.mp q01).resolve_left (mul_ne_zero (nz14 P) tn)
    have e2 := (mul_eq_zero.mp q02).resolve_left (mul_ne_zero (nz98 P) tn)
    have nn : (6:K)*t=0 := by linear_combination e1-e2
    exact tn ((mul_eq_zero.mp nn).resolve_left (nz6 P))
  have zs : s=0 := by
    have f : 34*t^2+17*s*t+3*s^2=0 := (mul_eq_zero.mp q00).resolve_left P.seven
    rw [zt] at f
    have e : (3:K)*s^2=0 := by linear_combination f
    exact sq_eq_zero_iff.mp ((mul_eq_zero.mp e).resolve_left P.three)
  have z : s=0 ∧ t=0 := ⟨zs,zt⟩
  intro i
  have idx : ∀ i : Fin 9, i=0 ∨ i=1 ∨ i=2 ∨ i=3 ∨ i=4 ∨ i=5 ∨ i=6 ∨ i=7 ∨ i=8 := by decide
  rcases idx i with rfl|rfl|rfl|rfl|rfl|rfl|rfl|rfl|rfl
  · have y := E0
    simp only [z.1,z.2,mul_zero,add_zero] at y
    exact (mul_eq_zero.mp y).resolve_left (nz420 P)
  · have y := E1
    simp only [z.1,z.2,mul_zero,add_zero] at y
    exact (mul_eq_zero.mp y).resolve_left (nz420 P)
  · have y := E2
    simp only [z.1,z.2,mul_zero,add_zero] at y
    exact (mul_eq_zero.mp y).resolve_left (nz420 P)
  · have y := E3
    simp only [z.1,z.2,mul_zero,add_zero] at y
    exact (mul_eq_zero.mp y).resolve_left (nz420 P)
  · have y := E4
    simp only [z.1,z.2,mul_zero,add_zero] at y
    exact (mul_eq_zero.mp y).resolve_left (nz420 P)
  · have y := E5
    simp only [z.1,z.2,mul_zero,add_zero] at y
    exact (mul_eq_zero.mp y).resolve_left (nz420 P)
  · have y := E6
    simp only [z.1,z.2,mul_zero,add_zero] at y
    exact (mul_eq_zero.mp y).resolve_left (nz420 P)
  · have y := E7
    simp only [z.1,z.2,mul_zero,add_zero] at y
    exact (mul_eq_zero.mp y).resolve_left (nz420 P)
  · have y := E8
    simp only [z.1,z.2,mul_zero,add_zero] at y
    exact (mul_eq_zero.mp y).resolve_left (nz420 P)

private theorem exceptional2 (P : Paid K) (u : Fin 9 → K) (x : K) (Hx : 2*x-1=0) (T : Tests x u) (O : RankOne u) : ∀ i, u i=0 := by
  have h0 : (14) * u 1 + (14) * u 2 + (14) * u 3 + (14) * u 4 + (12) * u 5 + (14) * u 6 + (12) * u 7 + (10) * u 8=0 := by
    have e := T.ok0
    unfold row0 at e
    linear_combination 2*e - ((-140) * u 0 + (-70) * u 1 + (-42) * u 2 + (-70) * u 3 + (-42) * u 4 + (-28) * u 5 + (-42) * u 6 + (-28) * u 7 + (-20) * u 8)*Hx
  have h1 : (42) * u 0 + (42) * u 1 + (36) * u 2 + (42) * u 3 + (36) * u 4 + (30) * u 5 + (36) * u 6 + (30) * u 7 + (25) * u 8=0 := by
    have e := T.ok1
    unfold row1 at e
    linear_combination 2*e - ((-210) * u 0 + (-126) * u 1 + (-84) * u 2 + (-126) * u 3 + (-84) * u 4 + (-60) * u 5 + (-84) * u 6 + (-60) * u 7 + (-45) * u 8)*Hx
  have h2 : (42) * u 0 + (36) * u 1 + (30) * u 2 + (36) * u 3 + (30) * u 4 + (25) * u 5 + (30) * u 6 + (25) * u 7 + (21) * u 8=0 := by
    have e := T.ok2
    unfold row2 at e
    linear_combination 2*e - ((-126) * u 0 + (-84) * u 1 + (-60) * u 2 + (-84) * u 3 + (-60) * u 4 + (-45) * u 5 + (-60) * u 6 + (-45) * u 7 + (-35) * u 8)*Hx
  have h3 : (84) * u 0 + (84) * u 1 + (72) * u 2 + (56) * u 3 + (48) * u 4 + (40) * u 5 + (36) * u 6 + (30) * u 7 + (25) * u 8=0 := by
    have e := T.ok3
    unfold row3 at e
    linear_combination 2*e - ((-420) * u 0 + (-252) * u 1 + (-168) * u 2 + (-168) * u 3 + (-112) * u 4 + (-80) * u 5 + (-84) * u 6 + (-60) * u 7 + (-45) * u 8)*Hx
  have h4 : (-168) * u 0 + (-112) * u 1 + (-80) * u 2 + (-56) * u 3 + (-40) * u 4 + (-30) * u 5 + (-24) * u 6 + (-18) * u 7 + (-14) * u 8=0 := by
    have e := T.ok4
    unfold row4 at e
    linear_combination 2*e - (0)*Hx
  have h5 : (252) * u 0 + (216) * u 1 + (180) * u 2 + (144) * u 3 + (120) * u 4 + (100) * u 5 + (90) * u 6 + (75) * u 7 + (63) * u 8=0 := by
    have e := T.ok5
    unfold row5 at e
    linear_combination 2*e - ((-756) * u 0 + (-504) * u 1 + (-360) * u 2 + (-336) * u 3 + (-240) * u 4 + (-180) * u 5 + (-180) * u 6 + (-135) * u 7 + (-105) * u 8)*Hx
  have h6 : (-1680) * u 0 + (-1200) * u 1 + (-900) * u 2 + (-600) * u 3 + (-450) * u 4 + (-350) * u 5 + (-270) * u 6 + (-210) * u 7 + (-168) * u 8=0 := by
    have e := T.ok6
    unfold row6 at e
    linear_combination 2*e - (0)*Hx
  let s := (10:K)*u 7
  let t := (1:K)*u 8
  have E0 : (420:K)*u 0 = (1)*s+(24)*t := by
    have y : (2:K)*((420:K)*u 0-((1)*s+(24)*t))=0 := by
      dsimp only [s,t]
      linear_combination (-150) * h0 + (450) * h1 + (-470) * h2 + (-150) * h3 + (45) * h4 + (60) * h5 + (-4) * h6
    exact sub_eq_zero.mp ((mul_eq_zero.mp y).resolve_left (nz2 P))
  have E1 : (420:K)*u 1 = (-7)*s+(-133)*t := by
    have y : (2:K)*((420:K)*u 1-((-7)*s+(-133)*t))=0 := by
      dsimp only [s,t]
      linear_combination (1050) * h0 + (-1750) * h1 + (1610) * h2 + (-315) * h4 + (28) * h6
    exact sub_eq_zero.mp ((mul_eq_zero.mp y).resolve_left (nz2 P))
  have E2 : (420:K)*u 2 = (7)*s+(126)*t := by
    have y : (2:K)*((420:K)*u 2-((7)*s+(126)*t))=0 := by
      dsimp only [s,t]
      linear_combination (-1050) * h0 + (1470) * h1 + (-1190) * h2 + (210) * h3 + (525) * h4 + (-140) * h5 + (-56) * h6
    exact sub_eq_zero.mp ((mul_eq_zero.mp y).resolve_left (nz2 P))
  have E3 : (420:K)*u 3 = (0)*s+(-105)*t := by
    have y : (1:K)*((420:K)*u 3-((0)*s+(-105)*t))=0 := by
      dsimp only [s,t]
      linear_combination (-1050) * h1 + (1260) * h2 + (525) * h3 + (-210) * h5
    exact sub_eq_zero.mp ((mul_eq_zero.mp y).resolve_left (nz1 P))
  have E4 : (420:K)*u 4 = (35)*s+(826)*t := by
    have y : (1:K)*((420:K)*u 4-((35)*s+(826)*t))=0 := by
      dsimp only [s,t]
      linear_combination (-1050) * h0 + (3710) * h1 + (-4130) * h2 + (-630) * h3 + (-315) * h4 + (350) * h5 + (42) * h6
    exact sub_eq_zero.mp ((mul_eq_zero.mp y).resolve_left (nz1 P))
  have E5 : (420:K)*u 5 = (-42)*s+(-840)*t := by
    have y : (1:K)*((420:K)*u 5-((-42)*s+(-840)*t))=0 := by
      dsimp only [s,t]
      linear_combination (1260) * h0 + (-2940) * h1 + (2940) * h2
    exact sub_eq_zero.mp ((mul_eq_zero.mp y).resolve_left (nz1 P))
  have E6 : (420:K)*u 6 = (-35)*s+(-294)*t := by
    have y : (1:K)*((420:K)*u 6-((-35)*s+(-294)*t))=0 := by
      dsimp only [s,t]
      linear_combination (140) * h2 + (210) * h4 + (-70) * h5 + (-28) * h6
    exact sub_eq_zero.mp ((mul_eq_zero.mp y).resolve_left (nz1 P))
  have E7 : (420:K)*u 7 = (42)*s+(0)*t := by
    dsimp only [s,t]
    ring
  have E8 : (420:K)*u 8 = (0)*s+(420)*t := by
    dsimp only [s,t]
    ring

  have q01 : (21:K)*(10*t+s)*(33*t+2*s)=0 := by
    have e : (420*u 0)*(420*u 5)-(420*u 2)*(420*u 3)=0 := by
      linear_combination 176400*O.m01
    rw [E0,E5,E2,E3] at e
    linear_combination -e
  have q02 : (49:K)*(156*t^2+26*s*t+s^2)=0 := by
    have e : (420*u 1)*(420*u 5)-(420*u 2)*(420*u 4)=0 := by
      linear_combination 176400*O.m02
    rw [E1,E5,E2,E4] at e
    linear_combination e
  have p0 := (mul_eq_zero.mp (show (21:K)*((10*t+s)*(33*t+2*s))=0 by simpa only [mul_assoc] using q01)).resolve_left (nz21 P)
  have p1 := (mul_eq_zero.mp q02).resolve_left (nz49 P)
  have z : s=0 ∧ t=0 := by
    rcases mul_eq_zero.mp p0 with e|e
    · have t0 : (4:K)*t^2=0 := by
        linear_combination (s+16*t)*e-p1
      have zt : t=0 := sq_eq_zero_iff.mp ((mul_eq_zero.mp t0).resolve_left (nz4 P))
      have zs : s=0 := by rw [zt] at e; linear_combination e
      exact ⟨zs,zt⟩
    · have t0 : (3:K)*t^2=0 := by
        linear_combination (2*s+19*t)*e-4*p1
      have zt : t=0 := sq_eq_zero_iff.mp ((mul_eq_zero.mp t0).resolve_left P.three)
      have zs : s=0 := by
        rw [zt] at e
        have y : (2:K)*s=0 := by linear_combination e
        exact (mul_eq_zero.mp y).resolve_left P.two
      exact ⟨zs,zt⟩
  intro i
  have idx : ∀ i : Fin 9, i=0 ∨ i=1 ∨ i=2 ∨ i=3 ∨ i=4 ∨ i=5 ∨ i=6 ∨ i=7 ∨ i=8 := by decide
  rcases idx i with rfl|rfl|rfl|rfl|rfl|rfl|rfl|rfl|rfl
  · have y := E0
    simp only [z.1,z.2,mul_zero,add_zero] at y
    exact (mul_eq_zero.mp y).resolve_left (nz420 P)
  · have y := E1
    simp only [z.1,z.2,mul_zero,add_zero] at y
    exact (mul_eq_zero.mp y).resolve_left (nz420 P)
  · have y := E2
    simp only [z.1,z.2,mul_zero,add_zero] at y
    exact (mul_eq_zero.mp y).resolve_left (nz420 P)
  · have y := E3
    simp only [z.1,z.2,mul_zero,add_zero] at y
    exact (mul_eq_zero.mp y).resolve_left (nz420 P)
  · have y := E4
    simp only [z.1,z.2,mul_zero,add_zero] at y
    exact (mul_eq_zero.mp y).resolve_left (nz420 P)
  · have y := E5
    simp only [z.1,z.2,mul_zero,add_zero] at y
    exact (mul_eq_zero.mp y).resolve_left (nz420 P)
  · have y := E6
    simp only [z.1,z.2,mul_zero,add_zero] at y
    exact (mul_eq_zero.mp y).resolve_left (nz420 P)
  · have y := E7
    simp only [z.1,z.2,mul_zero,add_zero] at y
    exact (mul_eq_zero.mp y).resolve_left (nz420 P)
  · have y := E8
    simp only [z.1,z.2,mul_zero,add_zero] at y
    exact (mul_eq_zero.mp y).resolve_left (nz420 P)

/-- The exact integer mixed rows cannot hold for a nonzero rank-one product
even at the exceptional clocks 0, 1 and 1/2. -/
theorem zero_of_tests (P : Paid K) (x : K) (u : Fin 9 → K)
    (T : Tests x u) (O : RankOne u) : ∀ i, u i=0 := by
  by_cases h0 : x=0
  · subst x
    exact exceptional0 P u T O
  by_cases h1 : x=1
  · subst x
    exact exceptional1 P u T O
  by_cases h2 : 2*x-1=0
  · exact exceptional2 P u x h2 T O
  exact generic P x u T O (mul_ne_zero (mul_ne_zero (pow_ne_zero 2 h0)
    (pow_ne_zero 2 (sub_ne_zero.mpr h1))) h2)

end Field
end RKResearch.Certified.Graded.AdjacentCubicScalar
