module

public import Init.Grind

@[expose] public section

/-! # Exact one-middle-site scalar certificate for DIRK10 with eight dirty labels

The proof is division-free. The local basis for the first primitive is
x²(x−y)(5x−3y) and ten times x²[(4y−12d)x−(3y−12d)y]; the other
primitive uses the reflected basis. The three hypotheses are cleared
ordinary moments through grade nine. The mathematical bridge from
actual order-ten tableaux to these moments is documented separately.
-/

namespace RKResearch.Certified.Graded.EightDirtyCleanScalar


open Lean.Grind

set_option maxHeartbeats 2000000

universe univ
variable {K : Type univ} [Field K]

private theorem mul_ne_zero {a b : K} (ha : a≠0) (hb : b≠0) : a*b≠0 :=
  fun h => (Field.of_mul_eq_zero h).elim ha hb

private theorem pow_ne_zero (n : Nat) {a : K} (ha : a≠0) : a^n≠0 :=
  fun h => ha (Field.of_pow_eq_zero a n h)

private theorem cancel_left {a b c : K} (ha : a≠0) (h : a*b=a*c) : b=c := by
  have z : a*(b-c)=0 := by grind only
  have := (Field.of_mul_eq_zero z).resolve_left ha
  grind only


def rho (y : K) : K := y*(1-y)

def clock (y : K) : K := 42*rho y^2-14*rho y+1

/-- Monomial coefficients after removing the common factor x².
The second basis vector is ten times the displayed journal basis. -/
def coeffs (y a b : K) : K×K×K :=
  (3*y^2*a+(5+42*rho y-30*y)*y*b, -8*y*a+(40*y-(5+42*rho y))*b, 5*a)

def low (p q : K×K×K) : K :=
  p.1*(84*q.1+42*q.2.1+24*q.2.2) +
  p.2.1*(42*q.1+18*q.2.1+9*q.2.2) +
  p.2.2*(24*q.1+9*q.2.1+4*q.2.2)

def high (p q : K×K×K) : K :=
  p.1*(42*q.1+18*q.2.1+9*q.2.2) +
  p.2.1*(24*q.1+9*q.2.1+4*q.2.2) +
  p.2.2*(15*q.1+5*q.2.1+2*q.2.2)

def prim (p q : K×K×K) : K :=
  40*p.1*(42*q.1+18*q.2.1+9*q.2.2) +
  30*p.2.1*(24*q.1+9*q.2.1+4*q.2.2) +
  24*p.2.2*(15*q.1+5*q.2.1+2*q.2.2)

/-- 2520 times the paid read ∫FG − b_y F(y)G(y). -/
def read0 (y a b c d : K) : K :=
  low (coeffs y a b) (coeffs (1-y) c d) - 4200*(7+42*rho y)*y^4*(1-y)^4*b*d

/-- 2520 times the paid read ∫(x−y)FG. -/
def read1 (y a b c d : K) : K :=
  high (coeffs y a b) (coeffs (1-y) c d) - y*low (coeffs y a b) (coeffs (1-y) c d)

/-- 302400 times the paid read ∫(I F−d_y F)G. -/
def read2 (y a b c d : K) : K :=
  prim (coeffs y a b) (coeffs (1-y) c d) -
    (5+42*rho y)*low (coeffs y a b) (coeffs (1-y) c d)

private def det3 (a b c d e f g h i : K) : K :=
  a*(e*i-f*h)-b*(d*i-f*g)+c*(d*h-e*g)

private def m00 (y : K) : K := (16200*y^2 - 16200*y + 4100)

private def m01 (y : K) : K := (22680*y^3 - 45480*y^2 + 27990*y - 5175)

private def m02 (y : K) : K := (-22680*y^3 + 22560*y^2 - 5070*y + 15)

private def m03 (y : K) : K := (2268*y^2 - 2268*y + 561)

private def m10 (y : K) : K := (-46800*y^3 + 70200*y^2 - 36600*y + 6600)

private def m11 (y : K) : K := (36240*y^3 - 64980*y^2 + 37100*y - 6640)

private def m12 (y : K) : K := (36240*y^3 - 43740*y^2 + 15860*y - 1720)

private def m13 (y : K) : K := (-8724*y^3 + 13086*y^2 - 6336*y + 987)

private def m20 (y : K) : K := (152400*y^2 - 152400*y + 35300)

private def m21 (y : K) : K := (118260*y^3 - 262410*y^2 + 175320*y - 35325)

private def m22 (y : K) : K := (-118260*y^3 + 92370*y^2 - 5280*y - 4155)

private def m23 (y : K) : K := (29610*y^2 - 29610*y + 6717)

private def row0 (y a b c d : K) : K :=
  m00 y*a+m01 y*b+m02 y*c+m03 y*d

private theorem row0_transfer (y a b c d : K) (hy : clock y=0) :
    50*read0 y a b c d = row0 y (a*c) (a*(10*d)) ((10*b)*c) ((10*b)*(10*d)) := by
  dsimp [read0,coeffs,low,high,prim,row0,m00,m01,m02,m03,rho]
  unfold clock rho at hy
  have paid := congrArg (fun x : K => ((900)*(a*c) + (12600*y - 19500)*(a*d) + (-12600*y - 6900)*(b*c) + (210000*y^6 - 630000*y^5 + 525000*y^4 - 251400*y^2 + 146400*y + 48900)*(b*d))*x) hy
  simp only [Semiring.mul_zero] at paid
  grind only

private def row1 (y a b c d : K) : K :=
  m10 y*a+m11 y*b+m12 y*c+m13 y*d

private theorem row1_transfer (y a b c d : K) (hy : clock y=0) :
    100*read1 y a b c d = row1 y (a*c) (a*(10*d)) ((10*b)*c) ((10*b)*(10*d)) := by
  dsimp [read1,coeffs,low,high,prim,row1,m10,m11,m12,m13,rho]
  unfold clock rho at hy
  have paid := congrArg (fun x : K => ((-1800*y + 900)*(a*c) + (-25200*y^2 + 51600*y - 33600)*(a*d) + (25200*y^2 + 1200*y + 7200)*(b*c) + (352800*y^3 - 529200*y^2 + 88800*y + 43800)*(b*d))*x) hy
  simp only [Semiring.mul_zero] at paid
  grind only

private def row2 (y a b c d : K) : K :=
  m20 y*a+m21 y*b+m22 y*c+m23 y*d

private theorem row2_transfer (y a b c d : K) (hy : clock y=0) :
    50*read2 y a b c d = row2 y (a*c) (a*(10*d)) ((10*b)*c) ((10*b)*(10*d)) := by
  dsimp [read2,coeffs,low,high,prim,row2,m20,m21,m22,m23,rho]
  unfold clock rho at hy
  have paid := congrArg (fun x : K => ((37800*y^2 - 37800*y + 29700)*(a*c) + (529200*y^3 - 1348200*y^2 + 1234800*y - 490500)*(a*d) + (-529200*y^3 + 239400*y^2 - 126000*y - 74700)*(b*c) + (-7408800*y^4 + 14817600*y^3 - 7686000*y^2 + 277200*y + 940800)*(b*d))*x) hy
  simp only [Semiring.mul_zero] at paid
  grind only

private def n0 (y : K) : K := (286398*y^2 - 286398*y + 65895)

private theorem cof0_eval (y : K) (hy : clock y=0) :
    49*(det3 (m01 y) (m02 y) (m03 y) (m11 y) (m12 y) (m13 y) (m21 y) (m22 y) (m23 y))=75000*n0 y := by
  dsimp [det3,n0,m01,m02,m03,m11,m12,m13,m21,m22,m23]
  unfold clock rho at hy
  have paid := congrArg (fun x : K => (22442659243200*y^4 - 44885318486400*y^3 + 31846177263600*y^2 - 9403518020400*y + 980114106600)*x) hy
  simp only [Semiring.mul_zero] at paid
  grind only

private def n1 (y : K) : K := (2793000*y^3 - 2808750*y^2 + 649530*y - 4980)

private theorem cof1_eval (y : K) (hy : clock y=0) :
    49*(-det3 (m00 y) (m02 y) (m03 y) (m10 y) (m12 y) (m13 y) (m20 y) (m22 y) (m23 y))=75000*n1 y := by
  dsimp [det3,n1,m00,m02,m03,m10,m12,m13,m20,m22,m23]
  unfold clock rho at hy
  have paid := congrArg (fun x : K => (6341994792000*y^4 - 14109477984000*y^3 + 12056192946000*y^2 - 4439984094000*y + 589316211000)*x) hy
  simp only [Semiring.mul_zero] at paid
  grind only

private def n2 (y : K) : K := (-2793000*y^3 + 5570250*y^2 - 3411030*y + 628800)

private theorem cof2_eval (y : K) (hy : clock y=0) :
    49*(det3 (m00 y) (m01 y) (m03 y) (m10 y) (m11 y) (m13 y) (m20 y) (m21 y) (m23 y))=75000*n2 y := by
  dsimp [det3,n2,m00,m01,m03,m10,m11,m13,m20,m21,m23]
  unfold clock rho at hy
  have paid := congrArg (fun x : K => (6341994792000*y^4 - 11258501184000*y^3 + 7779727746000*y^2 - 2711947014000*y + 438041871000)*x) hy
  simp only [Semiring.mul_zero] at paid
  grind only

private def n3 (y : K) : K := (2247000*y^2 - 2247000*y + 528200)

private theorem cof3_eval (y : K) (hy : clock y=0) :
    49*(-det3 (m00 y) (m01 y) (m02 y) (m10 y) (m11 y) (m12 y) (m20 y) (m21 y) (m22 y))=75000*n3 y := by
  dsimp [det3,n3,m00,m01,m02,m10,m11,m12,m20,m21,m22]
  unfold clock rho at hy
  have paid := congrArg (fun x : K => (-67703882400000*y^4 + 135407764800000*y^3 - 91452022200000*y^2 + 23748139800000*y - 1818991200000)*x) hy
  simp only [Semiring.mul_zero] at paid
  grind only

private theorem outer_eval (y : K) (hy : clock y=0) :
    n0 y*n3 y-n1 y*n2 y=1250*(2729314*rho y-646271) := by
  dsimp [n0,n1,n2,n3,rho]
  unfold clock rho at hy
  have paid := congrArg (fun x : K => (185734500000*y^2 - 185734500000*y + 38745001750)*x) hy
  simp only [Semiring.mul_zero] at paid
  grind only

private def minor0 (_p q r s _t u v w _A B C D : K) : K := det3 q r s u v w B C D

private def minor1 (p _q r s t _u v w A _B C D : K) : K := -det3 p r s t v w A C D

private def minor2 (p q _r s t u _v w A B _C D : K) : K := det3 p q s t u w A B D

private def minor3 (p q r _s t u v _w A B C _D : K) : K := -det3 p q r t u v A B C

private theorem cofactor_crosses (a0 a1 a2 a3 p q r s t u v w A B C D : K)
    (e0 : p*a0+q*a1+r*a2+s*a3=0)
    (e1 : t*a0+u*a1+v*a2+w*a3=0)
    (e2 : A*a0+B*a1+C*a2+D*a3=0) :
    (minor1 p q r s t u v w A B C D)*a0=(minor0 p q r s t u v w A B C D)*a1 ∧
    (minor2 p q r s t u v w A B C D)*a0=(minor0 p q r s t u v w A B C D)*a2 ∧
    (minor3 p q r s t u v w A B C D)*a0=(minor0 p q r s t u v w A B C D)*a3 ∧
    (minor2 p q r s t u v w A B C D)*a1=(minor1 p q r s t u v w A B C D)*a2 ∧
    (minor3 p q r s t u v w A B C D)*a1=(minor1 p q r s t u v w A B C D)*a3 ∧
    (minor3 p q r s t u v w A B C D)*a2=(minor2 p q r s t u v w A B C D)*a3 := by
  refine ⟨?_,?_,?_,?_,?_,?_⟩

  · dsimp [minor0,minor1,det3]
    have t0 := congrArg (fun x : K => (C*w - D*v)*x) e0
    have t1 := congrArg (fun x : K => (-C*s + D*r)*x) e1
    have t2 := congrArg (fun x : K => (-r*w + s*v)*x) e2
    simp only [Semiring.mul_zero] at t0 t1 t2
    grind only

  · dsimp [minor0,minor2,det3]
    have t0 := congrArg (fun x : K => (-B*w + D*u)*x) e0
    have t1 := congrArg (fun x : K => (B*s - D*q)*x) e1
    have t2 := congrArg (fun x : K => (q*w - s*u)*x) e2
    simp only [Semiring.mul_zero] at t0 t1 t2
    grind only

  · dsimp [minor0,minor3,det3]
    have t0 := congrArg (fun x : K => (B*v - C*u)*x) e0
    have t1 := congrArg (fun x : K => (-B*r + C*q)*x) e1
    have t2 := congrArg (fun x : K => (-q*v + r*u)*x) e2
    simp only [Semiring.mul_zero] at t0 t1 t2
    grind only

  · dsimp [minor1,minor2,det3]
    have t0 := congrArg (fun x : K => (A*w - D*t)*x) e0
    have t1 := congrArg (fun x : K => (-A*s + D*p)*x) e1
    have t2 := congrArg (fun x : K => (-p*w + s*t)*x) e2
    simp only [Semiring.mul_zero] at t0 t1 t2
    grind only

  · dsimp [minor1,minor3,det3]
    have t0 := congrArg (fun x : K => (-A*v + C*t)*x) e0
    have t1 := congrArg (fun x : K => (A*r - C*p)*x) e1
    have t2 := congrArg (fun x : K => (p*v - r*t)*x) e2
    simp only [Semiring.mul_zero] at t0 t1 t2
    grind only

  · dsimp [minor2,minor3,det3]
    have t0 := congrArg (fun x : K => (A*u - B*t)*x) e0
    have t1 := congrArg (fun x : K => (-A*q + B*p)*x) e1
    have t2 := congrArg (fun x : K => (-p*u + q*t)*x) e2
    simp only [Semiring.mul_zero] at t0 t1 t2
    grind only

private theorem incompatible (n0 n1 n2 n3 a0 a1 a2 a3 : K)
    (hn : n0*n3-n1*n2≠0) (ht : a0*a3-a1*a2=0)
    (h01 : n1*a0=n0*a1) (h02 : n2*a0=n0*a2) (h03 : n3*a0=n0*a3) (h12 : n2*a1=n1*a2) (h13 : n3*a1=n1*a3) (h23 : n3*a2=n2*a3) :
    a0=0 ∧ a1=0 ∧ a2=0 ∧ a3=0 := by
  refine ⟨?_,?_,?_,?_⟩

  · have eq : (n0*n3-n1*n2)*a0^2=n0^2*(a0*a3-a1*a2) := by
      calc
        _ = (n0*a0)*(n3*a0)-(n1*a0)*(n2*a0) := by grind only
        _ = (n0*a0)*(n0*a3)-(n0*a1)*(n0*a2) := by rw [h01, h02, h03]
        _ = _ := by grind only
    rw [ht,Semiring.mul_zero] at eq
    exact Field.of_pow_eq_zero _ 2 ((Field.of_mul_eq_zero eq).resolve_left hn)

  · have eq : (n0*n3-n1*n2)*a1^2=n1^2*(a0*a3-a1*a2) := by
      calc
        _ = (n0*a1)*(n3*a1)-(n1*a1)*(n2*a1) := by grind only
        _ = (n1*a0)*(n1*a3)-(n1*a1)*(n1*a2) := by rw [← h01, h12, h13]
        _ = _ := by grind only
    rw [ht,Semiring.mul_zero] at eq
    exact Field.of_pow_eq_zero _ 2 ((Field.of_mul_eq_zero eq).resolve_left hn)

  · have eq : (n0*n3-n1*n2)*a2^2=n2^2*(a0*a3-a1*a2) := by
      calc
        _ = (n0*a2)*(n3*a2)-(n1*a2)*(n2*a2) := by grind only
        _ = (n2*a0)*(n2*a3)-(n2*a1)*(n2*a2) := by rw [← h02, ← h12, h23]
        _ = _ := by grind only
    rw [ht,Semiring.mul_zero] at eq
    exact Field.of_pow_eq_zero _ 2 ((Field.of_mul_eq_zero eq).resolve_left hn)

  · have eq : (n0*n3-n1*n2)*a3^2=n3^2*(a0*a3-a1*a2) := by
      calc
        _ = (n0*a3)*(n3*a3)-(n1*a3)*(n2*a3) := by grind only
        _ = (n3*a0)*(n3*a3)-(n3*a1)*(n3*a2) := by rw [← h03, ← h13, ← h23]
        _ = _ := by grind only
    rw [ht,Semiring.mul_zero] at eq
    exact Field.of_pow_eq_zero _ 2 ((Field.of_mul_eq_zero eq).resolve_left hn)

private theorem outer_ne (y : K) (hy : clock y=0) (two : (2:K)≠0)
    (three : (3:K)≠0) (five : (5:K)≠0) (seven : (7:K)≠0)
    (guard : (62969:K)*(112249:K)≠0) : n0 y*n3 y-n1 y*n2 y≠0 := by
  rw [outer_eval y hy]
  have num : (1250:K)=2*5^4 := by grind only
  rw [num]
  apply mul_ne_zero (mul_ne_zero two (pow_ne_zero 4 five))
  intro h
  unfold clock at hy
  have bad : (2:K)*3*7*(62969*112249)=0 := by
    have paid0 := congrArg (fun x : K => ((2729314:K)^2)*x) hy
    have paid1 := congrArg (fun x : K => ((42*2729314*rho y +42*646271-14*2729314))*x) h
    simp only [Semiring.mul_zero] at paid0 paid1
    grind only
  exact (mul_ne_zero (mul_ne_zero (mul_ne_zero two three) seven) guard) bad

/-- The paid scalar face cannot contain a nonzero rank-one profile tensor.
No ordered structure or characteristic-zero hypothesis is built in. -/
theorem no_clean_scalar_reads (y a b c d : K) (hy : clock y=0)
    (two : (2:K)≠0) (three : (3:K)≠0) (five : (5:K)≠0) (seven : (7:K)≠0)
    (guard : (62969:K)*(112249:K)≠0)
    (hf : a≠0 ∨ b≠0) (hg : c≠0 ∨ d≠0)
    (H0 : read0 y a b c d=0) (H1 : read1 y a b c d=0)
    (H2 : read2 y a b c d=0) : False := by
  let a0 := a*c
  let a1 := a*(10*d)
  let a2 := (10*b)*c
  let a3 := (10*b)*(10*d)
  have E0 : row0 y a0 a1 a2 a3=0 := by
    rw [←row0_transfer y a b c d hy,H0,Semiring.mul_zero]
  have E1 : row1 y a0 a1 a2 a3=0 := by
    rw [←row1_transfer y a b c d hy,H1,Semiring.mul_zero]
  have E2 : row2 y a0 a1 a2 a3=0 := by
    rw [←row2_transfer y a b c d hy,H2,Semiring.mul_zero]
  have base : (75000:K)=2^3*3*5^5 := by grind only
  have nbase : (75000:K)≠0 := by
    rw [base]
    exact mul_ne_zero (mul_ne_zero (pow_ne_zero 3 two) three) (pow_ne_zero 5 five)
  have nt : (10:K)≠0 := by
    rw [show (10:K)=2*5 by grind only]
    exact mul_ne_zero two five
  obtain ⟨h01,h02,h03,h12,h13,h23⟩ := cofactor_crosses a0 a1 a2 a3
    (m00 y) (m01 y) (m02 y) (m03 y) (m10 y) (m11 y) (m12 y) (m13 y) (m20 y) (m21 y) (m22 y) (m23 y) E0 E1 E2

  have k01 : n1 y*a0=n0 y*a1 := by
    have z := congrArg (fun x : K => 49*x) h01
    simp only [minor0,minor1,← Semiring.mul_assoc,cof0_eval y hy,cof1_eval y hy] at z
    rw [Semiring.mul_assoc,Semiring.mul_assoc] at z
    exact cancel_left nbase z

  have k02 : n2 y*a0=n0 y*a2 := by
    have z := congrArg (fun x : K => 49*x) h02
    simp only [minor0,minor2,← Semiring.mul_assoc,cof0_eval y hy,cof2_eval y hy] at z
    rw [Semiring.mul_assoc,Semiring.mul_assoc] at z
    exact cancel_left nbase z

  have k03 : n3 y*a0=n0 y*a3 := by
    have z := congrArg (fun x : K => 49*x) h03
    simp only [minor0,minor3,← Semiring.mul_assoc,cof0_eval y hy,cof3_eval y hy] at z
    rw [Semiring.mul_assoc,Semiring.mul_assoc] at z
    exact cancel_left nbase z

  have k12 : n2 y*a1=n1 y*a2 := by
    have z := congrArg (fun x : K => 49*x) h12
    simp only [minor1,minor2,← Semiring.mul_assoc,cof1_eval y hy,cof2_eval y hy] at z
    rw [Semiring.mul_assoc,Semiring.mul_assoc] at z
    exact cancel_left nbase z

  have k13 : n3 y*a1=n1 y*a3 := by
    have z := congrArg (fun x : K => 49*x) h13
    simp only [minor1,minor3,← Semiring.mul_assoc,cof1_eval y hy,cof3_eval y hy] at z
    rw [Semiring.mul_assoc,Semiring.mul_assoc] at z
    exact cancel_left nbase z

  have k23 : n3 y*a2=n2 y*a3 := by
    have z := congrArg (fun x : K => 49*x) h23
    simp only [minor2,minor3,← Semiring.mul_assoc,cof2_eval y hy,cof3_eval y hy] at z
    rw [Semiring.mul_assoc,Semiring.mul_assoc] at z
    exact cancel_left nbase z

  have rank : a0*a3-a1*a2=0 := by
    dsimp [a0,a1,a2,a3]
    grind only
  obtain ⟨z0,z1,z2,z3⟩ := incompatible (n0 y) (n1 y) (n2 y) (n3 y) a0 a1 a2 a3
    (outer_ne y hy two three five seven guard) rank k01 k02 k03 k12 k13 k23
  rcases hf with ha|hb <;> rcases hg with hc|hd
  · exact (mul_ne_zero ha hc) z0
  · exact (mul_ne_zero ha (mul_ne_zero nt hd)) z1
  · exact (mul_ne_zero (mul_ne_zero nt hb) hc) z2
  · exact (mul_ne_zero (mul_ne_zero nt hb) (mul_ne_zero nt hd)) z3


/-- Literal value at y of x² times a coefficient triple. -/
def point (y : K) (p : K×K×K) : K :=
  p.1*y^2+p.2.1*y^3+p.2.2*y^4

/-- Clearing 120 in the local identity (I F)(y)=d_y F(y). -/
def localRead (y : K) (p : K×K×K) : K :=
  40*p.1*y^3+30*p.2.1*y^4+24*p.2.2*y^5-(5+42*rho y)*point y p

theorem coeffs_point (y a b : K) :
    point y (coeffs y a b)=10*y^4*b := by
  dsimp [point,coeffs,rho]
  grind only

theorem coeffs_localRead (y a b : K) : localRead y (coeffs y a b)=0 := by
  dsimp [localRead,point,coeffs,rho]
  grind only

theorem clock_ne_endpoints (y : K) (hy : clock y=0) : y≠0 ∧ y≠1 := by
  constructor
  · intro h
    subst y
    apply Field.zero_ne_one (α:=K)
    dsimp [clock,rho] at hy
    grind only
  · intro h
    subst y
    apply Field.zero_ne_one (α:=K)
    dsimp [clock,rho] at hy
    grind only

/-- The only extra characteristic needed to certify a nonzero clean
middle diagonal from the quartic clock equation. -/
theorem clean_diag_numerator_ne (y : K) (hy : clock y=0) (c137 : (137:K)≠0) :
    5+42*rho y≠0 := by
  intro z
  apply c137
  calc
    _ = 42*clock y-(42*rho y-19)*(5+42*rho y) := by dsimp [clock]; grind only
    _ = 0 := by rw [hy,z]; grind only

/-- The two local basis vectors span all profiles satisfying the
cleared primitive constraint, without exceptional determinant primes. -/
theorem exists_coeffs_of_localRead (y : K) (p : K×K×K)
    (hy : y≠0) (h2 : (2:K)≠0) (h5 : (5:K)≠0) (hp : localRead y p=0) :
    ∃ a b, p=coeffs y a b := by
  have h10 : (10:K)≠0 := by
    rw [show (10:K)=2*5 by grind only]
    exact mul_ne_zero h2 h5
  have hn : 10*y^4≠0 := mul_ne_zero h10 (pow_ne_zero 4 hy)
  let a := p.2.2*(5:K)⁻¹
  let b := point y p*(10*y^4)⁻¹
  let q := coeffs y a b
  have A : 5*a=p.2.2 := by
    dsimp [a]
    have z := Field.mul_inv_cancel h5
    calc
      _ = p.2.2 * ((5:K)*(5:K)⁻¹) := by grind only
      _ = _ := by rw [z]; grind only
  have B : 10*y^4*b=point y p := by
    dsimp [b]
    have z := Field.mul_inv_cancel hn
    calc
      _ = point y p * ((10*y^4)*(10*y^4)⁻¹) := by grind only
      _ = _ := by rw [z]; grind only
  have p2 : q.2.2=p.2.2 := A
  have pq : point y q=point y p := (coeffs_point y a b).trans B
  have hq : localRead y q=0 := coeffs_localRead y a b
  have diff1 : (10*y^4)*(p.2.1-q.2.1)=0 := by
    calc
      _ = (40*y-(5+42*rho y))*(point y p-point y q)
          -(localRead y p-localRead y q)-16*y^5*(p.2.2-q.2.2) := by
        dsimp only [point,localRead]
        grind only
      _ = 0 := by rw [pq,hp,hq,p2]; grind only
  have p1 : p.2.1=q.2.1 := by
    have z := (Field.of_mul_eq_zero diff1).resolve_left hn
    grind only
  have diff0 : y^2*(p.1-q.1)=0 := by
    change q.1*y^2+q.2.1*y^3+q.2.2*y^4=p.1*y^2+p.2.1*y^3+p.2.2*y^4 at pq
    rw [p1,p2] at pq
    grind only
  have p0 : p.1=q.1 := by
    have z := (Field.of_mul_eq_zero diff0).resolve_left (pow_ne_zero 2 hy)
    grind only
  exact ⟨a,b,Prod.ext p0 (Prod.ext p1 p2.symm)⟩

private theorem scale_point (y k b d : K) :
    4200*k*y^4*(1-y)^4*b*d=42*k*(10*y^4*b)*(10*(1-y)^4*d) := by
  grind only

/-- The scalar obstruction expressed on raw anchored quartic coefficient
triples (the second in the reflected monomial basis). Each read is
cleared by 2520 or 302400 as in the definitions above. -/
theorem no_anchored_quartics (y : K) (f g : K×K×K) (hy : clock y=0)
    (two : (2:K)≠0) (three : (3:K)≠0) (five : (5:K)≠0) (seven : (7:K)≠0)
    (guard : (62969:K)*(112249:K)≠0)
    (hf : f.1≠0 ∨ f.2.1≠0 ∨ f.2.2≠0) (hg : g.1≠0 ∨ g.2.1≠0 ∨ g.2.2≠0)
    (localF : localRead y f=0) (localG : localRead (1-y) g=0)
    (H0 : low f g-42*(7+42*rho y)*point y f*point (1-y) g=0)
    (H1 : high f g-y*low f g=0)
    (H2 : prim f g-(5+42*rho y)*low f g=0) : False := by
  have ends := clock_ne_endpoints y hy
  have ny : 1-y≠0 := by
    intro z
    apply ends.2
    grind only
  obtain ⟨a,b,fa⟩ := exists_coeffs_of_localRead y f ends.1 two five localF
  obtain ⟨c,d,ga⟩ := exists_coeffs_of_localRead (1-y) g ny two five localG
  have nz (x u v : K) (live : (coeffs x u v).1≠0 ∨
      (coeffs x u v).2.1≠0 ∨ (coeffs x u v).2.2≠0) : u≠0 ∨ v≠0 := by
    dsimp only [coeffs] at live
    grind only
  rw [fa] at hf
  rw [ga] at hg
  rw [fa,ga] at H0 H1 H2
  have H0' : read0 y a b c d=0 := by
    rw [coeffs_point,coeffs_point] at H0
    unfold read0
    exact (show _=0 by rw [scale_point]; exact H0)
  exact no_clean_scalar_reads y a b c d hy two three five seven guard
    (nz y a b hf) (nz (1-y) c d hg) H0' H1 H2

end RKResearch.Certified.Graded.EightDirtyCleanScalar
