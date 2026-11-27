import Lean

/-!
Scalar gates for ERK11 sharp-prefix classification, independent of mathlib.
The companion note supplies the rooted graded and rank interpretations.
-/
namespace RKResearch.ERK11JacobiPrefixGate
open Lean.Grind
variable {K : Type} [Field K]

private theorem nzMul {a b : K} (ha : a ≠ 0) (hb : b ≠ 0) : a*b ≠ 0 :=
  fun h => hb ((Field.of_mul_eq_zero h).resolve_left ha)

private theorem cancelR {x y z : K} (nz : z ≠ 0) (h : x*z=y*z) : x=y := by
  have p : (x-y)*z=0 := by grind
  exact AddCommGroup.sub_eq_zero_iff.mp ((Field.of_mul_eq_zero p).resolve_right nz)

private theorem endpointCompare {a h d e j k : K}
    (u : d ≠ 0) (v : e ≠ 0) (ne : j-k ≠ 0)
    (p : (j*a-h)*d=0) (q : (k*a-h)*e=0) : a=0 ∧ h=0 := by
  have p' := (Field.of_mul_eq_zero p).resolve_right u
  have q' := (Field.of_mul_eq_zero q).resolve_right v
  have z : (j-k)*a=0 := by grind
  have za := (Field.of_mul_eq_zero z).resolve_left ne
  exact ⟨za, by rw [za,Semiring.mul_zero] at p'; grind⟩

/-- In the one-mode branch the decoder terminal column at reflected
clock zero has only a first positive moment. The two outer no-pair
guards ensure that the nonzero read is not confined to a single shift. -/
theorem terminalEndpoint (a h d1 d2 d3 d4 : K)
    (n2 : (2:K) ≠ 0) (n3 : (3:K) ≠ 0)
    (n12 : d1 ≠ 0 ∨ d2 ≠ 0) (n34 : d3 ≠ 0 ∨ d4 ≠ 0)
    (e1 : (2*a-h)*d1=0) (e2 : (3*a-h)*d2=0)
    (e3 : (4*a-h)*d3=0) (e4 : (5*a-h)*d4=0) :
    a=0 ∧ h=0 := by
  rcases n12 with u|u <;> rcases n34 with v|v
  · exact endpointCompare u v (by grind) e1 e3
  · exact endpointCompare u v (by grind) e1 e4
  · exact endpointCompare u v (by grind) e2 e3
  · exact endpointCompare u v (by grind) e2 e4

private theorem cubicFromPencil (y a h d1 d2 d3 d4 : K)
    (c2 : (3*a-h)*d2=(y*a)*d1)
    (c3 : (4*a-h)*d3=(y*a)*d2)
    (c4 : (5*a-h)*d4=(y*a)*d3) :
    (y*a)*(2*d2*d2*d4-d1*d3*d4-d2*d3*d3)=0 := by
  calc
    _ = ((y*a)*d2)*(2*d2*d4) - ((y*a)*d1)*(d3*d4) -
          ((y*a)*d3)*(d2*d3) := by grind
    _ = (((4*a-h)*d3)*(2*d2*d4)) - (((3*a-h)*d2)*(d3*d4)) -
          (((5*a-h)*d4)*(d2*d3)) := by rw [←c2,←c3,←c4]
    _ = 0 := by grind

/-- Exact denominator-cleared polynomial conditions for the other
possible terminal clock, under the one-mode prefix moment pencil. -/
theorem terminalOther (y a h d1 d2 d3 d4 p1 p2 p3 p4 p5 : K)
    (ny : y ≠ 0) (np : ¬(p1=0 ∧ p2=0 ∧ p3=0 ∧ p4=0 ∧ p5=0))
    (n12 : d1 ≠ 0 ∨ d2 ≠ 0)
    (n34 : d3 ≠ 0 ∨ d4 ≠ 0)
    (u1 : p2=a*d1) (u2 : p3=a*d2) (u3 : p4=a*d3) (u4 : p5=a*d4)
    (e1 : 2*p2-y*p1=h*d1) (e2 : 3*p3-y*p2=h*d2)
    (e3 : 4*p4-y*p3=h*d3) (e4 : 5*p5-y*p4=h*d4) :
    a ≠ 0 ∧ d2 ≠ 0 ∧ d3 ≠ 0 ∧ d4 ≠ 0 ∧
    (d3*d3-d2*d4) ≠ 0 ∧
    y*(d3*d3-d2*d4)=d3*d4 ∧
    2*d2*d2*d4-d1*d3*d4-d2*d3*d3=0 := by
  have na : a ≠ 0 := by
    intro az
    have zp2 : p2=0 := by rw [u1,az,Semiring.zero_mul]
    have zp3 : p3=0 := by rw [u2,az,Semiring.zero_mul]
    have zp4 : p4=0 := by rw [u3,az,Semiring.zero_mul]
    have zp5 : p5=0 := by rw [u4,az,Semiring.zero_mul]
    have hz : h=0 := by
      rcases n34 with nz|nz
      · have eq : h*d3=0 := by grind
        exact (Field.of_mul_eq_zero eq).resolve_right nz
      · have eq : h*d4=0 := by grind
        exact (Field.of_mul_eq_zero eq).resolve_right nz
    have yz : y*p1=0 := by grind
    exact np ⟨(Field.of_mul_eq_zero yz).resolve_left ny,zp2,zp3,zp4,zp5⟩
  have c2 : (3*a-h)*d2=(y*a)*d1 := by grind
  have c3 : (4*a-h)*d3=(y*a)*d2 := by grind
  have c4 : (5*a-h)*d4=(y*a)*d3 := by grind
  have nya := nzMul ny na
  have nd2 : d2 ≠ 0 := by
    intro zz
    have h0 : (y*a)*d1=0 := by grind
    have zz1 := (Field.of_mul_eq_zero h0).resolve_left nya
    exact n12.elim (fun nz => nz zz1) (fun nz => nz zz)
  have nd3 : d3 ≠ 0 := by
    intro zz
    have h0 : (y*a)*d2=0 := by grind
    exact (Field.of_mul_eq_zero h0).elim nya nd2
  have nd4 : d4 ≠ 0 := by
    intro zz
    have h0 : (y*a)*d3=0 := by grind
    exact (Field.of_mul_eq_zero h0).elim nya nd3
  have equ : y*(d3*d3-d2*d4)=d3*d4 := by
    apply cancelR (z:=a) na
    have k := congrArg (fun z => z*d3) c4
    have l := congrArg (fun z => z*d4) c3
    grind
  have nonzero : (d3*d3-d2*d4) ≠ 0 := by
    intro z
    rw [z,Semiring.mul_zero] at equ
    exact nzMul nd3 nd4 equ.symm
  have c := cubicFromPencil y a h d1 d2 d3 d4 c2 c3 c4
  exact ⟨na,nd2,nd3,nd4,nonzero,equ,(Field.of_mul_eq_zero c).resolve_left nya⟩

/-- A terminal coordinate cannot enter one degree earlier: the two
unary ladders would make the positive charges geometric, contradicting
the clock transport at two adjacent degrees. -/
theorem noEarlyTerminal (a b h y d1 d2 d3 : K) (na : a ≠ 0)
    (n12 : d1 ≠ 0 ∨ d2 ≠ 0) (n23 : d2 ≠ 0 ∨ d3 ≠ 0)
    (u1 : a*d2=b*d1) (u2 : a*d3=b*d2)
    (c2 : (3*a-h)*d2=y*a*d1) (c3 : (4*a-h)*d3=y*a*d2) : False := by
  have nb : b ≠ 0 := by
    intro bz
    have h2 : a*d2=0 := by rw [u1,bz,Semiring.zero_mul]
    have h3 : a*d3=0 := by rw [u2,bz,Semiring.zero_mul]
    exact n23.elim (fun ne => ne ((Field.of_mul_eq_zero h2).resolve_left na))
      (fun ne => ne ((Field.of_mul_eq_zero h3).resolve_left na))
  have nd2 : d2 ≠ 0 := by
    intro zz
    have h1 : b*d1=0 := by rw [←u1,zz,Semiring.mul_zero]
    exact n12.elim (fun ne => ne ((Field.of_mul_eq_zero h1).resolve_left nb))
      (fun ne => ne zz)
  have nd3 : d3 ≠ 0 := by
    intro zz
    have h2 : b*d2=0 := by rw [←u2,zz,Semiring.mul_zero]
    exact (Field.of_mul_eq_zero h2).elim nb nd2
  have g : a*(d1*d3-d2*d2)=0 := by
    have q := congrArg (fun z => z*d1) u2
    have r := congrArg (fun z => z*d2) u1
    grind
  have g' := (Field.of_mul_eq_zero g).resolve_left na
  have nn : a*(d2*d3)=0 := by
    have q := congrArg (fun z => z*d2) c3
    have r := congrArg (fun z => z*d3) c2
    have s := congrArg (fun z => (y*a)*z) g'
    grind
  exact nzMul na (nzMul nd2 nd3) nn

/-- The two no-consecutive hypotheses force rank at least two in
the positive read test at grade seven. It suffices to exhibit one
of these minors from the three columns. -/
theorem gradeSevenMinor (d1 d2 d3 d4 : K)
    (n2 : (2:K) ≠ 0) (n12 : d1 ≠ 0 ∨ d2 ≠ 0)
    (n23 : d2 ≠ 0 ∨ d3 ≠ 0) (n34 : d3 ≠ 0 ∨ d4 ≠ 0) :
    d2*d3 ≠ 0 ∨ 2*d2*d4 ≠ 0 ∨ d3*d4 ≠ 0 ∨ d1*d3-d2*d2 ≠ 0 := by
  by_cases h2 : d2=0
  · by_cases h4 : d4=0
    · have h1 := n12.resolve_right (fun ne => ne h2)
      have h3 := n23.resolve_left (fun ne => ne h2)
      right; right; right
      have nz := nzMul h1 h3
      grind
    · exact Or.inr (Or.inr (Or.inl (nzMul (n23.resolve_left (fun ne => ne h2)) h4)))
  · rcases n34 with h3|h4
    · exact Or.inl (nzMul h2 h3)
    · exact Or.inr (Or.inl (nzMul (nzMul n2 h2) h4))

/-- When the three grade-seven read columns have rank exactly two,
a zero in their charge vector has the only surviving alternating shape. -/
theorem cubicPattern (d1 d2 d3 d4 : K) (n2 : (2:K) ≠ 0)
    (n12 : d1 ≠ 0 ∨ d2 ≠ 0) (n23 : d2 ≠ 0 ∨ d3 ≠ 0)
    (n34 : d3 ≠ 0 ∨ d4 ≠ 0) (g : 2*d2*d2*d4-d1*d3*d4-d2*d3*d3=0) :
    (d1 ≠ 0 ∧ d2=0 ∧ d3 ≠ 0 ∧ d4=0) ∨ (d2 ≠ 0 ∧ d3 ≠ 0 ∧ d4 ≠ 0) := by
  by_cases z2 : d2=0
  · have e1 := n12.resolve_right (fun ne => ne z2)
    have e3 := n23.resolve_left (fun ne => ne z2)
    have k : (d1*d3)*d4=0 := by grind
    exact Or.inl ⟨e1,z2,e3,(Field.of_mul_eq_zero k).resolve_left (nzMul e1 e3)⟩
  · have e3 : d3 ≠ 0 := by
      intro z3
      have e4 := n34.resolve_left (fun ne => ne z3)
      have k : ((2:K)*d2*d2)*d4=0 := by grind
      exact nzMul (nzMul (nzMul n2 z2) z2) e4 k
    have e4 : d4 ≠ 0 := by
      intro z4
      have k : d2*(d3*d3)=0 := by grind
      exact nzMul z2 (nzMul e3 e3) k
    exact Or.inr ⟨z2,e3,e4⟩

/-- Physical four-slot no-top argument with a nonendpoint last
clock; the non-overlap branch uses only the first two outgoing reads. -/
theorem fourSlotNoTop (r2 k2 k3 U b2 b3 y0 y1 y2 y3 p q : K)
    (ny3 : y3 ≠ 0) (n3 : (3:K) ≠ 0) (top : r2*k2=0)
    (total : U=b2*k2+b3*k3) (late : y2*b2*k2+y3*b3*k3=0)
    (head : r2=0 → y0*U=0 ∧ y1*U=0 ∧ y0*p+y1*q=3*U) : U=0 := by
  rcases Field.of_mul_eq_zero top with z|z
  · obtain ⟨e0,e1,e⟩ := head z
    by_cases zz : U=0
    · exact zz
    · have z0 := (Field.of_mul_eq_zero e0).resolve_right zz
      have z1 := (Field.of_mul_eq_zero e1).resolve_right zz
      have e3 : (3:K)*U=0 := by grind
      exact False.elim (nzMul n3 zz e3)
  · have z3 : y3*(b3*k3)=0 := by grind
    have w := (Field.of_mul_eq_zero z3).resolve_left ny3
    grind

/-- Top and penultimate visible on four slots, with actual mixed
two-clock words, force the initial two reflected clocks to tie. -/
theorem fourSlotTop (y0 y1 yLast T U V s0 s1 w0 w1 : K)
    (ny : yLast ≠ 0) (nt : T ≠ 0) (nu : U ≠ 0)
    (hi0 : y0*U+s0*T=4*T) (hi1 : y1*U+s1*T=3*T)
    (low0 : y0*V+s0*U+w0*T=3*U) (low1 : y1*V+s1*U+w1*T=2*U)
    (mix0 : w0*(yLast*T)=0) (mix1 : w1*(yLast*T)=0)
    (tie : y0=y1 → s0=0) :
    y0=y1 ∧ y0 ≠ 0 ∧ y0*U=4*T ∧ y0*V=3*U := by
  have a := (Field.of_mul_eq_zero mix0).resolve_right (nzMul ny nt)
  have b := (Field.of_mul_eq_zero mix1).resolve_right (nzMul ny nt)
  have e0 : y0*(U*U-T*V)=U*T := by
    have v1 := congrArg (fun z => z*U) hi0
    have v2 := congrArg (fun z => z*T) low0
    grind
  have e1 : y1*(U*U-T*V)=U*T := by
    have v1 := congrArg (fun z => z*U) hi1
    have v2 := congrArg (fun z => z*T) low1
    grind
  have nz : U*U-T*V ≠ 0 := by
    intro zz
    rw [zz,Semiring.mul_zero] at e0
    exact nzMul nu nt e0.symm
  have eq := cancelR nz (e0.trans e1.symm)
  have n0 : y0 ≠ 0 := by
    intro zz
    rw [zz,Semiring.zero_mul] at e0
    exact nzMul nu nt e0.symm
  have r := tie eq
  exact ⟨eq,n0,by grind,by grind⟩

/-- The remaining charge ratio is forced without dividing by a clock. -/
theorem geometricThird (z d1 d2 d3 d4 : K) (n3 : d3 ≠ 0) (n4 : d4 ≠ 0)
    (t2 : z*d2=3*d3) (t3 : z*d3=4*d4)
    (g : 2*d2*d2*d4-d1*d3*d4-d2*d3*d3=0) :
    z*d1=2*d2 := by
  apply cancelR (z:=d3*d4) (nzMul n3 n4)
  have t := congrArg (fun x => z*x) g
  have k := congrArg (fun x => x*(2*d2*d4)) t2
  have l := congrArg (fun x => x*(d2*d3)) t3
  grind

/-- The second clock-local order-five provider cannot follow a seed
with only one nonorigin available model read in degree four. -/
theorem secondProvider (x a b : K)
    (h2 : x^2=a+2*b) (h3 : x^3=a+3*b) (h4 : x^4=a+4*b) :
    x*x*(x-1)*(x-1)=0 := by grind

/-- Exact symbolic Bézout gate with paid guard 2. -/
def R4 (x : K) : K := 42*x^4-84*x^3+56*x^2-14*x+1
def R5 (x : K) : K := 132*x^5-330*x^4+300*x^3-120*x^2+20*x-1

theorem jacobiBezout (x : K) :
    (4620*x^4-9240*x^3+6111*x^2-1491*x+100)*R4 x +
    (-1470*x^3+2205*x^2-931*x+98)*R5 x = 2 := by
  unfold R4 R5
  grind

private def fact : Nat → Nat
  | 0 => 1
  | k+1 => (k+1) * fact k

private def ell (m : Nat) (coeffs : List Rat) : Rat :=
  (coeffs.zipIdx.map fun (q,i) => q*((fact i : Nat) : Rat) / ((fact (m+i+1) : Nat) : Rat)).foldl (·+·) 0

private def p4 : List Rat := [0,1,-14,56,-84,42]
private def p5 : List Rat := [0,-1,20,-120,300,-330,132]
private def pEnd : List Rat := [0,1,-16,72,-120,66]

/-- Mean and positive shifted moment constants used in the actual
Jacobi-atom transfer and the unique terminal-1 decoder line. -/
theorem jacobiMomentValues :
    ((List.range 5).map fun m => ell m p4)=[1/30,0,0,0,0] ∧
    ((List.range 5).map fun m => ell m p5)=[1/42,0,0,0,0] ∧
    ((List.range 6).map fun m => ell m pEnd)=[1/6,1/210,0,0,0,0] := by
  decide +kernel

end RKResearch.ERK11JacobiPrefixGate
#print axioms RKResearch.ERK11JacobiPrefixGate.terminalEndpoint
#print axioms RKResearch.ERK11JacobiPrefixGate.terminalOther
#print axioms RKResearch.ERK11JacobiPrefixGate.noEarlyTerminal
#print axioms RKResearch.ERK11JacobiPrefixGate.gradeSevenMinor
#print axioms RKResearch.ERK11JacobiPrefixGate.jacobiBezout
#print axioms RKResearch.ERK11JacobiPrefixGate.jacobiMomentValues
#print axioms RKResearch.ERK11JacobiPrefixGate.cubicPattern
#print axioms RKResearch.ERK11JacobiPrefixGate.fourSlotNoTop
#print axioms RKResearch.ERK11JacobiPrefixGate.fourSlotTop
#print axioms RKResearch.ERK11JacobiPrefixGate.geometricThird
#print axioms RKResearch.ERK11JacobiPrefixGate.secondProvider
