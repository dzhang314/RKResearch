module

public import Init

@[expose] public section

namespace RKResearch.Certified.ERK10GradeCore

/-! Core-only arithmetic for the actual raw-word to filtered-grade bridge.
Nodal parameters and trial inverses are formal variables; the stock
kernel checks polynomial coefficients, not a tableau order theorem. -/

set_option maxHeartbeats 0
set_option maxRecDepth 50000

abbrev Term := Nat × Int
structure P where
  xs : List Term
  degreeBound : Nat

def add (a b : P) : P := ⟨a.xs++b.xs,max a.degreeBound b.degreeBound⟩
def neg (a : P) : P := ⟨a.xs.map (fun t => (t.1,-t.2)),a.degreeBound⟩
def mul (a b : P) : P :=
  ⟨a.xs.flatMap (fun t => b.xs.map (fun u => (t.1+u.1,t.2*u.2))),
    a.degreeBound+b.degreeBound⟩

def con (z : Int) : P := ⟨(if z=0 then [] else [(0,z)]),0⟩
def v (i : Nat) : P := ⟨[(64^i,1)],1⟩
instance : Add P := ⟨add⟩
instance : Neg P := ⟨neg⟩
instance : Sub P := ⟨fun a b => a + -b⟩
instance : Mul P := ⟨mul⟩
instance (n : Nat) : OfNat P n := ⟨con (.ofNat n)⟩
def pow (a : P) : Nat → P
  | 0 => 1
  | n+1 => pow a n*a
instance : Pow P Nat := ⟨pow⟩

def packExp (es : List Nat) : Nat := es.foldr (fun a b => a+64*b) 0
def sparse (lhs : List (List Nat × Int)) : P :=
  ⟨lhs.map (fun b => (packExp b.1,b.2)),
    lhs.foldl (fun a b => max a (b.1.foldl Nat.add 0)) 0⟩

def merge : Nat → List Term → List Term → List Term
  | 0, a, b => a++b
  | _+1, [], b => b
  | _+1, a, [] => a
  | n+1, x::a, y::b =>
    if x.1≤y.1 then x::merge n a (y::b) else y::merge n (x::a) b

def mergePairs : List (List Term) → List (List Term)
  | a::b::xs => merge (a.length+b.length) a b::mergePairs xs
  | xs => xs

def sortRuns : Nat → List (List Term) → List Term
  | 0, xs => xs.flatten
  | _+1, [] => []
  | _+1, [a] => a
  | n+1, a::b::xs => sortRuns n (mergePairs (a::b::xs))

def zeroSorted (e : Nat) (a : Int) : List Term → Bool
  | [] => a == 0
  | (f,b)::xs =>
    if e=f then zeroSorted e (a+b) xs
    else (a == 0) && zeroSorted f b xs

/-- A total-degree bound below the radix prevents all exponent carries. -/
def zero (a : P) : Bool :=
  decide (a.degreeBound<64) &&
    (match sortRuns a.xs.length (a.xs.map fun t => [t]) with
     | [] => true
     | (e,b)::xs => zeroSorted e b xs)



def c : P := v 0
def d : P := v 1
def s : P := v 2
def t : P := v 3
def k : P := v 4
def y : P := v 5
def i2 : P := v 6
def n0 : P := v 7
def r : P := v 8
def q : P := v 9

def M : P := y^2*(y-c)^2
def L : P := y^3-(3*c*y^2-c^2*y)*i2
def kappaGate : P := 2*k*(t-2*s)-t
def delta : P := 2*k*t
def n1 : P := -2-4*k*(s-t)
def Gnom : P := (y-d)*L
def Zdef : P := -(y-c)*(n0+n1*y)
def Gdef : P := (y-d)*(2-t)*(y-c)
def lowerA : P :=
  (2*c-d-3*c*i2)*y^3+(c^2*i2+3*c*d*i2-c^2)*y^2-c^2*d*i2*y
def lowerB : P :=
  (-(2-t)*(d+c)-c*n1+n0)*y+(2-t)*d*c-c*n0

def monicM : P := M-(y^4-2*c*y^3+c^2*y^2)
def nominalDifference : P := Gnom-M-lowerA
def primitiveObserver : P :=
  4*L-(4*y^3-6*c*y^2+2*c^2*y)+2*(3*c*y^2-c^2*y)*(2*i2-1)
def paidDegreeTwo : P :=
  Gdef-Zdef-lowerB-delta*y^2-kappaGate*y^2

/-- Multiplying the actual half coefficient by its paid denominator first. -/
def actualL2 : P := 2*y^3-3*c*y^2+c^2*y
/-- 120 times the primitive of y²(y-c)² from zero. -/
def primM120 : P := 24*y^5-60*c*y^4+40*c^2*y^3
/-- 120 times the primitive of (y-d)*L from zero. -/
def primG120 : P :=
  24*y^5-(30*d+45*c)*y^4+(20*c^2+60*c*d)*y^3-30*c^2*d*y^2
def primitiveG : P :=
  4*primG120-(120*(y-d)*M-primM120)

def opKernel (x : P) : P := x*(x-r)*(x-t)
def opF2_3 (x : P) : P := 3*x^2-2*r*x
def geom0 : P := 3*s-2*r+t
def geom1 : P := t*q-r*s
def geom : P := 2*q*r-3*q*s-r*s
def alphaTop : P := q^2*(3*s-2*q)

def openingGeometry : P := geom-(geom1-q*geom0)
def openingCubic : P :=
  s^3*opKernel q-alphaTop*opKernel s-
     q*s*(q-s)*(2*q*r-2*q*s-r*s)*geom0-
     q*s*(q-s)*(2*r-3*s)*geom
def openingQuadratic : P :=
  s^3*opF2_3 q-alphaTop*opF2_3 s+2*q*s*(q-s)*geom

def jacobi : List Int := [0,1,(-14),56,(-84),42]
def jacobiTimesOneMinusY : List Int := [0,1,(-15),70,(-140),126,(-42)]
def scaledJacobiMoment (j : Nat) : Int :=
  ((List.range jacobiTimesOneMinusY.length).map fun k =>
    jacobiTimesOneMinusY[k]?.getD 0 * Int.ofNat (2520 / (k+j+1))).sum
def actualJacobi : Int := jacobi.foldr (fun a b => a+2*b) 0

def y29 : List Int := [0,11,20,2,2,26,27,7,6,22,15]
def w29 : List Int := [2,16,1,5,13,7,1,26,9,4,0]
def bushResidue : Int :=
  (11*((List.zipWith (fun y w => ((1-y)^10)*w) y29 w29).sum)-1)%29

theorem monic_M : zero monicM=true := by decide +kernel
theorem nominal_difference : zero nominalDifference=true := by decide +kernel
theorem primitive_observer : zero primitiveObserver=true := by decide +kernel
theorem paid_degree_two : zero paidDegreeTwo=true := by decide +kernel
theorem primitive_G : zero primitiveG=true := by decide +kernel
theorem opening_geometry : zero openingGeometry=true := by decide +kernel
theorem opening_cubic : zero openingCubic=true := by decide +kernel
theorem opening_quadratic : zero openingQuadratic=true := by decide +kernel
theorem jacobi_moment_scaled : ∀ j : Fin 4, scaledJacobiMoment j.val=0 :=
  by decide +kernel
theorem jacobi_scale_paid : 3628800 % 2520 = 0 := by decide +kernel
theorem jacobi_residue : actualJacobi % 29 = 17 := by decide +kernel
theorem delta_residue : (2*16*16 : Nat)%29 = 19 := by decide +kernel
theorem bush_failure_residue : bushResidue=10 := by decide +kernel

/-- The attach of a child to a rest can have a nonlinear error only in
these three cases through order ten. -/
theorem nonlinear_attach_cases (m n : Nat) (hm : 4 ≤ m) (hn : 5 ≤ n)
    (ht : m+n ≤ 10) :
    (m=4 ∧ n=5) ∨ (m=4 ∧ n=6) ∨ (m=5 ∧ n=5) := by omega

theorem edge_payment_budget (m : Nat) (hm : 5 ≤ m) (hM : m ≤ 9) :
    9-m ≤ 4 ∧ (9-m)+(m-1)=8 := by omega

theorem attach_grade_budget (m n : Nat) (hm : 1 ≤ m) (hn : 1 ≤ n)
    (ht : m+n ≤ 10) :
    (10-(m+n))+m = 10-n ∧ (10-(m+n))+(n-1)=9-m := by omega

end RKResearch.Certified.ERK10GradeCore

#print axioms RKResearch.Certified.ERK10GradeCore.monic_M
#print axioms RKResearch.Certified.ERK10GradeCore.nominal_difference
#print axioms RKResearch.Certified.ERK10GradeCore.primitive_observer
#print axioms RKResearch.Certified.ERK10GradeCore.paid_degree_two
#print axioms RKResearch.Certified.ERK10GradeCore.primitive_G
#print axioms RKResearch.Certified.ERK10GradeCore.opening_geometry
#print axioms RKResearch.Certified.ERK10GradeCore.opening_cubic
#print axioms RKResearch.Certified.ERK10GradeCore.opening_quadratic
#print axioms RKResearch.Certified.ERK10GradeCore.jacobi_moment_scaled
#print axioms RKResearch.Certified.ERK10GradeCore.jacobi_scale_paid
#print axioms RKResearch.Certified.ERK10GradeCore.jacobi_residue
#print axioms RKResearch.Certified.ERK10GradeCore.delta_residue
#print axioms RKResearch.Certified.ERK10GradeCore.bush_failure_residue
#print axioms RKResearch.Certified.ERK10GradeCore.nonlinear_attach_cases
#print axioms RKResearch.Certified.ERK10GradeCore.edge_payment_budget
#print axioms RKResearch.Certified.ERK10GradeCore.attach_grade_budget
