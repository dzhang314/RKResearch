import Lean

/-! Closed integer arithmetic for the balanced-half seam determinant census.
The physical rooted and interval-soundness bridges are separate. -/
namespace RKResearch.ERK10BalancedSeamDeterminants

def unit : Int := 1461501637330902918203684832716283019655932542976

structure Iv where
  lo : Int
  hi : Int

def ofInt (z : Int) : Iv := ⟨z*unit,z*unit⟩

instance (n : Nat) : OfNat Iv n := ⟨ofInt n⟩
instance : Add Iv := ⟨fun a b => ⟨a.lo+b.lo,a.hi+b.hi⟩⟩
instance : Neg Iv := ⟨fun a => ⟨-a.hi,-a.lo⟩⟩
instance : Sub Iv := ⟨fun a b => a+(-b)⟩

def floorDiv (a b : Int) : Int := if b < 0 then (-a)/(-b) else a/b
def ceilDiv (a b : Int) : Int := -(floorDiv (-a) b)

instance : Mul Iv := ⟨fun a b =>
  let aa := a.lo*b.lo
  let bb := a.lo*b.hi
  let cc := a.hi*b.lo
  let dd := a.hi*b.hi
  ⟨floorDiv (min (min aa bb) (min cc dd)) unit,
    ceilDiv (max (max aa bb) (max cc dd)) unit⟩⟩

def scale (a : Iv) (z : Int) : Iv := ofInt z*a

def divNat (a : Iv) (n : Nat) : Iv := ⟨floorDiv a.lo n,ceilDiv a.hi n⟩

def inv (a : Iv) : Option Iv :=
  if a.hi < 0 ∨ 0 < a.lo then
    some ⟨floorDiv (unit*unit) a.hi,ceilDiv (unit*unit) a.lo⟩
  else none

def divide (a b : Iv) : Option Iv := do
  let c ← inv b
  return a*c

-- Coefficients q0,q1,q2 of the monic cubic q; g0,g1 of the monic quadratic.
def lift (q0 q1 q2 g0 g1 : Iv) : Option (List Iv × List Iv) := do
  let a := q0-g0*q2+g0*g1
  let c := q1-g1*q2+g1*g1-g0
  let b := -(g0*c)
  let d := a-g1*c
  let idet ← inv (a*d-b*c)
  let prod := fun r0 r1 =>
    [q0*r0,q1*r0+q0*r1,q2*r0+q1*r1,r0+q2*r1,r1]
  return (prod (d*idet) ((-c)*idet),prod ((-b)*idet) (a*idet))

def moment (l r : List Iv) : Iv :=
  l.zipIdx.foldl (fun v (a,i) =>
    r.zipIdx.foldl (fun w (b,j) => w+divNat (a*b) ((i+1)*(i+j+2))) v) 0

def determinant (u w y v : Iv) : Option Iv := do
  let bar := 1-v
  let h ← divide (scale (u*u) 3-scale (bar*bar) 3+scale bar 8-6)
    (scale (u+bar) 4-6)
  let g0 := divNat (scale (h*u) 4-scale (u*u) 3) 6
  let g1 := -h
  let l ← lift 0 (u*w) (-(u+w)) g0 g1
  let r ← lift (-(y*v)) (y+v+y*v) (-(1+y+v)) g0 g1
  let testL := [0,-(g0*u),g0-g1*u,g1-u,1]
  let testR := [g0*v,g1*v-g0*(v+1),v-g1*(v+1)+g0,g1-(v+1),1]
  let a := moment l.1 testR
  let b := moment l.2 testR
  let c := moment testL r.1
  let d := moment testL r.2
  return a*d-b*c


def root₁ : Iv :=
  ⟨171686014379632978896358265233598292354350969495,
   171686014379632978896358265233598292354350969500⟩
def root₂ : Iv :=
  ⟨522317654488031844978711301023922741443185858476,
   522317654488031844978711301023922741443185858479⟩
def root₃ : Iv :=
  ⟨939183982842871073224973531692360278212746684497,
   939183982842871073224973531692360278212746684500⟩
def root₄ : Iv :=
  ⟨1289815622951269939307326567482684727301581573476,
   1289815622951269939307326567482684727301581573481⟩

def lobattoNumerator (z : Int) : Int :=
  42*z^4-84*z^3*unit+56*z^2*unit^2-14*z*unit^3+unit^4

theorem rootBrackets :
    0 < root₁.lo ∧ root₁.lo < root₁.hi ∧ root₁.hi < root₂.lo ∧
    root₂.lo < root₂.hi ∧ root₂.hi < root₃.lo ∧ root₃.lo < root₃.hi ∧
    root₃.hi < root₄.lo ∧ root₄.lo < root₄.hi ∧ root₄.hi < unit ∧
    0 < lobattoNumerator root₁.lo ∧ lobattoNumerator root₁.hi < 0 ∧
    lobattoNumerator root₂.lo < 0 ∧ 0 < lobattoNumerator root₂.hi ∧
    0 < lobattoNumerator root₃.lo ∧ lobattoNumerator root₃.hi < 0 ∧
    lobattoNumerator root₄.lo < 0 ∧ 0 < lobattoNumerator root₄.hi := by decide

def detSign (positive : Bool) (u w y v : Iv) : Bool :=
  match determinant u w y v with
  | none => false
  | some d => if positive then decide (0 < d.lo) else decide (d.hi < 0)

set_option maxHeartbeats 0
set_option maxRecDepth 100000

theorem det1234 : detSign true root₁ root₂ root₃ root₄ = true := by decide
theorem det1243 : detSign true root₁ root₂ root₄ root₃ = true := by decide
theorem det1324 : detSign true root₁ root₃ root₂ root₄ = true := by decide
theorem det1342 : detSign false root₁ root₃ root₄ root₂ = true := by decide
theorem det1423 : detSign false root₁ root₄ root₂ root₃ = true := by decide
theorem det1432 : detSign false root₁ root₄ root₃ root₂ = true := by decide
theorem det2134 : detSign true root₂ root₁ root₃ root₄ = true := by decide
theorem det2143 : detSign true root₂ root₁ root₄ root₃ = true := by decide
theorem det2314 : detSign false root₂ root₃ root₁ root₄ = true := by decide
theorem det2341 : detSign true root₂ root₃ root₄ root₁ = true := by decide
theorem det2413 : detSign true root₂ root₄ root₁ root₃ = true := by decide
theorem det2431 : detSign true root₂ root₄ root₃ root₁ = true := by decide
theorem det3124 : detSign false root₃ root₁ root₂ root₄ = true := by decide
theorem det3142 : detSign false root₃ root₁ root₄ root₂ = true := by decide
theorem det3214 : detSign false root₃ root₂ root₁ root₄ = true := by decide
theorem det3241 : detSign false root₃ root₂ root₄ root₁ = true := by decide
theorem det3412 : detSign false root₃ root₄ root₁ root₂ = true := by decide
theorem det3421 : detSign true root₃ root₄ root₂ root₁ = true := by decide
theorem det4123 : detSign true root₄ root₁ root₂ root₃ = true := by decide
theorem det4132 : detSign false root₄ root₁ root₃ root₂ = true := by decide
theorem det4213 : detSign true root₄ root₂ root₁ root₃ = true := by decide
theorem det4231 : detSign true root₄ root₂ root₃ root₁ = true := by decide
theorem det4312 : detSign true root₄ root₃ root₁ root₂ = true := by decide
theorem det4321 : detSign true root₄ root₃ root₂ root₁ = true := by decide

end RKResearch.ERK10BalancedSeamDeterminants
#print axioms RKResearch.ERK10BalancedSeamDeterminants.rootBrackets
#print axioms RKResearch.ERK10BalancedSeamDeterminants.det1234
#print axioms RKResearch.ERK10BalancedSeamDeterminants.det1243
#print axioms RKResearch.ERK10BalancedSeamDeterminants.det1324
#print axioms RKResearch.ERK10BalancedSeamDeterminants.det1342
#print axioms RKResearch.ERK10BalancedSeamDeterminants.det1423
#print axioms RKResearch.ERK10BalancedSeamDeterminants.det1432
#print axioms RKResearch.ERK10BalancedSeamDeterminants.det2134
#print axioms RKResearch.ERK10BalancedSeamDeterminants.det2143
#print axioms RKResearch.ERK10BalancedSeamDeterminants.det2314
#print axioms RKResearch.ERK10BalancedSeamDeterminants.det2341
#print axioms RKResearch.ERK10BalancedSeamDeterminants.det2413
#print axioms RKResearch.ERK10BalancedSeamDeterminants.det2431
#print axioms RKResearch.ERK10BalancedSeamDeterminants.det3124
#print axioms RKResearch.ERK10BalancedSeamDeterminants.det3142
#print axioms RKResearch.ERK10BalancedSeamDeterminants.det3214
#print axioms RKResearch.ERK10BalancedSeamDeterminants.det3241
#print axioms RKResearch.ERK10BalancedSeamDeterminants.det3412
#print axioms RKResearch.ERK10BalancedSeamDeterminants.det3421
#print axioms RKResearch.ERK10BalancedSeamDeterminants.det4123
#print axioms RKResearch.ERK10BalancedSeamDeterminants.det4132
#print axioms RKResearch.ERK10BalancedSeamDeterminants.det4213
#print axioms RKResearch.ERK10BalancedSeamDeterminants.det4231
#print axioms RKResearch.ERK10BalancedSeamDeterminants.det4312
#print axioms RKResearch.ERK10BalancedSeamDeterminants.det4321
