import Lean

/-! Arithmetic leaves for the nonzero-pooled sole invisible ghost
with a nonconstant affine outgoing/reverse-defect relation. -/
namespace RKResearch.ERK10InvisibleUnbalancedSingletonGate
open Lean.Grind
set_option linter.unusedSectionVars false
variable {K : Type} [Field K] [IsCharP K 0]

theorem affineExtend (a b m3 m4 m5 : K) (b0 : b ≠ 0) (m30 : m3=0)
    (m34 : a*m3+b*m4=0) (m45 : a*m4+b*m5=0) : m4=0 ∧ m5=0 := by
  have m40 : m4=0 := by grind
  exact ⟨m40,by grind⟩

theorem pairResidues (x y a b : K) (xy : x ≠ y)
    (m0 : a+b=0) (m1 : x*a+y*b=0) : a=0 ∧ b=0 := by
  have h : (x-y)*a=0 := by
    calc
      _=(x*a+y*b)-y*(a+b) := by clear m0 m1; grind
      _=0 := by rw [m0,m1]; grind
  exact ⟨by grind,by grind⟩

theorem doubleResidues (x a b d slope : K) (d0 : d ≠ 0)
    (m0 : a*d-b*slope=0)
    (m1 : x*(a*d-b*slope)+b*d=0) : a=0 ∧ b=0 := by
  rw [m0] at m1
  have b0 : b=0 := by grind
  exact ⟨by grind,b0⟩

theorem pairVariance (a b x y mean : K) (a0 : a ≠ 0) (b0 : b ≠ 0)
    (mass : a+b ≠ 0) (first : a*x+b*y=(a+b)*mean)
    (second : a*x^2+b*y^2=(a+b)*mean^2) : x=mean ∧ y=mean := by
  have h : a*b*(x-y)^2=0 := by
    calc
      _=(a+b)*(a*x^2+b*y^2)-(a*x+b*y)^2 := by clear first second; grind
      _=0 := by rw [first,second]; grind
  have e : x=y := by grind
  exact ⟨by grind,by grind⟩

def L (w : K) : K := 42*w^4-84*w^3+56*w^2-14*w+1
def r0 (w : K) : K := 42*w^3-84*w^2+56*w-14
def r1 (w : K) : K := 42*w^2-84*w+56
def r2 (w : K) : K := 42*w-84
def quo (x w : K) : K := r0 w+r1 w*x+r2 w*x^2+42*x^3

theorem quotientIdentity (x w : K) : (x-w)*quo x w=L x-L w := by
  unfold quo r0 r1 r2 L
  grind

/- Entries are 50400/((i+2)(i+j+3)(i+j+4)), for i,j=0,1,2,3. -/
def seam (w : K) : K :=
  r0 w*(2100*r0 w+1260*r1 w+840*r2 w+600*42)
  +r1 w*(840*r0 w+560*r1 w+400*r2 w+300*42)
  +r2 w*(420*r0 w+300*r1 w+225*r2 w+175*42)
  +42*(240*r0 w+180*r1 w+140*r2 w+112*42)

def rem (w : K) : K := 105*w^2-105*w+56

theorem seamReduce (w : K) :
    seam w=28*((3150*w^2-3150*w+630)*L w+rem w) := by
  unfold seam r0 r1 r2 L rem
  grind

theorem seamBezout (w : K) :
    25*L w+(-10*w^2+10*w+2)*rem w=137 := by
  unfold L rem
  grind

theorem noCleanMiddleSeam (w : K) (root : L w=0) (cut : seam w=0) : False := by
  have red := seamReduce w
  rw [cut, root] at red
  have rr : rem w=0 := by grind
  have bz := seamBezout w
  rw [root, rr] at bz
  grind

end RKResearch.ERK10InvisibleUnbalancedSingletonGate
#print axioms RKResearch.ERK10InvisibleUnbalancedSingletonGate.affineExtend
#print axioms RKResearch.ERK10InvisibleUnbalancedSingletonGate.pairResidues
#print axioms RKResearch.ERK10InvisibleUnbalancedSingletonGate.doubleResidues
#print axioms RKResearch.ERK10InvisibleUnbalancedSingletonGate.pairVariance
#print axioms RKResearch.ERK10InvisibleUnbalancedSingletonGate.quotientIdentity
#print axioms RKResearch.ERK10InvisibleUnbalancedSingletonGate.seamReduce
#print axioms RKResearch.ERK10InvisibleUnbalancedSingletonGate.seamBezout
#print axioms RKResearch.ERK10InvisibleUnbalancedSingletonGate.noCleanMiddleSeam
