import Lean

namespace RKResearch.ERK10InvisibleAffineRepeatGate
open Lean.Grind
set_option linter.unusedSectionVars false
variable {K : Type} [Field K] [IsCharP K 0]

theorem separatePoleVariance (w xi charge var : K) (distinct : w ≠ xi)
    (first : var-charge=0) (second : w*var-xi*charge=0) :
    charge=0 ∧ var=0 := by
  have h : (w-xi)*var=0 := by
    calc
      _=(w*var-xi*charge)-xi*(var-charge) := by clear first second; grind
      _=0 := by rw [first,second]; grind
  exact ⟨by grind,by grind⟩

theorem oneMissedValue (a b d : K) (dnz : d ≠ 0)
    (miss : d*(a*b)^2=0) (again : b=0 → d*a^2=0) : a=0 := by
  by_cases a0 : a=0
  · exact a0
  · have b0 : b=0 := by grind
    have h := again b0
    grind

theorem sameAmplitudeOpposed (b c u v : K)
    (b0 : b ≠ 0) (u0 : u ≠ 0)
    (mom1 : b*u+c*v=0) (mom2 : b*u^2+c*v^2=0) :
    u=v ∧ b+c=0 := by
  have h : b*u*(u-v)=0 := by
    calc
      _=(b*u^2+c*v^2)-v*(b*u+c*v) := by clear mom1 mom2; grind
      _=0 := by rw [mom1,mom2]; grind
  have uv : u=v := by grind
  exact ⟨uv,by grind⟩

theorem tripleSameMoment (a b c x y z : K)
    (h1 : a*x*(1-x)+b*y*(1-y)+c*z*(1-z)=0)
    (h2 : a*x^2*(1-x)+b*y^2*(1-y)+c*z^2*(1-z)=0) :
    a*x+b*y+c*z=a*x^2+b*y^2+c*z^2 ∧
    a*x+b*y+c*z=a*x^3+b*y^3+c*z^3 := by
  constructor <;> grind

theorem liveHeadTap (w scale first second gamma tap : K)
    (distinct : first ≠ second) (nz : gamma ≠ 0)
    (eqn : w*scale*first*tap=gamma*(second-first)) : tap ≠ 0 := by
  intro h
  rw [h] at eqn
  grind

theorem pureMaskValue (r p : K) (rn : r ≠ 0) (pn : p ≠ 0)
    (p1 : p ≠ 1) : (r*p)^2-r*(r*p) ≠ 0 := by
  have e : (r*p)^2-r*(r*p)=r^2*p*(p-1) := by
    clear rn pn p1
    grind
  rw [e]
  grind

theorem endpointModelMean :
    (42:K)/6-84/5+56/4-14/3+1/2=1/30 := by grind

def Retained {n : Nat} (ghost u port clock x : Fin n → K) : Prop :=
  ∃ (a b p0 p1 p2 p3 p4 : K), ∀ i,
    x i=a*ghost i+u i*(p0+p1*clock i+p2*(clock i)^2
                         +p3*(clock i)^3+p4*(clock i)^4)+b*port i

theorem retainedEndpoint {n : Nat} (k : Fin n)
    (ghost u port clock x : Fin n → K)
    (ge : ghost k=0) (ue : u k=0) (ve : port k=0)
    (paidSpan : Retained ghost u port clock x) : x k=0 := by
  obtain ⟨a,b,p0,p1,p2,p3,p4,h⟩ := paidSpan
  have q := h k
  grind

theorem terminalAlias {n : Nat} (k : Fin n)
    (ghost u port clock x : Fin n → K)
    (ge : ghost k=0) (ue : u k=0) (ve : port k=0)
    (paidSpan : Retained ghost u port clock x)
    (aliasAtTerminal : x k= -(1:K)/30) : False := by
  have q := retainedEndpoint k ghost u port clock x ge ue ve paidSpan
  grind

end RKResearch.ERK10InvisibleAffineRepeatGate
#print axioms RKResearch.ERK10InvisibleAffineRepeatGate.separatePoleVariance
#print axioms RKResearch.ERK10InvisibleAffineRepeatGate.oneMissedValue
#print axioms RKResearch.ERK10InvisibleAffineRepeatGate.sameAmplitudeOpposed
#print axioms RKResearch.ERK10InvisibleAffineRepeatGate.tripleSameMoment
#print axioms RKResearch.ERK10InvisibleAffineRepeatGate.liveHeadTap

#print axioms RKResearch.ERK10InvisibleAffineRepeatGate.pureMaskValue
#print axioms RKResearch.ERK10InvisibleAffineRepeatGate.endpointModelMean
#print axioms RKResearch.ERK10InvisibleAffineRepeatGate.retainedEndpoint
#print axioms RKResearch.ERK10InvisibleAffineRepeatGate.terminalAlias
