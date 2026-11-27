import Lean

/-! Exact scalar leaves for the shared-clock two-dormant ERK10 chart. -/
namespace RKResearch.ERK10SharedDormantGate
open Lean.Grind
variable {K : Type} [Field K]

def lobatto (x : K) : K := 42*x^4-84*x^3+56*x^2-14*x+1
def lobattoDeriv (x : K) : K := 168*x^3-252*x^2+112*x-14
def doubleContact (x : K) : K := 294*x^4-336*x^3+84*x-16

theorem doubleContactClear (t : K) :
    doubleContact (2*t)=2*((2*t)*lobattoDeriv (2*t)-8*lobatto t) := by
  unfold doubleContact lobattoDeriv lobatto
  grind

theorem doubleContactBezout (x : K) :
    (-319284*x^3+182028*x^2+95802*x-35007)*lobatto x+
    (45612*x^3-65100*x^2+24738*x-2263)*doubleContact x=1201 := by
  unfold lobatto doubleContact
  grind

private theorem mulNZ {a b : K} (ha : a ≠ 0) (hb : b ≠ 0) : a*b ≠ 0 :=
  fun h => hb ((Field.of_mul_eq_zero h).resolve_left ha)

theorem threeResidues (a b c x y z : K)
    (hab : a-b≠0) (hac : a-c≠0) (hbc : b-c≠0)
    (h0 : x+y+z=0) (h1 : a*x+b*y+c*z=0) (h2 : a^2*x+b^2*y+c^2*z=0) :
    x=0 ∧ y=0 ∧ z=0 := by
  have h : (a-b)*(a-c)*x=0 := by grind
  have hx := (Field.of_mul_eq_zero h).resolve_left (mulNZ hab hac)
  have k : (b-c)*y=0 := by grind
  exact ⟨hx,(Field.of_mul_eq_zero k).resolve_left hbc,by grind⟩

theorem pairedPureSplit (b c v w : K) (nb : b≠0) (nc : c≠0)
    (np : b+c≠0) (nonzero : v≠0 ∨ w≠0) (cancel : b*v+c*w=0) :
    v≠0 ∧ w≠0 ∧ v≠w := by
  have hv : v≠0 := by
    intro q
    have h : c*w=0 := by grind
    have h' := (Field.of_mul_eq_zero h).resolve_left nc
    exact nonzero.elim (fun n => n q) (fun n => n h')
  have hw : w≠0 := by
    intro q
    have h : b*v=0 := by grind
    exact hv ((Field.of_mul_eq_zero h).resolve_left nb)
  refine ⟨hv,hw,?_⟩
  intro q
  have h : (b+c)*v=0 := by grind
  exact hv ((Field.of_mul_eq_zero h).resolve_left np)

theorem quadraticNoThree (a b c x y z : K)
    (xy : x-y≠0) (xz : x-z≠0) (yz : y-z≠0)
    (hx : a*x^2+b*x+c=0) (hy : a*y^2+b*y+c=0) (hz : a*z^2+b*z+c=0) :
    a=0 ∧ b=0 ∧ c=0 := by
  have h₁ : (x-y)*(a*(x+y)+b)=0 := by grind
  have h₂ : (x-z)*(a*(x+z)+b)=0 := by grind
  have h₃ := (Field.of_mul_eq_zero h₁).resolve_left xy
  have h₄ := (Field.of_mul_eq_zero h₂).resolve_left xz
  have h₅ : (y-z)*a=0 := by grind
  have ha := (Field.of_mul_eq_zero h₅).resolve_left yz
  exact ⟨ha,by grind,by grind⟩

/-- No sign assumption is needed to exclude a zero mixed numerator. -/
theorem mixedNorm (t : K) :
    225*(42*t^2-14*t+1) - (15*t-8)*(630*t+126)=1233 := by grind

end RKResearch.ERK10SharedDormantGate
#print axioms RKResearch.ERK10SharedDormantGate.doubleContactClear
#print axioms RKResearch.ERK10SharedDormantGate.doubleContactBezout
#print axioms RKResearch.ERK10SharedDormantGate.threeResidues
#print axioms RKResearch.ERK10SharedDormantGate.pairedPureSplit
#print axioms RKResearch.ERK10SharedDormantGate.quadraticNoThree
#print axioms RKResearch.ERK10SharedDormantGate.mixedNorm
