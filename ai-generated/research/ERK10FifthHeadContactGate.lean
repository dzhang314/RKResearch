import Lean

/-! Cleared scalar identities for the genuine grade-four fifth-row gate. -/
namespace RKResearch.ERK10FifthHeadContactGate
open Lean.Grind
variable {K : Type} [Field K]

private theorem mulNZ {a b : K} (ha : a ≠ 0) (hb : b ≠ 0) : a*b ≠ 0 :=
  fun h => hb ((Field.of_mul_eq_zero h).resolve_left ha)

def probe (t y X : K) : K := X^2*(X-y)*(2*X-3*t)
def primeProbe (t y X : K) : K := 8*X^3-(9*t+6*y)*X^2+6*t*y*X

theorem probeEntrance (t y : K) :
    primeProbe t y 0=0 ∧ primeProbe t y t= -t^3 ∧ probe t y t= -t^3*(t-y) := by
  unfold primeProbe probe
  constructor
  · grind
  · constructor <;> grind

theorem probeQuartic (t x y : K) :
    probe t y x=x^2*(2*x-3*t)*(x-y) ∧
    primeProbe t y x-x^2*(2*x-3*t)=6*x*(x-t)*(x-y) := by
  unfold primeProbe probe
  constructor <;> grind

theorem zeroFourthTapForcesOldClock (t x y a b : K)
    (n2 : (2:K) ≠ 0)
    (q : 2*(a+t*b)=y^2) (c : 2*t*a+3*t^2*b=y^3)
    (ar : (3*t-2*x)*t^2*b=2*t*(y-t)*a) :
    y=0 ∨ y=t ∨ y=x := by
  have q' := congrArg (fun v : K => t*v) q
  have h₁ : t^2*b=y^2*(y-t) := by grind
  have h₂ : 2*t*a=y^2*(3*t-2*y) := by grind
  have hs := congrArg (fun v : K => (3*t-2*x)*v) h₁
  have ht := congrArg (fun v : K => (y-t)*v) h₂
  have h : (2:K)*((y*y)*((y-t)*(y-x)))=0 := by grind
  rcases Field.of_mul_eq_zero ((Field.of_mul_eq_zero h).resolve_left n2) with hy | hz
  · exact Or.inl ((Field.of_mul_eq_zero hy).elim id id)
  · rcases Field.of_mul_eq_zero hz with hz | hz
    · exact Or.inr (Or.inl (by grind))
    · exact Or.inr (Or.inr (by grind))

theorem fourthTapForcesRepeat (t x y a : K)
    (n6 : (6:K) ≠ 0) (nx : x≠0) (nxt : x-t≠0) (na : a≠0)
    (paid : a*(primeProbe t y x-x^2*(2*x-3*t))=0) : y=x := by
  rw [(probeQuartic t x y).2] at paid
  have q : (a*(6*x*(x-t)))*(x-y)=0 := by grind
  have nz := mulNZ na (mulNZ (mulNZ n6 nx) nxt)
  have hx := (Field.of_mul_eq_zero q).resolve_left nz
  grind

theorem simpsonMasses (u a b c : K) (nu : u≠0)
    (clock : a+b+c=u) (one : u*(b+2*c)=u^2)
    (two : 3*u^2*(b+4*c)=4*u^3) :
    6*a=u ∧ 3*b=2*u ∧ 6*c=u := by
  have h : u*(b+2*c-u)=0 := by grind
  have h := (Field.of_mul_eq_zero h).resolve_left nu
  have k : (u*u)*(3*(b+4*c)-4*u)=0 := by grind
  have k := (Field.of_mul_eq_zero k).resolve_left (mulNZ nu nu)
  exact ⟨by grind,by grind,by grind⟩

end RKResearch.ERK10FifthHeadContactGate
#print axioms RKResearch.ERK10FifthHeadContactGate.probeEntrance
#print axioms RKResearch.ERK10FifthHeadContactGate.probeQuartic
#print axioms RKResearch.ERK10FifthHeadContactGate.zeroFourthTapForcesOldClock
#print axioms RKResearch.ERK10FifthHeadContactGate.fourthTapForcesRepeat
#print axioms RKResearch.ERK10FifthHeadContactGate.simpsonMasses
