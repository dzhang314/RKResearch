import Lean

/-! Local arithmetic of the one-clock explicit order-ten chart. -/
namespace RKResearch.ERK10DependentLocalGate
open Lean.Grind
variable {K : Type} [Field K]

private theorem nzMul {a b : K} (na : a ≠ 0) (nb : b ≠ 0) : a*b ≠ 0 :=
  fun z => nb ((Field.of_mul_eq_zero z).resolve_left na)

theorem cleanFiveContact (t z u b c : K) (nu : u ≠ 0)
    (m₂ : 3*(b*t^2+c*z^2)=u^3) (m₃ : 4*(b*t^3+c*z^3)=u^4)
    (r : b*t^3+c*z^2*(3*t-2*z)=0)
    (p : 3*u^2-4*(t+z)*u+6*t*z=0) : u=z := by
  have hx : u^3*(2*t-u)=0 := by grind
  have n3 : u^3 ≠ 0 := by
    have hp : u^3 = (u*u)*u := by grind
    rw [hp]
    exact nzMul (nzMul nu nu) nu
  have hp := (Field.of_mul_eq_zero hx).resolve_left n3
  have hu : u=2*t := by grind
  have hq : 2*t*(2*t-z)=0 := by grind
  have nz : 2*t ≠ 0 := by simpa only [← hu] using nu
  have hg := (Field.of_mul_eq_zero hq).resolve_left nz
  grind

theorem repeatedClock (x y r₁ r₂ q : K) (nx : x ≠ 0) (nr : r₁-r₂ ≠ 0)
    (h₁ : x^3*(2*y-x)+12*q*r₁=0)
    (h₂ : x^3*(2*y-x)+12*q*r₂=0) : x=2*y := by
  have hr : 12*q*(r₁-r₂)=0 := by grind
  have hq := (Field.of_mul_eq_zero hr).resolve_right nr
  have hz : x^3*(2*y-x)=0 := by grind
  have np : x^3 ≠ 0 := by
    have hp : x^3=(x*x)*x := by grind
    rw [hp]
    exact nzMul (nzMul nx nx) nx
  have hh := (Field.of_mul_eq_zero hz).resolve_left np
  grind

theorem sameRepeat (x y : K) (h₁ : x=2*y) (h₂ : 1-x=2*(1-y)) : False := by grind

theorem oppositeRepeatContact (x y u : K) (h₁ : x=2*y) (h₂ : 1-y=2*(1-x))
    (proto : (3*u-2)^2=0) (n3 : (3:K) ≠ 0) : u=x := by
  have hz : (3*u-2)*(3*u-2)=0 := by grind
  rcases Field.of_mul_eq_zero hz with hz | hz
  · have hp : (3:K)*(u-x)=0 := by grind
    have h := (Field.of_mul_eq_zero hp).resolve_left n3
    grind
  · have hp : (3:K)*(u-x)=0 := by grind
    have h := (Field.of_mul_eq_zero hp).resolve_left n3
    grind

def large (u : K) : K := 4725*u^6-4095*u^4+915*u^2+23
def J4 (u : K) : K := 21*u^4-14*u^2+1

theorem lobattoRemainder (u : K) :
    large u-4*(15*u^2+17)=(225*u^2-45)*J4 u := by
  unfold large J4
  grind

theorem lobattoConflict (u : K) (hJ : J4 u=0) (hP : large u=0)
    (n4 : (4:K) ≠ 0) (n1096 : (1096:K) ≠ 0) : False := by
  have h := lobattoRemainder u
  rw [hJ,hP] at h
  have hx : (4:K)*(15*u^2+17)=0 := by grind
  have hx := (Field.of_mul_eq_zero hx).resolve_left n4
  have hn : 25*J4 u+(63-35*u^2)*(15*u^2+17)=1096 := by
    unfold J4
    grind
  rw [hJ,hx] at hn
  exact n1096 (by grind)

def gram : List (List Int) :=
  [[3150,1050,1050,630,630],[-1050,0,-210,0,-90],
   [1050,210,350,150,210],[-630,0,-150,0,-70],[630,90,210,70,126]]

def moment (u : Int) : Int :=
  let a := 21*u^3-14*u
  let b := 21*u^2-14
  let c := 21*u
  let d : Int := 21
  let l := [a,a+b,b+c,c+d,d]
  let r := [-a,a-b,b-c,c-d,d]
  l.zipIdx.foldl (fun x (v,i) => r.zipIdx.foldl (fun y (w,j) =>
    y+v*w*((gram[i]?.getD [])[j]?.getD 0)) x) 0

set_option maxHeartbeats 0 in
theorem mixedCubicGrid : ∀ i : Fin 7,
    let u : Int := i.val
    moment u = -98*(4725*u^6-4095*u^4+915*u^2+23) := by decide

end RKResearch.ERK10DependentLocalGate
#print axioms RKResearch.ERK10DependentLocalGate.cleanFiveContact
#print axioms RKResearch.ERK10DependentLocalGate.repeatedClock
#print axioms RKResearch.ERK10DependentLocalGate.sameRepeat
#print axioms RKResearch.ERK10DependentLocalGate.oppositeRepeatContact
#print axioms RKResearch.ERK10DependentLocalGate.lobattoRemainder
#print axioms RKResearch.ERK10DependentLocalGate.lobattoConflict
#print axioms RKResearch.ERK10DependentLocalGate.mixedCubicGrid
