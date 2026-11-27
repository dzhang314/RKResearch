import Lean

/-! Paid scalar leaves for the all-live explicit order-ten equality case. -/
namespace RKResearch.ERK10EqualityClockGate
open Lean.Grind
variable {K : Type} [Field K]

def L (x : K) : K := 42*x^4-84*x^3+56*x^2-14*x+1
def Q (x : K) : K := 336*x^4-56*x^2+1

theorem lobattoBezout (x : K) :
    (59136*x^3+14784*x^2-5248*x-856)*L x
      + (-7392*x^3+12936*x^2-6736*x+951)*Q x = 95 := by
  unfold L Q
  grind

theorem halfShift (u v : K) (shift : 2*(u-v)=1) (n2 : (2:K) ≠ 0) :
    8*L u=Q v := by
  have hu : 2*u=2*v+1 := by grind
  have hh : 16*L u=42*(2*u)^4-168*(2*u)^3+224*(2*u)^2-112*(2*u)+16 := by
    unfold L
    grind
  rw [hu] at hh
  have hv : 42*(2*v+1)^4-168*(2*v+1)^3+224*(2*v+1)^2-112*(2*v+1)+16=2*Q v := by
    unfold Q
    grind
  rw [hv] at hh
  have hz : (2:K)*(8*L u-Q v)=0 := by grind
  have hi := (Field.of_mul_eq_zero hz).resolve_left n2
  grind

theorem lobattoNoHalfShift (u v : K) (hU : L u=0) (hV : L v=0)
    (shift : 2*(u-v)=1) (n2 : (2:K) ≠ 0) (n95 : (95:K) ≠ 0) : False := by
  have hv : Q v=0 := by rw [← halfShift u v shift n2,hU]; grind
  have z := lobattoBezout v
  rw [hV,hv] at z
  have hn : (95:K)=0 := by grind
  exact n95 hn

theorem noLobattoRootModEleven : ∀ j : Fin 11,
    (42*(j.val:Int)^4-84*(j.val:Int)^3+56*(j.val:Int)^2-14*(j.val:Int)+1)%11 ≠ 0 := by decide

def p (t : K) : K := 49*t^2-14*t+29
def q (t : K) : K := 77*t^2-102*t+25

theorem centeredBezout (t : K) :
    (87-55*t)*p t+(35*t-19)*q t=2048 := by
  unfold p q
  grind

theorem firstTwoCenteredCoeffs (s₂ s₄ : K)
    (h₀ : 3+7*s₂+35*s₄=0) (h₂ : 5+9*s₂+21*s₄=0)
    (n5 : (5:K) ≠ 0) (n8 : (8:K) ≠ 0) :
    3*s₂+2=0 ∧ 21*s₄=1 := by
  have h₁ : (8:K)*(3*s₂+2)=0 := by grind
  have v := (Field.of_mul_eq_zero h₁).resolve_left n8
  have h₃ : (5:K)*(21*s₄-1)=0 := by grind
  have w := (Field.of_mul_eq_zero h₃).resolve_left n5
  exact ⟨v, by grind⟩

theorem centeredElimination (z w : K)
    (h₂ : 7*z^2+5+16*z*w=0) (h₄ : 7*z*(z^2-1)*w=4)
    (h₃ : 7*z^3+41*z+(49*z^2+15)*w=0)
    (n3 : (3:K) ≠ 0) : p (z^2)=0 ∧ q (z^2)=0 := by
  have ap : p (z^2)=(7*(z^2-1))*(7*z^2+5+16*z*w)
      -16*(7*z*(z^2-1)*w-4) := by unfold p; grind
  have aq : 3*q (z^2)=(49*z^2+15)*(7*z^2+5+16*z*w)
      -16*z*(7*z^3+41*z+(49*z^2+15)*w) := by unfold q; grind
  rw [h₂,h₄] at ap
  rw [h₂,h₃] at aq
  have nz : (3:K)*q (z^2)=0 := by grind
  exact ⟨by grind, (Field.of_mul_eq_zero nz).resolve_left n3⟩

theorem noCenteredRoots (z w : K)
    (h₂ : 7*z^2+5+16*z*w=0) (h₄ : 7*z*(z^2-1)*w=4)
    (h₃ : 7*z^3+41*z+(49*z^2+15)*w=0)
    (n3 : (3:K) ≠ 0) (n2048 : (2048:K) ≠ 0) : False := by
  obtain ⟨a,b⟩ := centeredElimination z w h₂ h₄ h₃ n3
  have zc := centeredBezout (z^2)
  rw [a,b] at zc
  exact n2048 (by grind)

def J4 (u : K) : K := 21*u^4-14*u^2+1
def opposite (u : K) : K := 9*u^2-2*u-3
def crossed (u : K) : K := 447*u^4-288*u^3-98*u^2+56*u-5

theorem oppositeBezout (u : K) :
    (-63*u-256)*J4 u+(147*u^3+630*u^2+91*u-168)*opposite u=248 := by
  unfold J4 opposite
  grind

theorem crossedBezout (u : K) :
    (-50611575*u^3+15646491*u^2+16492714*u-1578139)*J4 u
      +(2377725*u^3+796887*u^2-1325254*u-412839)*crossed u=486056 := by
  unfold J4 crossed
  grind

theorem crossedNecessary (u v : K)
    (h : 7*u^2-4*u+1+(2-10*u)*v=0) (hv : 3*v^2=2-3*u^2) :
    crossed u=0 := by
  let a := 7*u^2-4*u+1
  let b := 2-10*u
  have root : a= -(b*v) := by
    dsimp [a,b]
    grind
  have sq : a^2=b^2*v^2 := by rw [root]; grind
  have fact : crossed u=3*a^2-b^2*(2-3*u^2) := by
    dsimp [a,b]
    unfold crossed
    grind
  rw [sq, ← hv] at fact
  grind

theorem oppositeAtOne (s : K) (hJ : 21*s^2-14*s+1=0)
    (h : 3*s=1) (n4 : (4:K) ≠ 0) : False := by
  exact n4 (by grind)

theorem crossedAtOne (s p : K) (hp : 21*p^2=1) (hs : 3*s^2=2+6*p)
    (h : s=1+3*p) (n4 : (4:K) ≠ 0) (n5 : (5:K) ≠ 0) : False := by
  rw [h] at hs
  have hq0 : (4:K)*(21*p+4)=0 := by grind
  have hq1 := (Field.of_mul_eq_zero hq0).resolve_left n4
  have hq : 21*p= -4 := by grind
  have hq2 : (21*p)^2=21 := by grind
  rw [hq] at hq2
  exact n5 (by grind)

end RKResearch.ERK10EqualityClockGate
#print axioms RKResearch.ERK10EqualityClockGate.lobattoBezout
#print axioms RKResearch.ERK10EqualityClockGate.halfShift
#print axioms RKResearch.ERK10EqualityClockGate.lobattoNoHalfShift
#print axioms RKResearch.ERK10EqualityClockGate.noLobattoRootModEleven
#print axioms RKResearch.ERK10EqualityClockGate.centeredBezout
#print axioms RKResearch.ERK10EqualityClockGate.firstTwoCenteredCoeffs
#print axioms RKResearch.ERK10EqualityClockGate.centeredElimination
#print axioms RKResearch.ERK10EqualityClockGate.noCenteredRoots
#print axioms RKResearch.ERK10EqualityClockGate.oppositeBezout
#print axioms RKResearch.ERK10EqualityClockGate.crossedBezout
#print axioms RKResearch.ERK10EqualityClockGate.crossedNecessary
#print axioms RKResearch.ERK10EqualityClockGate.oppositeAtOne
#print axioms RKResearch.ERK10EqualityClockGate.crossedAtOne
