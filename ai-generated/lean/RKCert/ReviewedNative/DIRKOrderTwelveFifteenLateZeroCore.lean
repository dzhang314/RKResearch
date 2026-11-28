import Lean.Elab.Tactic.Omega

/-! Portable integer scalar identities and the fixed prime/quintic check.
    These are denominator-cleared coefficient identities; the actual
    stage-space and finite extension arguments are documented separately. -/
namespace RKResearch.Certified.Graded.OrderTwelveFifteen.LateZeroCore

theorem firstNuCleared (u C : Int) (h : 2*C = 5-20*u) :
    2*C+10*(1+2*u)=15 := by omega

/-- After multiplication by 1200, z is the C-dependent contribution to
    the quintic coefficient. It cancels without dividing by a mode. -/
theorem geometryFreeGradeSixCleared (p₁ p₂ p₃ p₄ p₅ z : Int) :
    (600*p₁+400*p₂+300*p₃+240*p₄+198*p₅+15*z)-(15*z-2*p₅)
       = 600*p₁+400*p₂+300*p₃+240*p₄+200*p₅ := by omega

/-- The literal fourth-row commutator identity with m=t-y-omega and
    q the surviving prior tap times the third-row primitive value. -/
theorem fourthPureReadInt (m d q w V Z : Int)
    (hrow : q+d*w=V) (hz : Z=(m-d)*q-d*d*w) :
    Z=m*V-d*(V+m*w) := by
  have hq : q=V-d*w := by omega
  rw [hz,hq]
  simp only [Int.sub_mul, Int.mul_sub, Int.mul_add, Int.mul_assoc]
  have hm : m*(d*w)=d*(m*w) := by
    rw [← Int.mul_assoc, Int.mul_comm m d, Int.mul_assoc]
  omega

def f (x : Nat) : Int :=
  let a := Int.ofNat x
  ((((129888*a-330000)*a+312000)*a-136800)*a+27800)*a-2015

def L₆d (x : Nat) : Int :=
  let a := Int.ofNat x
  ((((5544*a-13860)*a+12600)*a-5040)*a+840)*a-42

theorem primeTrial : (List.range 15).all (fun i => 271 % (i+2) != 0) = true := by decide +kernel

theorem quinticResidues :
    (List.range 271).filter (fun i => f i % 271 == 0) = [11,82,99,134,191] := by decide +kernel

theorem fixedGuards :
    ([11,82,99,134,191] : List Nat).all (fun i => i != 0 && L₆d i % 271 != 0) = true := by decide +kernel

#print axioms firstNuCleared
#print axioms geometryFreeGradeSixCleared
#print axioms fourthPureReadInt
#print axioms primeTrial
#print axioms quinticResidues
#print axioms fixedGuards

end RKResearch.Certified.Graded.OrderTwelveFifteen.LateZeroCore
