import Lean

/-! Exact scalar certificates for the two-clock single-invisible-ghost census. -/
namespace RKResearch.ERK10SingleGhostClosureGate
open Lean.Grind
variable {K : Type} [Field K]

def bracket (u v a b : K) : K :=
  12*v^3-15*(u+a+b)*v^2+20*(u*a+u*b+a*b)*v-30*u*a*b

def lobatto (v : K) : K := 42*v^4-84*v^3+56*v^2-14*v+1
def contact (v : K) : K := 231*v^3-390*v^2+200*v-30

theorem vietaIdentity (u v a b : K) :
    3*bracket u v a b =
      231*v^3-195*(u+v+a+b)*v^2+
      150*(u*v+u*a+u*b+v*a+v*b+a*b)*v-
      90*(u*v*a+u*v*b+u*a*b+v*a*b) := by
  unfold bracket
  grind

theorem contactBezout (v : K) :
    (-32340*v^2+35658*v-8263)*lobatto v+
     (5880*v^3-8316*v^2+3178*v-280)*contact v=137 := by
  unfold lobatto contact
  grind

/-- These are the denominator-cleared cancellations at the first
effective contact, before using the nonzero contact clock. -/
theorem firstJetIdentity (u s p : K) :
    u*(5*s-6*u) =
      10*(3*u^2-4*s*u+6*p)-3*(12*u^2-15*s*u+20*p) ∧
    3*(10*p-3*u^2)=
      5*(3*u^2-4*s*u+6*p)+4*u*(5*s-6*u) := by
  constructor <;> grind

theorem secondContactFactor (u v : K) :
    12*v^3-33*u*v^2+30*u^2*v-9*u^3=3*(v-u)^2*(4*v-3*u) := by
  grind

theorem affineLast (u v a b : K) :
    bracket u v a b=bracket u v a 0+b*(bracket u v a 1-bracket u v a 0) := by
  unfold bracket
  grind

theorem affineFirst (u v a b : K) :
    bracket u v a b=bracket 0 v a b+u*(bracket 1 v a b-bracket 0 v a b) := by
  unfold bracket
  grind

theorem affineDetZero (a0 a1 b0 b1 x : K)
    (ha : a0+(a1-a0)*x=0) (hb : b0+(b1-b0)*x=0) : a0*b1-a1*b0=0 := by
  have q := congrArg (fun v : K => (b1-b0)*v) ha
  have r := congrArg (fun v : K => (a1-a0)*v) hb
  grind

theorem sixCleanExpansion (x : K) :
    x*(1-x)*(24*x^2-24*x+5)*(6*x-5)*(8*x-5)*(8*x-3)*(6*x-1) =
    -55296*x^8+221184*x^7-363936*x^6+317664*x^5-157876*x^4+
    44360*x^3-6475*x^2+375*x := by grind

theorem sixCleanMoment :
    (-55296*(2520/9)+221184*(2520/8)-363936*(2520/7)+317664*(2520/6)-
      157876*(2520/5)+44360*(2520/4)-6475*(2520/3)+375*(2520/2):Int)=2796 := by decide

namespace Mod37
def red (x : Int) : Int := x%37
def nodes : Fin 4 → Int := fun i => ([6,8,30,32]:List Int)[i.val]?.getD 0
def l (x : Int) : Int := 42*x^4-84*x^3+56*x^2-14*x+1
def f (u v a b : Int) : Int :=
  12*v^3-15*(u+a+b)*v^2+20*(u*a+u*b+a*b)*v-30*u*a*b
def distinct4 (i j k m : Fin 4) : Prop :=
  i≠j ∧ i≠k ∧ i≠m ∧ j≠k ∧ j≠m ∧ k≠m
instance : Decidable (distinct4 i j k m) := by unfold distinct4; infer_instance
def detFixed (u v w a : Int) : Int :=
  f u v a 0*f (1-u) (1-w) (1-a) 0-
  f u v a 1*f (1-u) (1-w) (1-a) 1
def detMovable (v w a b : Int) : Int :=
  f 0 v a b*f 0 (1-w) (1-a) (1-b)-
  f 1 v a b*f 1 (1-w) (1-a) (1-b)

theorem primeTrial : ∀ i : Fin 37, 2≤i.val → 37%i.val≠0 := by decide
theorem roots : ∀ i : Fin 4, red (l (nodes i))=0 := by decide
theorem distinct : ∀ i j : Fin 4, i≠j → red (nodes i)≠red (nodes j) := by decide
theorem noFirstJet : ∀ i j : Fin 4, i≠j →
    red (10*(nodes i)^2-12*(nodes i)*(nodes j)+3*(nodes j)^2)≠0 := by decide
theorem noFixedDetZero : ∀ i j k m : Fin 4, distinct4 i j k m →
    red (detFixed (nodes i) (nodes j) (nodes k) (nodes m))≠0 := by decide
theorem noMovableDetZero : ∀ i j k m : Fin 4, distinct4 i j k m →
    red (detMovable (nodes i) (nodes j) (nodes k) (nodes m))≠0 := by decide
end Mod37
end RKResearch.ERK10SingleGhostClosureGate

#print axioms RKResearch.ERK10SingleGhostClosureGate.vietaIdentity
#print axioms RKResearch.ERK10SingleGhostClosureGate.contactBezout
#print axioms RKResearch.ERK10SingleGhostClosureGate.firstJetIdentity
#print axioms RKResearch.ERK10SingleGhostClosureGate.secondContactFactor
#print axioms RKResearch.ERK10SingleGhostClosureGate.affineLast
#print axioms RKResearch.ERK10SingleGhostClosureGate.affineFirst
#print axioms RKResearch.ERK10SingleGhostClosureGate.affineDetZero
#print axioms RKResearch.ERK10SingleGhostClosureGate.sixCleanExpansion
#print axioms RKResearch.ERK10SingleGhostClosureGate.sixCleanMoment
#print axioms RKResearch.ERK10SingleGhostClosureGate.Mod37.primeTrial
#print axioms RKResearch.ERK10SingleGhostClosureGate.Mod37.roots
#print axioms RKResearch.ERK10SingleGhostClosureGate.Mod37.distinct
#print axioms RKResearch.ERK10SingleGhostClosureGate.Mod37.noFirstJet
#print axioms RKResearch.ERK10SingleGhostClosureGate.Mod37.noFixedDetZero
#print axioms RKResearch.ERK10SingleGhostClosureGate.Mod37.noMovableDetZero
