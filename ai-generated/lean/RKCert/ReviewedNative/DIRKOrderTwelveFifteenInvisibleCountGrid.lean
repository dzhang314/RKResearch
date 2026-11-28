import Lean

/-! Portable kernel arithmetic for the fixed Lobatto grid in the five- and
    six-ghost chronological exclusions. No tableau parameter is reduced. -/
namespace RKResearch.Certified.Graded.OrderTwelveFifteen.InvisibleCountGrid

set_option maxRecDepth 30000
set_option maxHeartbeats 0

def p : Nat := 1013
def sites : List Nat := [1,347,468,507,546,667]

def radau (u v : Nat) : Nat :=
  (10*v^2 + 3*u^2 + p - (12*u*v) % p) % p

def anchored (a u v : Nat) : Nat :=
  (3*a^2 + 10*u*v + p - (5*(u+v)*a) % p) % p

/-- For distinct sites the actual primitive is a²/60 times this expression,
before reduction modulo the split prime. -/
def unanchored (a d u v : Nat) : Nat :=
  (12*a^3 + 20*(d*u+d*v+u*v)*a + p
    - (15*(d+u+v)*a^2 + 30*d*u*v) % p) % p

def checkRadau : Bool :=
  sites.all fun u => sites.all fun v => u == v || radau u v != 0

def checkAnchored : Bool :=
  sites.all fun a => sites.all fun u => sites.all fun v =>
    a == u || a == v || u == v || anchored a u v != 0

def checkUnanchored : Bool :=
  sites.all fun a => sites.all fun d => sites.all fun u => sites.all fun v =>
    a == d || a == u || a == v || d == u || d == v || u == v || unanchored a d u v != 0

theorem radau_nonzero : checkRadau = true := by decide +kernel
theorem anchored_nonzero : checkAnchored = true := by decide +kernel
theorem unanchored_nonzero : checkUnanchored = true := by decide +kernel

#print axioms radau_nonzero
#print axioms anchored_nonzero
#print axioms unanchored_nonzero

end RKResearch.Certified.Graded.OrderTwelveFifteen.InvisibleCountGrid
