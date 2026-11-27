import Lean

namespace RKResearch.Certified.SDIRK9ThreeTerminalMod37

/-- Ascending coefficient arrays over the residue field, used only for
the four literal finite Bézout certificates. -/
abbrev P := List Int
def norm (p : P) : P := (p.reverse.dropWhile (· == 0)).reverse
def k (i : Int) : P := norm [i % 37]
def get (p : P) (j : Nat) : Int := p[j]?.getD 0
def pAdd (a b : P) : P :=
  norm ((List.range (max a.length b.length)).map fun i => (get a i + get b i) % 37)
def pScale (a : Int) (b : P) : P := norm (b.map fun v => (a*v)%37)
def pSub (a b : P) : P := pAdd a (pScale (-1) b)
def pMul (a b : P) : P :=
  norm ((List.range (a.length + b.length - 1)).map fun j =>
    (((List.range (j+1)).map fun i => get a i * get b (j-i)).foldl (·+·) 0)%37)
def cert (degree : Nat) (f g u v : P) : Bool :=
  f.length == degree+1 && g.length == degree+1 &&
  pAdd (pMul u f) (pMul v g) == [1]

def f0 : P := [33, 26, 3, 35, 35]
def g0 : P := [24, 31, 8, 6, 36]
def u0 : P := [11, 29, 20, 21]
def v0 : P := [25, 30, 36, 32]
def f1 : P := [2, 1, 4, 13, 24]
def g1 : P := [20, 0, 19, 18, 7]
def u1 : P := [4, 26, 34, 2]
def v1 : P := [20, 12, 31, 9]
def f2 : P := [5, 11, 3, 13, 21, 5, 22, 10, 3, 20, 26, 27]
def g2 : P := [21, 32, 9, 19, 31, 4, 35, 11, 30, 31, 25, 27]
def u2 : P := [34, 5, 5, 7, 36, 25, 28, 5, 26, 3, 23]
def v2 : P := [36, 16, 22, 12, 22, 24, 25, 22, 1, 3, 14]
def f3 : P := [25, 34, 9, 13, 25, 13, 19, 2, 21, 10, 0, 18, 6, 20, 32, 32, 13, 27, 0, 31, 21, 32, 0, 28, 11, 8, 20, 8, 16, 13, 22]
def g3 : P := [36, 15, 15, 3, 3, 33, 19, 20, 29, 11, 1, 27, 0, 7, 12, 7, 6, 20, 6, 2, 11, 22, 6, 18, 33, 35, 21, 12, 22, 26, 35]
def u3 : P := [22, 2, 11, 13, 28, 31, 13, 22, 0, 15, 6, 26, 12, 29, 17, 30, 4, 12, 34, 14, 29, 2, 12, 9, 15, 2, 35, 14, 1, 2]
def v3 : P := [31, 5, 8, 33, 24, 22, 16, 20, 32, 6, 30, 0, 16, 28, 13, 21, 23, 17, 26, 28, 4, 15, 10, 15, 20, 5, 19, 27, 14, 22]

set_option maxRecDepth 12000
set_option maxHeartbeats 0

/-- Checks the literal coefficient pair exported by the independently
reconstructed pinned-port minors, without native evaluation axioms. -/
theorem first_is_v : cert 4 f0 g0 u0 v0 = true := by decide
theorem first_is_w : cert 4 f1 g1 u1 v1 = true := by decide
theorem first_is_live : cert 11 f2 g2 u2 v2 = true := by decide
theorem first_is_terminal : cert 30 f3 g3 u3 v3 = true := by decide

end RKResearch.Certified.SDIRK9ThreeTerminalMod37
