import RKCert.ReviewedNative.DIRKOrderTwelveFifteenFourDirtyArithmetic

/-! Portable coprime-primitive and moving-linear-factor receipts for the
visible rank-four cubic split at order twelve. -/

namespace RKResearch.Certified.Graded.OrderTwelveFifteen.HighVisibleArithmetic

open FourDirtyArithmetic

set_option maxRecDepth 20000
set_option maxHeartbeats 0

def finiteInv (x : Nat) : Nat :=
  (List.range prime).find? (fun k => x*k % prime == 1) |>.getD 0

def trimPoly (f : List Nat) : List Nat :=
  (f.reverse.dropWhile (· == 0)).reverse

def remEuclid : Nat → List Nat → List Nat → List Nat
  | 0, f, _ => f
  | n+1, f, g =>
    if g.isEmpty || f.length < g.length then f
    else
      let q := f.getLastD 0 * finiteInv (g.getLastD 0) % prime
      let gg := (List.replicate (f.length-g.length) 0) ++ g.map (fun g => negative (g*q))
      remEuclid n (trimPoly (addPoly f gg)) g

def gcdIsConstant : Nat → List Nat → List Nat → Bool
  | 0, _, _ => false
  | n+1, f, g =>
    if g.isEmpty then f.length == 1 && f.getLastD 0 != 0
    else gcdIsConstant n g (remEuclid 8 f g)

def residual (weight : Nat) (p : List Nat) : List Nat :=
  (List.range p.length).map fun i => p[i]?.getD 0 * inverseSmall (i+weight+1) % prime

def primitivePairPass (chosen : List Nat) : Bool :=
  let f := hull chosen
  let a := residual 1 f
  let b := residual 2 f
  a.length == chosen.length+1 && b.length == chosen.length+1 &&
  a.getLastD 0 != 0 && b.getLastD 0 != 0 && gcdIsConstant 8 a b

def selectTriples : List Nat → List (List Nat)
  | [] => []
  | a::as => ((selectPairs as).map fun ab => a::ab) ++ selectTriples as

def linearFamilyDet (u : Nat) (chosen : List Nat) : Nat :=
  let f := 0::hull chosen
  let a := integral f 0 u
  let b := integral (0::f) 0 u
  let c := integral (0::0::f) 0 u
  subMod (a*c) (b*b)

def linearFamilyDets (chosen : List Nat) : List Nat :=
  ((interiors ++ [1]).filter fun v => !chosen.contains v).map fun v => linearFamilyDet v chosen

theorem fixedQuadraticFactors :
    (selectPairs interiors).length = 10 ∧
    (selectPairs interiors).all primitivePairPass = true := by decide_cbv

theorem fixedCubicFactors :
    (selectTriples interiors).length = 10 ∧
    (selectTriples interiors).all primitivePairPass = true := by decide_cbv

theorem movingLinearFactor :
    ((selectPairs interiors).flatMap linearFamilyDets).length = 40 ∧
    ((selectPairs interiors).flatMap linearFamilyDets).all (· != 0) = true := by decide_cbv

#print axioms fixedQuadraticFactors
#print axioms fixedCubicFactors
#print axioms movingLinearFactor

end RKResearch.Certified.Graded.OrderTwelveFifteen.HighVisibleArithmetic
