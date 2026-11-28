import Lean.Elab.Tactic.Omega

/-! Portable arithmetic receipt for the base degree preservation and
factor products in the prime-113 reflected-zero exclusion. The
ordered-pair multiplication determinants are checked separately. -/
namespace RKResearch.Certified.Graded.OrderTwelveFifteen.NineSiteFirstRootZeroCore

def l6d (a : Int) : Int :=
  ((((5544*a-13860)*a+12600)*a-5040)*a+840)*a-42

def baseResiduals : List Nat := [7,21,57,93,107]

def hQuartic (a : Int) : List Int :=
  [(((-26598*a+48360)*a-29016)*a+6448)*a-403,
   (((-144144*a+271440)*a-168480)*a+38688)*a-2496,
   (((384384*a-742560)*a+474240)*a-112320)*a+7488,
   (((-216216*a+425880)*a-278460)*a+67860)*a-4680,
   (((33264*a-66528)*a+44352)*a-11088)*a+792]

def momentPivot (a : Int) : Int := ((42*a-56)*a+21)*a-2

def hFactors : List (Nat × List (List Int)) :=
  [(7,[[43,1],[65,1],[40,48,1]]),
   (21,[[92,20,64,54,1]]),
   (57,[[84,1],[10,66,79,1]]),
   (93,[[51,1],[103,1],[62,5,1]]),
   (107,[[60,67,53,57,1]])]

def polyMul (p q : List Int) : List Int :=
  (List.range (p.length+q.length-1)).map (fun k =>
    (List.range p.length).foldl (fun sum i =>
      if i ≤ k then sum+(p[i]?).getD 0*(q[k-i]?).getD 0 else sum) 0)

def test (c : Nat × List (List Int)) : Bool :=
  let p := hQuartic (Int.ofNat c.1)
  let leading := (p[4]?).getD 0
  let g := c.2.foldl polyMul [1]
  p.map (fun v => v % 113) == g.map (fun v => (v*leading) % 113)

theorem primeTrial : (List.range 9).all (fun i => 113 % (i+2) != 0) = true :=
  by decide +kernel

theorem completeBase : (List.range 113).filter (fun a => l6d (Int.ofNat a) % 113 == 0) =
    baseResiduals := by decide +kernel

theorem leadingGuards : baseResiduals.all (fun a =>
    a != 0 && momentPivot a % 113 != 0 && ((hQuartic a)[4]?).getD 0 % 113 != 0) = true :=
  by decide +kernel

theorem hFactorProducts : hFactors.all test = true :=
  by decide +kernel

#print axioms primeTrial
#print axioms completeBase
#print axioms leadingGuards
#print axioms hFactorProducts
end RKResearch.Certified.Graded.OrderTwelveFifteen.NineSiteFirstRootZeroCore
