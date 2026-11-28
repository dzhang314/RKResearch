import Lean.Elab.Tactic.Omega

/-! Portable receipt for degree-132 base residue degree preservation
and the two exact singular scalar pivot branches. -/
namespace RKResearch.Certified.Graded.OrderTwelveFifteen.NineSiteNonrootZeroCore
set_option maxRecDepth 4096 in
def f132 : List Int :=
  [30, 25, 35, 31, 22, 18, 2, 26, 34, 17, 3, 0, 14, 34, 21, 13, 29, 6, 13, 14, 21, 25, 25, 22, 36, 1, 24, 20, 13, 5, 19, 19, 33, 7, 11, 25, 33, 13, 5, 15, 5, 7, 2, 12, 10, 28, 31, 1, 25, 11, 0, 12, 1, 1, 18, 31, 10, 31, 26, 29, 28, 17, 20, 20, 15, 7, 34, 0, 3, 9, 9, 18, 6, 13, 35, 35, 33, 11, 11, 3, 25, 34, 31, 31, 33, 6, 26, 17, 22, 27, 14, 20, 7, 2, 16, 32, 36, 24, 16, 15, 19, 26, 15, 0, 10, 32, 16, 30, 19, 15, 9, 12, 35, 21, 8, 34, 26, 35, 9, 4, 21, 1, 2, 23, 20, 15, 32, 20, 29, 14, 7, 16, 1]

def factor37 : List (List Int) :=
  [[1, 1], [13, 1], [19, 22, 22, 32, 24, 34, 22, 4, 27, 1], [29, 34, 29, 31, 1, 36, 34, 12, 9, 28, 1, 13, 11, 21, 24, 23, 19, 7, 26, 4, 1], [33, 15, 23, 21, 30, 12, 35, 16, 1, 0, 9, 23, 27, 25, 3, 4, 19, 26, 31, 10, 31, 28, 13, 26, 13, 18, 31, 27, 8, 23, 10, 6, 25, 29, 36, 31, 8, 11, 18, 28, 23, 27, 12, 19, 14, 33, 18, 11, 30, 1], [19, 12, 7, 30, 7, 34, 8, 9, 17, 5, 4, 16, 7, 18, 34, 14, 11, 15, 3, 22, 24, 3, 23, 35, 28, 9, 6, 2, 7, 23, 3, 12, 22, 15, 11, 15, 10, 26, 36, 36, 18, 28, 31, 7, 2, 25, 5, 19, 2, 29, 7, 15, 1]]

def eval37 (p : List Int) (x : Int) : Int :=
  p.reverse.foldl (fun acc c => (acc*x+c)%37) 0

def d3 (a : Int) : Int := ((42*a-56)*a+21)*a-2
def t4 (a : Int) : Int := (((42*a-84)*a+56)*a-14)*a+1

def k3 (a : Int) : Int :=
  (((-216216*a+425880)*a-278460)*a+67860)*a-4680

theorem prime37 : (List.range 5).all (fun i => 37 % (i+2) != 0) = true :=
  by decide +kernel

theorem prime73 : (List.range 7).all (fun i => 73 % (i+2) != 0) = true :=
  by decide +kernel

theorem regularDegrees :
    f132.length = 133 ∧ factor37.map (fun p => p.length-1) = [1,1,9,20,49,52] :=
  by decide +kernel

theorem unitLeadingAndLinear :
    f132.getLast? = some 1 ∧ eval37 f132 36 = 0 ∧ eval37 f132 24 = 0 :=
  by decide +kernel

theorem cubicResidues : (List.range 73).filter (fun a => d3 (Int.ofNat a) % 73 == 0) =
    [18,40,65] := by decide +kernel

theorem quarticResidues : (List.range 37).filter (fun a => t4 (Int.ofNat a) % 37 == 0) =
    [6,8,30,32] := by decide +kernel

theorem singularLeading :
    ([18,40,65] : List Int).all (fun a => 792*t4 a % 73 != 0) = true ∧
    ([6,8,30,32] : List Int).all (fun a => k3 a % 37 != 0) = true :=
  by decide +kernel

#print axioms regularDegrees
#print axioms unitLeadingAndLinear
#print axioms cubicResidues
#print axioms quarticResidues
#print axioms singularLeading
end RKResearch.Certified.Graded.OrderTwelveFifteen.NineSiteNonrootZeroCore
