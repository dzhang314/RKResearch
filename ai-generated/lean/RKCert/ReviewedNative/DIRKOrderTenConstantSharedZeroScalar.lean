module

public import RKCert.ReviewedNative.DIRKOrderTenUniformOneOffPolynomialScalar

@[expose] public section

/-! # Two-end constant-clock debris: exact finite tensor certificate

The true degree-nine quadrature implies vanishing of a Hankel minor
from the first and last three generic clocks.  Their end sums are
algebraic roots of the same octic.  The computed minor is a unit in
the two-variable quotient by the independent octics, a certificate
over every extension of F_419, not an enumeration of F_419 points. -/
namespace RKResearch.Certified.Graded.ConstantSharedZeroScalar

open ConstantOneOffScalar UniformOneOffPolynomialScalar
set_option maxRecDepth 100000
set_option maxHeartbeats 6000000

def normInt (i : Int) : Nat := (i % (p : Int)).toNat
def octic : Poly :=
  scale (inv (2016%p)) ([-2430,28512,-140670,376686,-587973,530922,-253204,46200,2016].map normInt)
def sumToProduct : Poly :=
  scale (inv (7990348842%p))
    ([709443967905,-6582222614817,24916972066389,-48858014778303,
      51867299523606,-27886169534188,5605993175160,240326547552].map normInt)

def octic419 : Poly := [227,74,338,228,325,307,113,407,1]
def sumToProduct419 : Poly := [152,200,346,97,281,39,260,15]

theorem normalized_coefficients :
    octic = octic419 ∧ sumToProduct = sumToProduct419 := by decide

def remQ : Nat → Poly → Poly
  | 0, v => v
  | n+1, v =>
    if v.length < 9 then v
    else remQ n (minus v (shift (v.length-9) (scale (leading v) octic419)))

def red (v : Poly) : Poly := remQ v.length v

def front : List Poly :=
  let P := sumToProduct419
  let D := minus (scale 6 P) (power q 2)
  let a := red (power P 2)
  [neg (red (times q a)), scale 6 a, neg (red (times q (plus D P))), D]

def back : List Poly :=
  let a := front[0]?.getD []
  let b := front[1]?.getD []
  let c := front[2]?.getD []
  let d := front[3]?.getD []
  [plus (plus a b) (plus c d),neg (plus b (plus (scale 2 c) (scale 3 d))),
    plus c (scale 3 d),neg d]

def moments (n : Nat) : Nat :=
  sub (inv (n+1)) (if n=0 then div 2 30 else inv 30)

def n8 : List Nat := List.range 8
abbrev Tensor := List Poly

def front419 : List Poly := [[253,342,128,130,118,355,319,387],[165,95,298,9,222,322,25,398],[371,2,151,150,345,100,279,272],[74,362,399,163,10,234,303,90]]
def back419 : List Poly := [[25,382,138,33,276,173,88,309],[128,72,298,40,315,33,184,45],[174,250,91,220,375,383,350,123],[345,57,20,256,409,185,116,329]]

theorem fixed_heads_coefficients : front = front419 ∧ back = back419 := by decide

def moment419 : Poly := [392,196,126,91,70,56,46,248,312]
theorem fixed_interior_moments : (List.range 9).map moments = moment419 := by decide

def jEntry (h i j : Nat) : Nat :=
  front419.zipIdx.foldl (fun acc1 (a,d) =>
    back419.zipIdx.foldl (fun acc2 (b,e) =>
      add acc2 (mul3 (c a i) (c b j) (c moment419 (h+d+e)))) acc1) 0

def J (h : Nat) : Tensor := n8.map (fun i => clean (n8.map (jEntry h i)))

def J0 : Tensor := [[144,215,55,152,417,65,173,265],[215,178,406,350,393,61,211,339],[55,406,292,153,347,90,280,289],[152,350,153,353,48,224,213,312],[417,393,347,48,46,29,127,347],[65,61,90,224,29,407,50,322],[173,211,280,213,127,50,116,81],[265,339,289,312,347,322,81,328]]
def J1 : Tensor := [[72,66,301,290,201,280,318,325],[149,89,339,99,396,284,327,22],[173,67,146,10,375,3,12,97],[281,251,143,386,344,339,241,374],[216,416,391,123,23,116,338,257],[204,196,87,304,332,413,372,149],[274,303,268,391,208,97,58,352],[359,317,192,357,90,173,148,164]]
def J2 : Tensor := [[8,260,234,270,294,330,211,5],[343,4,357,347,138,328,58,221],[106,85,197,336,71,249,43,13],[261,80,50,190,124,390,117,66],[309,158,87,322,387,258,193,188],[254,240,333,355,55,293,146,374],[167,34,299,267,63,290,159,188],[39,97,108,49,21,398,403,130]]

set_option maxRecDepth 100000 in
set_option maxHeartbeats 5000000 in
private theorem J0_exact : J 0 = J0 := by decide

set_option maxRecDepth 100000 in
set_option maxHeartbeats 5000000 in
private theorem J1_exact : J 1 = J1 := by decide

set_option maxRecDepth 100000 in
set_option maxHeartbeats 5000000 in
private theorem J2_exact : J 2 = J2 := by decide

def rawTensorRow (a b : Tensor) (k₀ : Nat) : Poly :=
  n8.foldl (fun acc i => if i ≤ k₀ && k₀-i < 8 then
    plus acc (times (a[i]?.getD []) (b[k₀-i]?.getD [])) else acc) []

def powerCoeffs : List Poly :=
  (List.range 15).map (fun d => red (shift d [1]))

def rawRows (a b : Tensor) : Tensor :=
  (List.range 15).map (fun d => red (rawTensorRow a b d))

def reduceARow (raw : Tensor) (i : Nat) : Poly :=
  powerCoeffs.zipIdx.foldl (fun acc (pc,d) =>
    let cc := c pc i
    if cc=0 then acc else plus acc (scale cc (raw[d]?.getD []))) []

def mulRow (a b : Tensor) (i : Nat) : Poly := reduceARow (rawRows a b) i

def minorRow (j0 j1 j2 : Tensor) (i : Nat) : Poly :=
  minus (mulRow j0 j2 i) (mulRow j1 j1 i)

def knownMinor : Tensor :=
  [[270,170,120,106,350,320,399,224],
   [170,365,13,351,350,151,90,125],
   [120,13,127,333,258,55,381,353],
   [106,351,333,219,349,198,146,395],
   [350,350,258,349,181,227,68,140],
   [320,151,55,198,227,66,405,255],
   [399,90,381,146,68,405,290,93],
   [224,125,353,395,140,255,93,184]]

def unitWitness : Tensor :=
  [[152,236,358,374,271,135,412,88],
   [236,48,184,330,54,416,307,180],
   [358,184,68,229,180,110,73,382],
   [374,330,229,50,360,330,341,355],
   [271,54,180,360,411,223,172,338],
   [135,416,110,330,223,108,276,56],
   [412,307,73,341,172,276,317,55],
   [88,180,382,355,338,56,55,62]]

def minorCheck (j0 j1 j2 : Tensor) (i : Nat) : Bool :=
  minorRow j0 j1 j2 i == knownMinor[i]?.getD []

def witnessCheck (i : Nat) : Bool :=
  mulRow knownMinor unitWitness i == if i=0 then [1] else []

theorem normalization_units :
    [2016,7990348842,2,3,4,5,6,7,8,9,30].all unit = true := by decide


def p02 : Tensor := [[259,124,259,158,377,249,73,385],[3,117,53,119,174,326,156,315],[131,101,146,89,292,360,286,387],[121,372,387,322,232,11,231,259],[312,385,118,303,289,368,325,399],[375,328,44,288,293,366,222,123],[9,184,371,144,255,81,340,392],[44,86,411,241,116,60,20,319],[179,385,212,330,2,186,366,129],[10,105,40,29,220,70,373,55],[244,106,339,331,114,415,3,53],[140,167,264,5,190,17,270,347],[13,67,66,330,367,287,210,383],[311,264,199,35,183,262,120,116],[7,212,130,190,173,269,97,416]]

set_option maxRecDepth 100000 in
set_option maxHeartbeats 3000000 in
private theorem p02row0 : red (rawTensorRow J0 J2 0) = p02[0]?.getD [] := by decide

set_option maxRecDepth 100000 in
set_option maxHeartbeats 3000000 in
private theorem p02row1 : red (rawTensorRow J0 J2 1) = p02[1]?.getD [] := by decide

set_option maxRecDepth 100000 in
set_option maxHeartbeats 3000000 in
private theorem p02row2 : red (rawTensorRow J0 J2 2) = p02[2]?.getD [] := by decide

set_option maxRecDepth 100000 in
set_option maxHeartbeats 3000000 in
private theorem p02row3 : red (rawTensorRow J0 J2 3) = p02[3]?.getD [] := by decide

set_option maxRecDepth 100000 in
set_option maxHeartbeats 3000000 in
private theorem p02row4 : red (rawTensorRow J0 J2 4) = p02[4]?.getD [] := by decide

set_option maxRecDepth 100000 in
set_option maxHeartbeats 3000000 in
private theorem p02row5 : red (rawTensorRow J0 J2 5) = p02[5]?.getD [] := by decide

set_option maxRecDepth 100000 in
set_option maxHeartbeats 3000000 in
private theorem p02row6 : red (rawTensorRow J0 J2 6) = p02[6]?.getD [] := by decide

set_option maxRecDepth 100000 in
set_option maxHeartbeats 3000000 in
private theorem p02row7 : red (rawTensorRow J0 J2 7) = p02[7]?.getD [] := by decide

set_option maxRecDepth 100000 in
set_option maxHeartbeats 3000000 in
private theorem p02row8 : red (rawTensorRow J0 J2 8) = p02[8]?.getD [] := by decide

set_option maxRecDepth 100000 in
set_option maxHeartbeats 3000000 in
private theorem p02row9 : red (rawTensorRow J0 J2 9) = p02[9]?.getD [] := by decide

set_option maxRecDepth 100000 in
set_option maxHeartbeats 3000000 in
private theorem p02row10 : red (rawTensorRow J0 J2 10) = p02[10]?.getD [] := by decide

set_option maxRecDepth 100000 in
set_option maxHeartbeats 3000000 in
private theorem p02row11 : red (rawTensorRow J0 J2 11) = p02[11]?.getD [] := by decide

set_option maxRecDepth 100000 in
set_option maxHeartbeats 3000000 in
private theorem p02row12 : red (rawTensorRow J0 J2 12) = p02[12]?.getD [] := by decide

set_option maxRecDepth 100000 in
set_option maxHeartbeats 3000000 in
private theorem p02row13 : red (rawTensorRow J0 J2 13) = p02[13]?.getD [] := by decide

set_option maxRecDepth 100000 in
set_option maxHeartbeats 3000000 in
private theorem p02row14 : red (rawTensorRow J0 J2 14) = p02[14]?.getD [] := by decide

private theorem p02_exact : rawRows J0 J2 = p02 := by
  unfold rawRows
  have er : List.range 15 = [0,1,2,3,4,5,6,7,8,9,10,11,12,13,14] := by decide
  rw [er]
  simp only [List.map_cons,List.map_nil,p02row0, p02row1, p02row2, p02row3, p02row4, p02row5, p02row6, p02row7, p02row8, p02row9, p02row10, p02row11, p02row12, p02row13, p02row14] <;> rfl
def p11 : Tensor := [[348,404,99,160,193,270,300,233],[371,203,305,249,253,330,71,125],[378,181,208,354,413,225,25,349],[226,38,140,4,268,141,397,367],[78,7,379,61,28,217,286,248],[189,270,415,244,257,24,270,61],[77,374,98,54,309,92,388,409],[2,45,53,165,304,379,38,404],[84,378,353,379,393,214,184,253],[212,397,67,15,272,175,308,168],[364,109,347,317,193,64,25,14],[220,49,345,68,272,89,246,64],[148,332,259,39,310,200,308,160],[387,173,331,220,359,298,209,253],[236,47,41,163,144,244,245,145]]

set_option maxRecDepth 100000 in
set_option maxHeartbeats 3000000 in
private theorem p11row0 : red (rawTensorRow J1 J1 0) = p11[0]?.getD [] := by decide

set_option maxRecDepth 100000 in
set_option maxHeartbeats 3000000 in
private theorem p11row1 : red (rawTensorRow J1 J1 1) = p11[1]?.getD [] := by decide

set_option maxRecDepth 100000 in
set_option maxHeartbeats 3000000 in
private theorem p11row2 : red (rawTensorRow J1 J1 2) = p11[2]?.getD [] := by decide

set_option maxRecDepth 100000 in
set_option maxHeartbeats 3000000 in
private theorem p11row3 : red (rawTensorRow J1 J1 3) = p11[3]?.getD [] := by decide

set_option maxRecDepth 100000 in
set_option maxHeartbeats 3000000 in
private theorem p11row4 : red (rawTensorRow J1 J1 4) = p11[4]?.getD [] := by decide

set_option maxRecDepth 100000 in
set_option maxHeartbeats 3000000 in
private theorem p11row5 : red (rawTensorRow J1 J1 5) = p11[5]?.getD [] := by decide

set_option maxRecDepth 100000 in
set_option maxHeartbeats 3000000 in
private theorem p11row6 : red (rawTensorRow J1 J1 6) = p11[6]?.getD [] := by decide

set_option maxRecDepth 100000 in
set_option maxHeartbeats 3000000 in
private theorem p11row7 : red (rawTensorRow J1 J1 7) = p11[7]?.getD [] := by decide

set_option maxRecDepth 100000 in
set_option maxHeartbeats 3000000 in
private theorem p11row8 : red (rawTensorRow J1 J1 8) = p11[8]?.getD [] := by decide

set_option maxRecDepth 100000 in
set_option maxHeartbeats 3000000 in
private theorem p11row9 : red (rawTensorRow J1 J1 9) = p11[9]?.getD [] := by decide

set_option maxRecDepth 100000 in
set_option maxHeartbeats 3000000 in
private theorem p11row10 : red (rawTensorRow J1 J1 10) = p11[10]?.getD [] := by decide

set_option maxRecDepth 100000 in
set_option maxHeartbeats 3000000 in
private theorem p11row11 : red (rawTensorRow J1 J1 11) = p11[11]?.getD [] := by decide

set_option maxRecDepth 100000 in
set_option maxHeartbeats 3000000 in
private theorem p11row12 : red (rawTensorRow J1 J1 12) = p11[12]?.getD [] := by decide

set_option maxRecDepth 100000 in
set_option maxHeartbeats 3000000 in
private theorem p11row13 : red (rawTensorRow J1 J1 13) = p11[13]?.getD [] := by decide

set_option maxRecDepth 100000 in
set_option maxHeartbeats 3000000 in
private theorem p11row14 : red (rawTensorRow J1 J1 14) = p11[14]?.getD [] := by decide

private theorem p11_exact : rawRows J1 J1 = p11 := by
  unfold rawRows
  have er : List.range 15 = [0,1,2,3,4,5,6,7,8,9,10,11,12,13,14] := by decide
  rw [er]
  simp only [List.map_cons,List.map_nil,p11row0, p11row1, p11row2, p11row3, p11row4, p11row5, p11row6, p11row7, p11row8, p11row9, p11row10, p11row11, p11row12, p11row13, p11row14] <;> rfl
def pw : Tensor := [[245,400,241,349,10,358,283,94],[164,358,179,369,132,396,361,142],[309,31,390,89,250,53,263,129],[262,205,391,281,166,381,287,135],[407,116,24,290,351,221,51,133],[149,404,324,36,193,328,316,10],[274,201,300,404,382,405,169,324],[408,312,298,34,35,370,203,115],[379,47,347,371,313,33,391,22],[220,49,115,251,37,54,261,32],[298,97,93,412,416,229,257,141],[344,403,346,285,128,18,136,242],[91,191,203,315,66,1,126,321],[145,171,205,242,136,306,288,152],[79,219,123,160,298,355,24,325]]

set_option maxRecDepth 100000 in
set_option maxHeartbeats 3000000 in
private theorem pwrow0 : red (rawTensorRow knownMinor unitWitness 0) = pw[0]?.getD [] := by decide

set_option maxRecDepth 100000 in
set_option maxHeartbeats 3000000 in
private theorem pwrow1 : red (rawTensorRow knownMinor unitWitness 1) = pw[1]?.getD [] := by decide

set_option maxRecDepth 100000 in
set_option maxHeartbeats 3000000 in
private theorem pwrow2 : red (rawTensorRow knownMinor unitWitness 2) = pw[2]?.getD [] := by decide

set_option maxRecDepth 100000 in
set_option maxHeartbeats 3000000 in
private theorem pwrow3 : red (rawTensorRow knownMinor unitWitness 3) = pw[3]?.getD [] := by decide

set_option maxRecDepth 100000 in
set_option maxHeartbeats 3000000 in
private theorem pwrow4 : red (rawTensorRow knownMinor unitWitness 4) = pw[4]?.getD [] := by decide

set_option maxRecDepth 100000 in
set_option maxHeartbeats 3000000 in
private theorem pwrow5 : red (rawTensorRow knownMinor unitWitness 5) = pw[5]?.getD [] := by decide

set_option maxRecDepth 100000 in
set_option maxHeartbeats 3000000 in
private theorem pwrow6 : red (rawTensorRow knownMinor unitWitness 6) = pw[6]?.getD [] := by decide

set_option maxRecDepth 100000 in
set_option maxHeartbeats 3000000 in
private theorem pwrow7 : red (rawTensorRow knownMinor unitWitness 7) = pw[7]?.getD [] := by decide

set_option maxRecDepth 100000 in
set_option maxHeartbeats 3000000 in
private theorem pwrow8 : red (rawTensorRow knownMinor unitWitness 8) = pw[8]?.getD [] := by decide

set_option maxRecDepth 100000 in
set_option maxHeartbeats 3000000 in
private theorem pwrow9 : red (rawTensorRow knownMinor unitWitness 9) = pw[9]?.getD [] := by decide

set_option maxRecDepth 100000 in
set_option maxHeartbeats 3000000 in
private theorem pwrow10 : red (rawTensorRow knownMinor unitWitness 10) = pw[10]?.getD [] := by decide

set_option maxRecDepth 100000 in
set_option maxHeartbeats 3000000 in
private theorem pwrow11 : red (rawTensorRow knownMinor unitWitness 11) = pw[11]?.getD [] := by decide

set_option maxRecDepth 100000 in
set_option maxHeartbeats 3000000 in
private theorem pwrow12 : red (rawTensorRow knownMinor unitWitness 12) = pw[12]?.getD [] := by decide

set_option maxRecDepth 100000 in
set_option maxHeartbeats 3000000 in
private theorem pwrow13 : red (rawTensorRow knownMinor unitWitness 13) = pw[13]?.getD [] := by decide

set_option maxRecDepth 100000 in
set_option maxHeartbeats 3000000 in
private theorem pwrow14 : red (rawTensorRow knownMinor unitWitness 14) = pw[14]?.getD [] := by decide

private theorem pw_exact : rawRows knownMinor unitWitness = pw := by
  unfold rawRows
  have er : List.range 15 = [0,1,2,3,4,5,6,7,8,9,10,11,12,13,14] := by decide
  rw [er]
  simp only [List.map_cons,List.map_nil,pwrow0, pwrow1, pwrow2, pwrow3, pwrow4, pwrow5, pwrow6, pwrow7, pwrow8, pwrow9, pwrow10, pwrow11, pwrow12, pwrow13, pwrow14] <;> rfl

def minorFast (i : Nat) : Bool :=
  minus (reduceARow p02 i) (reduceARow p11 i) == knownMinor[i]?.getD []

def unitFast (i : Nat) : Bool :=
  reduceARow pw i == if i=0 then [1] else []

set_option maxRecDepth 100000 in
set_option maxHeartbeats 5000000 in
private theorem minorFast_checked : n8.all minorFast = true := by decide
set_option maxRecDepth 100000 in
set_option maxHeartbeats 5000000 in
private theorem unitFast_checked : n8.all unitFast = true := by decide

theorem minor_exact : n8.all (minorCheck (J 0) (J 1) (J 2)) = true := by
  rw [J0_exact,J1_exact,J2_exact]
  simpa [minorCheck,minorRow,mulRow,p02_exact,p11_exact,minorFast] using minorFast_checked

theorem minor_unit : n8.all witnessCheck = true := by
  simpa [witnessCheck,mulRow,pw_exact,unitFast] using unitFast_checked

end RKResearch.Certified.Graded.ConstantSharedZeroScalar
