module
public import RKCert.ERKOrderNineH48Stages
@[expose] public section
namespace RKCert.GoodPrimeDense

def partK0x3 : Box exactTower.atV :=
  let u : Box exactTower.atV := ⟨exactTower.u⟩
  let v : Box exactTower.atV := ⟨exactTower.v⟩
  (756*u^2*v^3 - 1260*u^2*v^2 + 576*u^2*v - 36*u^2 - 756*u*v^3 + 1224*u*v^2 - 522*u*v + 18*u + 18*v^2 - 36*v + 18)

def partK0x3Value : L3 (List ℚ) := [[[[72, (-2493/7), 486], [-348, 1422, -1134], [558, -1800, 756], [-288, 756]], [[-264, 828, -486], [1326, -2520, 1134], [-2016, 2520, -756], [1008, -756]], [[198, -486], [-1008, 1134], [1512, -756], [-756]]], [[[-66, 342, -486], [318, -1386, 1134], [-504, 1764, -756], [252, -756]], [[228, -720, 378], [-1224, 2142, -756], [1764, -1512], [-756]], [[-144, 378], [756, -756], [-756]]]]

set_option maxRecDepth 6000 in
set_option maxHeartbeats 0 in
theorem partK0x3_check : partK0x3.value = partK0x3Value := by decide +kernel

def partK0x2 : Box exactTower.atV :=
  let u : Box exactTower.atV := ⟨exactTower.u⟩
  let v : Box exactTower.atV := ⟨exactTower.v⟩
  (-1008*u^3*v^3 + 1680*u^3*v^2 - 768*u^3*v + 48*u^3 + 546*u^2*v^3 - 900*u^2*v^2 + 390*u^2*v - 12*u^2 + 510*u*v^3 - 834*u*v^2 + 378*u*v - 30*u - 24*v^3 + 42*v^2 - 12*v - 6)

def partK0x2Value : L3 (List ℚ) := [[[[(-839/7), (3477/7), (-4203/7)], [572, -2033, 1641], [-918, 2694, -1158], [474, -1158]], [[413, (-7948/7), 525], [-2042, 3613, -1449], [3252, -3594, 966], [-1662, 966]], [[-288, 657], [1440, -1701], [-2268, 1134], [1134]]], [[[101, (-2953/7), 525], [-482, 1768, -1449], [768, -2316, 966], [-384, 966]], [[-324, 847, -291], [1734, -2859, 966], [-2652, 2100], [1134]], [[180, -423], [-990, 1134], [1134]]]]

set_option maxRecDepth 6000 in
set_option maxHeartbeats 0 in
theorem partK0x2_check : partK0x2.value = partK0x2Value := by decide +kernel

def partK0x1 : Box exactTower.atV :=
  let u : Box exactTower.atV := ⟨exactTower.u⟩
  let v : Box exactTower.atV := ⟨exactTower.v⟩
  (1008*u^3*v^3 - 1632*u^3*v^2 + 696*u^3*v - 24*u^3 - 1362*u^2*v^3 + 2208*u^2*v^2 - 930*u^2*v + 24*u^2 + 318*u*v^3 - 516*u*v^2 + 204*u*v + 6*u + 12*v^3 - 30*v^2 + 24*v - 6)

def partK0x1Value : L3 (List ℚ) := [[[[(319/7), (-874/7), (603/7)], [-220, 542, -411], [366, -768, 330], [-192, 330]], [[(-899/7), (1772/7), (-87/7)], [590, -845, 225], [-984, 810, -150], [510, -150]], [[72, (-963/7)], [-324, 405], [540, -270], [-270]]], [[[(-227/7), (449/7), (-87/7)], [158, -314, 225], [-264, 432, -150], [132, -150]], [[74, (-575/7), -105], [-396, 507, -150], [672, -420], [-270]], [[-18, 27], [162, -270], [-270]]]]

set_option maxRecDepth 6000 in
set_option maxHeartbeats 0 in
theorem partK0x1_check : partK0x1.value = partK0x1Value := by decide +kernel

def partK0x0 : Box exactTower.atV :=
  let u : Box exactTower.atV := ⟨exactTower.u⟩
  let v : Box exactTower.atV := ⟨exactTower.v⟩
  (-24*u^3*v^2 + 48*u^3*v - 24*u^3 + 30*u^2*v^3 - 36*u^2*v^2 - 18*u^2*v + 24*u^2 - 42*u*v^3 + 90*u*v^2 - 54*u*v + 6*u + 12*v^3 - 30*v^2 + 24*v - 6)

def partK0x0Value : L3 (List ℚ) := [[[[-5, (53/7), 9], [28, -7, -51], [-54, -42, 42], [30, 42]], [[(33/7), (-26/7), (-51/7)], [22, -91, 45], [-96, 126, -30], [66, -30]], [[0, (9/7)], [-36, 81], [108, -54], [-54]]], [[[(33/7), (-53/7), (-51/7)], [-26, 8, 45], [48, 36, -30], [-24, -30]], [[-4, (53/7), 3], [-18, 75, -30], [84, -84], [-54]], [[0, -9], [18, -54], [-54]]]]

set_option maxRecDepth 6000 in
set_option maxHeartbeats 0 in
theorem partK0x0_check : partK0x0.value = partK0x0Value := by decide +kernel

def kPart0Value : L3 (List ℚ) := [[[[(-305/21), (891/14), (-3774/49)], [(1397/21), (-1606/7), (1170/7)], [(-709/7), (1958/7), (-876/7)], [50, (-876/7)]], [[(1138/21), -169, 108], [(-5392/21), 522, -270], [410, -628, 252], [-232, 252]], [[(-318/7), 108], [228, -270], [-396, 252], [252]]], [[[(397/21), (-167/2), (720/7)], [(-259/3), 315, -252], [131, -424, 216], [-64, 216]], [[(-496/7), (1542/7), (-990/7)], [336, -690, 360], [-552, 864, -360], [324, -360]], [[60, (-990/7)], [-300, 360], [540, -360], [-360]]]]

def computedKPart0 : Box exactTower.atV := ⟨partK0x3Value⟩ * exactR^3 + ⟨partK0x2Value⟩ * exactR^2 + ⟨partK0x1Value⟩ * exactR + ⟨partK0x0Value⟩

set_option maxRecDepth 6000 in
set_option maxHeartbeats 0 in
theorem computedKPart0_check : computedKPart0.value = kPart0Value := by decide +kernel

theorem kPart0_check : (rawCoeff0 exactR ⟨exactTower.u⟩ ⟨exactTower.v⟩).value = kPart0Value := by
  change exactTower.atV.add (exactTower.atV.add (exactTower.atV.add (exactTower.atV.mul partK0x3.value (pow exactTower.atV exactR.value 3)) (exactTower.atV.mul partK0x2.value (pow exactTower.atV exactR.value 2))) (exactTower.atV.mul partK0x1.value exactR.value)) (partK0x0.value) = _
  rw [partK0x3_check,partK0x2_check,partK0x1_check,partK0x0_check]
  exact computedKPart0_check

end RKCert.GoodPrimeDense
