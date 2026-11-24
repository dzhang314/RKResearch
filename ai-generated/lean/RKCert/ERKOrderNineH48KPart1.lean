module
public import RKCert.ERKOrderNineH48Stages
@[expose] public section
namespace RKCert.GoodPrimeDense

def partK1x3 : Box exactTower.atV :=
  let u : Box exactTower.atV := ⟨exactTower.u⟩
  let v : Box exactTower.atV := ⟨exactTower.v⟩
  (-168*u^2*v^2 + 336*u^2*v - 168*u^2 - 504*u*v^3 + 1092*u*v^2 - 888*u*v + 276*u + 504*v^3 - 924*v^2 + 564*v - 120)

def partK1x3Value : L3 (List ℚ) := [[[[-104, 396, -432], [280, -546, -252], [-252, -420, 504], [84, 504]], [[332, -876, 504], [-644, 504], [-168, 336], [336]], [[-252, 504], [504]]], [[[116, -444, 504], [-308, 756], [336, -168], [-168]], [[-356, 924, -504], [756, -672], [-168]], [[252, -504], [-504]]]]

set_option maxRecDepth 6000 in
set_option maxHeartbeats 0 in
theorem partK1x3_check : partK1x3.value = partK1x3Value := by decide +kernel

def partK1x2 : Box exactTower.atV :=
  let u : Box exactTower.atV := ⟨exactTower.u⟩
  let v : Box exactTower.atV := ⟨exactTower.v⟩
  (224*u^3*v^2 - 448*u^3*v + 224*u^3 + 224*u^2*v^3 - 588*u^2*v^2 + 576*u^2*v - 204*u^2 - 28*u*v^3 + 72*u*v^2 + 16*u*v - 52*u - 196*v^3 + 288*v^2 - 148*v + 40)

def partK1x2Value : L3 (List ℚ) := [[[[182, (-9080/21), 312], [(-1456/3), (2536/3), -238], [520, -460, 28], [-208, 28]], [[-516, (2456/3), -340], [(2384/3), (-2240/3), 336], [-196, 336, -224], [-112, -224]], [[348, -420], [-420]]], [[[-192, (1376/3), -340], [(1544/3), (-2870/3), 336], [-616, 756, -224], [308, -224]], [[(1576/3), (-2444/3), 308], [-828, 728, -224], [308, -224]], [[-336, 420], [420]]]]

set_option maxRecDepth 6000 in
set_option maxHeartbeats 0 in
theorem partK1x2_check : partK1x2.value = partK1x2Value := by decide +kernel

def partK1x1 : Box exactTower.atV :=
  let u : Box exactTower.atV := ⟨exactTower.u⟩
  let v : Box exactTower.atV := ⟨exactTower.v⟩
  (672*u^3*v^3 - 1456*u^3*v^2 + 1184*u^3*v - 368*u^3 - 952*u^2*v^3 + 2004*u^2*v^2 - 1608*u^2*v + 508*u^2 + 524*u*v^3 - 1008*u*v^2 + 684*u*v - 176*u - 260*v^3 + 484*v^2 - 272*v + 40)

def partK1x1Value : L3 (List ℚ) := [[[[(-482/7), -34, (1812/7)], [(616/3), (136/3), -74], [-348, 156, -92], [184, -92]], [[(284/3), (5924/21), -248], [(1300/3), (-2660/3), 84], [-836, 584, -56], [472, -56]], [[-24, -216], [-564, 756], [1008, -504], [-504]]], [[[(224/3), (416/21), -248], [(-692/3), (-14/3), 84], [376, -76, -56], [-188, -56]], [[-112, (-608/3), 176], [-372, 772, -56], [820, -560], [-504]], [[48, 96], [348, -504], [-504]]]]

set_option maxRecDepth 6000 in
set_option maxHeartbeats 0 in
theorem partK1x1_check : partK1x1.value = partK1x1Value := by decide +kernel

def partK1x0 : Box exactTower.atV :=
  let u : Box exactTower.atV := ⟨exactTower.u⟩
  let v : Box exactTower.atV := ⟨exactTower.v⟩
  (-672*u^3*v^3 + 1232*u^3*v^2 - 752*u^3*v + 160*u^3 + 728*u^2*v^3 - 1244*u^2*v^2 + 704*u^2*v - 148*u^2 + 28*u*v^3 - 184*u*v^2 + 200*u*v - 52*u - 68*v^3 + 176*v^2 - 148*v + 40)

def partK1x0Value : L3 (List ℚ) := [[[[(22/3), (740/21), (-852/7)], [(-112/3), (-928/3), 574], [104, 740, -460], [-64, -460]], [[(112/3), (-3256/21), 64], [(-1552/3), (3292/3), -420], [1196, -1272, 280], [-712, 280]], [[-36, 96], [444, -756], [-1008, 504], [504]]], [[[(-44/3), (92/21), 64], [(200/3), (466/3), -420], [-136, -492, 280], [68, 280]], [[(-16/3), (64/3), 40], [372, -788, 280], [-940, 784], [504]], [[0, 24], [-228, 504], [504]]]]

set_option maxRecDepth 6000 in
set_option maxHeartbeats 0 in
theorem partK1x0_check : partK1x0.value = partK1x0Value := by decide +kernel

def kPart1Value : L3 (List ℚ) := [[[[(266/9), (-2263/21), (801/7)], [(-4696/63), 170, -17], [54, (-136/3), 38], [(-28/3), 38]], [[(-6640/63), (1998/7), (-1290/7)], [(2462/9), (-1442/3), 282], [-304, (2300/3), -492], [(716/3), -492]], [[90, (-1290/7)], [-296, 282], [528, -492], [-492]]], [[[(-2482/63), (1038/7), -168], [(944/9), (-1004/3), 216], [-92, (1232/3), -336], [(80/3), -336]], [[140, (-2620/7), 240], [(-1136/3), 704, -420], [536, -1304, 840], [-464, 840]], [[-120, 240], [400, -420], [-840, 840], [840]]]]

def computedKPart1 : Box exactTower.atV := ⟨partK1x3Value⟩ * exactR^3 + ⟨partK1x2Value⟩ * exactR^2 + ⟨partK1x1Value⟩ * exactR + ⟨partK1x0Value⟩

set_option maxRecDepth 6000 in
set_option maxHeartbeats 0 in
theorem computedKPart1_check : computedKPart1.value = kPart1Value := by decide +kernel

theorem kPart1_check : (rawCoeff1 exactR ⟨exactTower.u⟩ ⟨exactTower.v⟩).value = kPart1Value := by
  change exactTower.atV.add (exactTower.atV.add (exactTower.atV.add (exactTower.atV.mul partK1x3.value (pow exactTower.atV exactR.value 3)) (exactTower.atV.mul partK1x2.value (pow exactTower.atV exactR.value 2))) (exactTower.atV.mul partK1x1.value exactR.value)) (partK1x0.value) = _
  rw [partK1x3_check,partK1x2_check,partK1x1_check,partK1x0_check]
  exact computedKPart1_check

end RKCert.GoodPrimeDense
