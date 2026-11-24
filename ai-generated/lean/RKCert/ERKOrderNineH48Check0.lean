module

public import RKCert.ERKOrderNineH48KPart0
public import RKCert.ERKOrderNineH48KPart1
public import RKCert.ERKOrderNineH48KPart2

@[expose] public section
namespace RKCert.GoodPrimeDense

def mergedK2 : L3 (List ℚ) := [[[[(3/14), (15/4), (-369/28)], [(-41/14), (-1473/28), (1521/14)], [(-48/7), (1737/7), -252], [(27/2), -252]], [[(131/14), (-312/7), (99/2)], [-122, (3081/7), -396], [(933/2), -1218, 720], [-462, 720]], [[(-33/2), (99/2)], [(429/2), -396], [-756, 720], [720]]], [[[(2/7), (-90/7), 36], [(-45/14), (2259/14), -288], [30, -591, 540], [-33, 540]], [[-18, 84, -90], [234, -822, 720], [-852, 2160, -1260], [810, -1260]], [[30, -90], [-390, 720], [1350, -1260], [-1260]]]]
def mergedK1 : L3 (List ℚ) := [[[[(2/9), (-11/7), (19/7)], [(238/9), (-1871/21), 90], [(-1304/21), (316/3), 40], [(106/3), 40]], [[(-358/63), (604/21), (-246/7)], [(-1628/63), -32, 132], [(-134/3), (1600/3), -456], [(520/3), -456]], [[(82/7), (-246/7)], [-74, 132], [360, -456], [-456]]], [[[(-40/63), (208/21), -24], [(-1922/63), (134/7), 48], [(208/3), (460/3), -288], [(-116/3), -288]], [[(232/21), (-372/7), 60], [(-44/3), 204, -300], [240, -1112, 840], [-392, 840]], [[-20, 60], [160, -300], [-720, 840], [840]]]]

set_option maxRecDepth 6000 in
set_option maxHeartbeats 0 in
theorem mergedK2_check : exactTower.atV.mul kPart2Value (pow exactTower.atV exactTower.h 2)=mergedK2 := by decide +kernel

set_option maxRecDepth 6000 in
set_option maxHeartbeats 0 in
theorem mergedK1_check : exactTower.atV.mul kPart1Value exactTower.h=mergedK1 := by decide +kernel

set_option maxRecDepth 6000 in
set_option maxHeartbeats 0 in
theorem mergedK_check :
    exactTower.atV.add (exactTower.atV.add mergedK2 mergedK1) kPart0Value=h48Stage0 := by decide +kernel

theorem h48_check0 :
    k8Recipe exactTower.atV exactTower.h exactR.value exactTower.u exactTower.v = h48Stage0 := by
  change exactTower.atV.add
    (exactTower.atV.add
      (exactTower.atV.mul (rawCoeff2 exactR ⟨exactTower.u⟩ ⟨exactTower.v⟩).value
        (pow exactTower.atV exactTower.h 2))
      (exactTower.atV.mul (rawCoeff1 exactR ⟨exactTower.u⟩ ⟨exactTower.v⟩).value exactTower.h))
    (rawCoeff0 exactR ⟨exactTower.u⟩ ⟨exactTower.v⟩).value = h48Stage0
  rw [kPart2_check,kPart1_check,kPart0_check,mergedK2_check,mergedK1_check]
  exact mergedK_check

end RKCert.GoodPrimeDense
