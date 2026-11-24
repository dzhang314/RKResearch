module
public import RKCert.ERKOrderNineH48Stages
@[expose] public section
namespace RKCert.GoodPrimeDense

def partK2x2 : Box exactTower.atV :=
  let u : Box exactTower.atV := ⟨exactTower.u⟩
  let v : Box exactTower.atV := ⟨exactTower.v⟩
  (504*u*v^3 - 945*u*v^2 + 540*u*v - 81*u - 504*v^3 + 945*v^2 - 549*v + 90)

def partK2x2Value : L3 (List ℚ) := [[[[-3, -270, 432], [-42, (609/2), 252], [-63, 567, -504], [63, -504]], [[-39, 747, -504], [399, -252], [504, -504], [-504]], [[63, -504], [-504]]], [[[-3, 315, -504], [63, -504]], [[57, -819, 504], [-567, 504]], [[-63, 504], [504]]]]

set_option maxRecDepth 6000 in
set_option maxHeartbeats 0 in
theorem partK2x2_check : partK2x2.value = partK2x2Value := by decide +kernel

def partK2x1 : Box exactTower.atV :=
  let u : Box exactTower.atV := ⟨exactTower.u⟩
  let v : Box exactTower.atV := ⟨exactTower.v⟩
  (-756*u^2*v^3 + 1512*u^2*v^2 - 972*u^2*v + 192*u^2 + 504*u*v^3 - 1107*u*v^2 + 816*u*v - 201*u + 252*v^3 - 393*v^2 + 150*v + 3)

def partK2x1Value : L3 (List ℚ) := [[[[-16, (2862/7), -702], [90, (-2277/2), 1008], [87, 1161, -504], [-99, -504]], [[171, -1137, 738], [-1287, 2268, -1134], [1260, -2016, 756], [-504, 756]], [[-171, 738], [1260, -1134], [-1512, 756], [756]]], [[[18, -435, 738], [-111, 1260, -1134], [0, -1512, 756], [0, 756]], [[-165, 1107, -630], [1359, -2142, 756], [-1512, 1512], [756]], [[135, -630], [-1008, 756], [756]]]]

set_option maxRecDepth 6000 in
set_option maxHeartbeats 0 in
theorem partK2x1_check : partK2x1.value = partK2x1Value := by decide +kernel

def partK2x0 : Box exactTower.atV :=
  let u : Box exactTower.atV := ⟨exactTower.u⟩
  let v : Box exactTower.atV := ⟨exactTower.v⟩
  (756*u^2*v^3 - 1512*u^2*v^2 + 984*u^2*v - 204*u^2 - 1008*u*v^3 + 2037*u*v^2 - 1350*u*v + 291*u + 252*v^3 - 537*v^2 + 381*v - 90)

def partK2x0Value : L3 (List ℚ) := [[[[7, -126, 270], [-38, (1683/2), -1260], [-9, -1743, 1008], [21, 1008]], [[-93, 375, -234], [873, -2016, 1134], [-1764, 2520, -756], [1008, -756]], [[81, -234], [-756, 1134], [1512, -756], [-756]]], [[[-3, 105, -234], [33, -756, 1134], [0, 1512, -756], [0, -756]], [[69, -273, 126], [-777, 1638, -756], [1512, -1512], [-756]], [[-45, 126], [504, -756], [-756]]]]

set_option maxRecDepth 6000 in
set_option maxHeartbeats 0 in
theorem partK2x0_check : partK2x0.value = partK2x0Value := by decide +kernel

def kPart2Value : L3 (List ℚ) := [[[[(-125/7), (843/14), (-909/14)], [(55/2), (-147/2), (99/4)], [-3, (183/2), (-279/2)], [-3, (-279/2)]], [[(137/2), (-357/2), 126], [-180, 432, (-693/2)], [363, -1071, 693], [-378, 693]], [[-63, 126], [258, (-693/2)], [-693, 693], [693]]], [[[25, (-1263/14), 108], [-53, (483/2), -252], [54, -537, 504], [-33, 504]], [[-96, 252, -180], [306, -798, 630], [-756, 2016, -1260], [756, -1260]], [[90, -180], [-420, 630], [1260, -1260], [-1260]]]]

def computedKPart2 : Box exactTower.atV := ⟨partK2x2Value⟩ * exactR^2 + ⟨partK2x1Value⟩ * exactR + ⟨partK2x0Value⟩

set_option maxRecDepth 6000 in
set_option maxHeartbeats 0 in
theorem computedKPart2_check : computedKPart2.value = kPart2Value := by decide +kernel

theorem kPart2_check : (rawCoeff2 exactR ⟨exactTower.u⟩ ⟨exactTower.v⟩).value = kPart2Value := by
  change exactTower.atV.add (exactTower.atV.add (exactTower.atV.mul partK2x2.value (pow exactTower.atV exactR.value 2)) (exactTower.atV.mul partK2x1.value exactR.value)) (partK2x0.value) = _
  rw [partK2x2_check,partK2x1_check,partK2x0_check]
  exact computedKPart2_check

end RKCert.GoodPrimeDense
