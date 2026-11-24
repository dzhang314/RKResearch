module

public import RKCert.ERKOrderNineH48Check0
public import RKCert.ERKOrderNineH48Check1
public import RKCert.ERKOrderNineH48Check2
public import RKCert.ERKOrderNineH48Check3

@[expose] public section

namespace RKCert.GoodPrimeDense

theorem h48_raw_check : h48RawCoeffs = h48ExpectedCoeffs := by
  change norm exactTower.ops 4 exactTower.relH
    (norm exactTower.atH 3 exactTower.relU
      (norm exactTower.atU 2 exactTower.relV
        (k8Recipe exactTower.atV exactTower.h exactR.value exactTower.u exactTower.v))) = _
  rw [h48_check0,h48_check1,h48_check2,h48_check3]

end RKCert.GoodPrimeDense
