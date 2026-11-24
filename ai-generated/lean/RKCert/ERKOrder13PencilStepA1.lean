module
public import RKCert.ERKOrder13PencilData

@[expose] public section
namespace RKCert.Paired.FiniteMidpoint.Pencil13
open RKCert.DenseCommonRoot

set_option maxHeartbeats 0
set_option maxRecDepth 500000
set_option maxSynthPendingDepth 10000

open RKCert.GoodPrimeDense
def A1 : Bi := [[210,-5250,58450,-364700,1414840,-3601620,6138660,-6945840,5004120,-2076360,377520],[0,0,1925,-38885,256993,-794750,1308120,-1186680,566280,-113256],[0,0,-1925,38533,-239360,650760,-853050,519090,-113256],[0,0,715,-14300,85800,-214500,235950,-94380]]
private def A1L : List ℤ := [165636900,-6625476000,106007616000,-894439260000,4482134514000,-14155992021600,28900326312000,-38043483192000,31156300890000,-14430286728000,2886057345600]
private def A1Q : Bi := [[0,-3680820,147232800,-2355724800,19876428000,-99602989200,314577600480,-642229473600,845410737600,-692362242000,320673038400,-64134607680],[5521230,-220849200,3533587200,-29814642000,149404483800,-471866400720,963344210400,-1268116106400,1038543363000,-481009557600,96201911520]]
private theorem A1_checked : checkStep omitted firstMoment A1 A1Q A1L
    (unitDigits anchor 5521230 2 0) := by
  decide +kernel

theorem propagateA1 {K:Type*} [Field K] [CharZero K] (u v:K) (un:u≠0)
    (an:GoodPrimeDense.read (Int.castRingHom K) u anchor≠0)
    (f:GoodPrimeDense.read (GoodPrimeDense.read (Int.castRingHom K) u) v omitted=0)
    (g:GoodPrimeDense.read (GoodPrimeDense.read (Int.castRingHom K) u) v firstMoment=0) :
    GoodPrimeDense.read (GoodPrimeDense.read (Int.castRingHom K) u) v A1=0 := by
  apply propagate u v A1_checked f g
  have n := unitDigits_ne u anchor (c:=5521230) (by decide) 2 0 un an
  exact n

end RKCert.Paired.FiniteMidpoint.Pencil13
