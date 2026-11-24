module
public import RKCert.ERKOrder13PencilStepA1

@[expose] public section
namespace RKCert.Paired.FiniteMidpoint.Pencil13
open RKCert.DenseCommonRoot

set_option maxHeartbeats 0
set_option maxRecDepth 500000
set_option maxSynthPendingDepth 10000

open RKCert.GoodPrimeDense
def A2 : Bi := [[0,-1120,26250,-276150,1670025,-6395655,16218015,-27623970,31256280,-22518540,9343620,-1698840],[2100,-52500,593250,-3829350,15499995,-41093481,72421800,-84027240,61636410,-25907310,4756752],[0,0,0,0,429,-8580,51480,-128700,141570,-56628]]
private def A2L : List ℤ := [0,0,0,0,511225,-20449000,327184000,-2760615000,13833748500,-43691333400,89198538000,-117418158000,96161422500,-44537922000,8907584400]
private def A2Q : Bi := [[0,0,0,4907760,-196310400,3140966400,-26501904000,132803985600,-419436800640,856305964800,-1127214316800,923149656000,-427564051200,85512810240],[0,0,-9202050,368082000,-5889312000,49691070000,-249007473000,786444001200,-1605573684000,2113526844000,-1730905605000,801682596000,-160336519200]]
private theorem A2_checked : checkStep firstMoment A1 A2 A2Q A2L
    (unitDigits anchor 920205 2 2) := by
  decide +kernel

theorem propagateA2 {K:Type*} [Field K] [CharZero K] (u v:K) (un:u≠0)
    (an:GoodPrimeDense.read (Int.castRingHom K) u anchor≠0)
    (f:GoodPrimeDense.read (GoodPrimeDense.read (Int.castRingHom K) u) v firstMoment=0)
    (g:GoodPrimeDense.read (GoodPrimeDense.read (Int.castRingHom K) u) v A1=0) :
    GoodPrimeDense.read (GoodPrimeDense.read (Int.castRingHom K) u) v A2=0 := by
  apply propagate u v A2_checked f g
  have n := unitDigits_ne u anchor (c:=920205) (by decide) 2 2 un an
  exact n

end RKCert.Paired.FiniteMidpoint.Pencil13
