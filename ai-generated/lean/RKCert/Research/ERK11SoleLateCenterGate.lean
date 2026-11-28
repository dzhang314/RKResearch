import Lean

/-!
Arithmetic certificates for the real three-carrier, two-new-boundary chart.
The polynomials F and E use symmetric plateau sum and product. Degree-bounded
interpolations bind them to the exact moment formula and the exact Bezout
determinant/cofactors. The final dyadic Bernstein certificate checks the discriminant sign
on all possible real determinant roots, without floating point.
-/
namespace RKResearch.ERK11SoleLateCenterGate
set_option maxRecDepth 30000
set_option maxHeartbeats 0

def fa : List (List Int) :=
  [[720,-11160,74280,-267960,548460,-598950,272250],
  [18840,-273180,1557600,-4409460,6152850,-3403125],
  [285676,-3264426,14061960,-26264865,18186300],
  [2324718,-20576655,57303180,-52598700],
  [11751960,-63445140,86248800],
  [28041750,-75467700],
  [27442800]]
def fb : List (List Int) :=
  [[60,-1290,10150,-39760,83160,-87780,36300],
  [6790,-88795,462560,-1182720,1450020,-671550],
  [133220,-1368240,5161200,-8179380,4537500],
  [1221480,-9274980,21484320,-15246000],
  [6106298,-27110160,27442800],
  [13167000,-25155900],
  [9147600]]
def detScale : Int := 433933237584000000
def coScale : Int := 21696661879200000
def detFactor : List Int := [-3983465452255650459885941093103304472576,161810414362458154356396987187628858831296,-3158087972256294857716088452988412713263424,39427203935408321568253946092277616940260240,-353668412975902767149883421677821799042796416,2427443259062992063823418167130796382030297172,-13257007013319471804092221658660698280858813244,59148328604571819240899479496820411389375169051,-219669663107442980351039287034051358477518939724,688472872049009382248362844095182344256080839812,-1839673122551266985886332207114446423349383886880,4223487474227442186984140134191205601690105955054,-8378479151817496823089565191913786507817267935256,14421896829673613295443364619960299429902465012460,-21600483245901399312940123261543962806240096889360,28196645601982279668657853686884415153373801429800,-32096562403285287119719259012701966410805000494600,31843258679600107855019195609692833871769989384500,-27489657183681051106145851520718141718945657401000,20591835549466949016396167962136396267452800315000,-13328873939101735034197456634968302159069655935000,7412624114919926721098122453669125656347704825000,-3514630860416788533560831161390086300572963250000,1406212416701225146574006463382254075760117500000,-468275671502846049277217934442633216613681250000,127370064212956726850540338206750502331062500000,-27557947114383022969548517386557036790937500000,4560298770255126054699738351174307832812500000,-541893847556546953301349288667471500000000000,41157811132051000946577796598674218750000000,-1500467895160254991006264433583984375000000]
def pivot0 : List Int := [-90671813813250189896614496886945453056,2235437200726848772237637574778459115696,-20922373930126725566589767889336846532768,49363001716662941881377871157593152720840,854421664845149735116607614470491811934824,-11186332315738056658415388423943187934377397,74497509787760431038380374261078296934036548,-340817255885928803617648512563609603353351572,1170956737155558307779232349942605080969931680,-3150871975947808602493632918359593468148570400,6800360545643437452084625498399915825986411600,-11944862537015415669930676999532090673627651900,17229531627197733154287174161719076207387226000,-20510776125897103602414071262361647924314319000,20188247734723881735858595974007632664139865000,-16412054355906351070251862475107130236754812500,10975991469266826808090615910619158469087375000,-5994826620100748044605542236217564076271875000,2643759203751211618618531652002032978496875000,-925638735182067820665501840877610992781250000,250936861520472907715954517782954694375000000,-50697448798231658631967945463958630468750000,7170694801784863637366740637181937500000000,-632063138551588126226665927748671875000000,26059281354686457857917809641601562500000]
def pivot1 : List Int := [-7032355553974033595590622260311224832,363814401313487387293110323072014694304,-8124361209746187137114018395610392448800,108325429729366503268478216388213254833168,-985913304414549715549799725436779838968656,6583179787887653420696266717086467357017938,-33706978677970627271874549674016764295162426,136259057854215362502291538136114804615028480,-443725485294461557301695100958311622350402856,1180672957541224139879286612673811022191698080,-2592734988008558362923290754716870101328332920,4731309375929946862523318311177963358659235400,-7205809336357069018279029241167856813328221800,9179066062481052572549193548222293728690432000,-9781008248912391665751206344058846497716534000,8701786196601051419505303876994346697442365000,-6437015464119703425529420761927856150857675000,3932858090894833406356219244185356671716500000,-1965115239555204998762212501252240655295000000,791757889682068224685634947769879895656250000,-252109621413563434214340215275087559062500000,61617430164037933081068853825185989062500000,-11059843935802362329955683391789923437500000,1356717774758368410170453290547812500000000,-99565009038409490684094307264453125000000,3168026562744098732292891064453125000000]

def term (a : List Int) (i : Nat) : Int := a[i]?.getD 0
def eval (a : List Int) (x : Int) : Int := a.foldr (fun v r => v+x*r) 0
def evalPair (f : List (List Int)) (s p : Int) : Int :=
  f.foldr (fun r v => eval r s+p*v) 0

def add (a b : List Int) : List Int :=
  (List.range (max a.length b.length)).map (fun i => term a i + term b i)
def scale (r : Int) (a : List Int) : List Int := a.map (r * ·)
def neg (a : List Int) : List Int := scale (-1) a
def product (a b : List Int) : List Int :=
  (List.range (a.length+b.length-1)).map (fun k =>
    (List.range (k+1)).foldl (fun s i => s+term a i*term b (k-i)) 0)

def anchoredKernelRows : List (List Int) :=
  [[3,-32,108,-144,66],
   [-32,388,-1404,1956,-924],
   [108,-1404,5316,-7644,3696],
   [-144,1956,-7644,11256,-5544],
   [66,-924,3696,-5544,2772]]

def common : Int := 27720

def integrate (a : List Int) : Int :=
  a.zipIdx.foldl (fun s (v,i) => s+v*(common / Int.ofNat (i+1))) 0
def primitiveAt0 (a : List Int) : List Int :=
  0::(a.zipIdx.map (fun (v,i) => v*(common / Int.ofNat (i+1))))
def primitiveAt1 (a : List Int) : List Int :=
  integrate a :: (primitiveAt0 a).tail.map (- ·)

def leftQuartic (a : Int) : List Int := [0,0,a^2,-2*a,1]
def rightQuartic (b : Int) : List Int :=
    product [1,-2,1] [(1-b)^2,-2*(1-b),1]

def checkMomentSample (a b : Int) : Bool :=
  let x := leftQuartic a
  let y := rightQuartic b
  let px := primitiveAt0 x
  let qy := primitiveAt1 y
  let h := integrate (product px y)
  let c := integrate (0::product x qy)
  let k := integrate (0::product px y)
  let d := product x y
  let f := integrate (0::0::d)*h^2 - integrate (0::d)*h*(c+k) + integrate d*c*k
  let kernel := evalPair anchoredKernelRows (1-b) a
  let e := 900*(210*kernel) * integrate (product px qy) -
    (a^4*b^4)*common^3
  -- f is scaled by common^5; e is scaled by 900 * common^3.
  decide (evalPair fa (a+b) (a*b)*common^5 = 871363785600000*f ∧
          evalPair fb (a+b) (a*b)*900*common^3 = 19800*e)

theorem momentInterpolation : ∀ a b : Fin 7,
    checkMomentSample (Int.ofNat a.val) (Int.ofNat b.val) = true := by decide

def bezout (s : Int) (i j : Nat) : Int :=
  let a := fun k => eval (fa[k]?.getD []) s
  let b := fun k => eval (fb[k]?.getD []) s
  (List.range (min i j+1)).foldl (fun p k =>
    let h := i+j+1-k
    if h < 7 then p + (a h * b k - a k * b h) else p) 0

def bezoutMatrix (s : Int) : List (List Int) :=
  (List.range 6).map (fun i => (List.range 6).map (bezout s i))

/-- Fraction-free signed Schur elimination, with every division verified exact. -/
def determinant : Nat → List (List Int) → Int → Option Int
  | 0, _, _ => some 1
  | 1, mat, _ => some (term (mat.headD []) 0)
  | n+2, mat, prev =>
    match mat.zipIdx.find? (fun (r,_) => term r 0 != 0) with
    | none => some 0
    | some (pivot,i) =>
      let p := term pivot 0
      let new := (mat.eraseIdx i).map (fun row =>
        List.zipWith (fun x y => p*x-term row 0*y) row.tail pivot.tail)
      if prev == 0 || !(new.all (fun row => row.all (fun a => a % prev == 0)))
      then none
      else ((determinant (n+1) (new.map (fun row => row.map (· / prev))) p).map
        (fun val => if i%2==0 then val else -val))

def det (n : Nat) (mat : List (List Int)) : Option Int := determinant n mat 1

def quadratic : List Int := [6,-33,55]

def checkBezoutSample (s : Int) : Bool :=
  let mat := bezoutMatrix s
  let lower := mat.tail
  decide (det 6 mat = some (detScale*(eval quadratic s)^2*eval detFactor s) ∧
          det 5 (lower.map (fun row => row.eraseIdx 0)) = some (coScale*eval pivot0 s) ∧
          det 5 (lower.map (fun row => row.eraseIdx 1)) = some (-(coScale*eval pivot1 s)))

theorem bezoutInterpolation : ∀ s : Fin 37,
    checkBezoutSample (Int.ofNat s.val) = true := by decide

def trim (a : List Int) : List Int := (a.reverse.dropWhile (· == 0)).reverse

def fac : Nat → Nat
  | 0 => 1
  | n+1 => (n+1)*fac n

/-- Bernstein coefficients on [0,2], cleared by n!. -/
def bern (a : List Int) : List Int :=
  let n := a.length-1
  (List.range a.length).map (fun j =>
    (List.range (j+1)).foldl (fun s i =>
      s + (Int.ofNat ((2^i*fac j*fac (n-i))/fac (j-i)))*term a i) 0)

def deCasteljau : Nat → List Int → List Int → List Int → List Int × List Int
  | 0, _, l, r => (l.reverse,r)
  | n+1, a, l, r =>
    let b := 2^n
    deCasteljau n (List.zipWith (·+·) a a.tail)
      (b*(a.headD 0)::l) (b*a.getLast?.getD 0::r)

def split (a : List Int) : List Int × List Int := deCasteljau a.length a [] []

def detPos : List Int := neg detFactor
def discrim : List Int := product pivot0
  (add ([0,0] ++ pivot0) (scale (-4) pivot1))

def plusTwo (a : List Int) : List Int :=
  trim (a.foldr (fun c p => add [c] (add (scale 2 p) (0::p))) [])

theorem outsideSigns :
    ((detPos.zipIdx.map (fun (c,i) => if i%2==0 then c else -c)).all
      (fun v => decide (v>0))) = true ∧
    ((plusTwo detPos).all (fun v => decide (v>0))) = true := by decide

inductive Certificate where
  | determinant
  | discriminant
  | branch (l r : Certificate)

def region : Certificate :=
  .branch
    (.branch .determinant (.branch .discriminant (.branch .discriminant .determinant)))
    (.branch
      (.branch .determinant (.branch .discriminant .determinant))
      (.branch
        (.branch
          .discriminant
          (.branch
            .determinant
            (.branch
              .determinant
              (.branch (.branch .determinant .discriminant) .determinant))))
        .determinant))

def certify : Certificate → List Int → List Int → Bool
  | .determinant, f, _ => (f.all (fun v => decide (v>0))) ||
      (f.all (fun v => decide (v<0)))
  | .discriminant, _, q => q.all (fun v => decide (v<0))
  | .branch l r, f, q =>
    let (f0,f1) := split f
    let (q0,q1) := split q
    certify l f0 q0 && certify r f1 q1

theorem bernsteinSignCertificate : certify region (bern detPos) (bern discrim)=true := by decide

end RKResearch.ERK11SoleLateCenterGate
#print axioms RKResearch.ERK11SoleLateCenterGate.momentInterpolation
#print axioms RKResearch.ERK11SoleLateCenterGate.bezoutInterpolation
#print axioms RKResearch.ERK11SoleLateCenterGate.outsideSigns
#print axioms RKResearch.ERK11SoleLateCenterGate.bernsteinSignCertificate
