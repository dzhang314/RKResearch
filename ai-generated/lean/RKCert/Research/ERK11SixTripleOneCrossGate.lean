import Lean

/-!
Exact interval checks of the literal seventh-row primitive in the
remaining one-cross, zero-mass active triple chart.
-/
namespace RKResearch.ERK11SixTripleOneCrossGate
set_option maxRecDepth 30000
set_option maxHeartbeats 0

structure Interval where
  lo : Int
  hi : Int

def step : Int := 10^54
def i36 (a b : Int) : Interval := ⟨a*10^18,b*10^18⟩
def i28 (a b : Int) : Interval := ⟨a*10^26,b*10^26⟩
def exact (a : Int) : Interval := ⟨a*step,a*step⟩
def point (n : Int) : Interval := ⟨n,n⟩

instance (n : Nat) : OfNat Interval n := ⟨exact (Int.ofNat n)⟩
instance : Add Interval := ⟨fun a b => ⟨a.lo+b.lo,a.hi+b.hi⟩⟩
instance : Neg Interval := ⟨fun a => ⟨-a.hi,-a.lo⟩⟩
instance : Sub Interval := ⟨fun a b => ⟨a.lo-b.hi,a.hi-b.lo⟩⟩
instance : Mul Interval := ⟨fun a b =>
  let p := a.lo*b.lo
  let q := a.lo*b.hi
  let r := a.hi*b.lo
  let s := a.hi*b.hi
  let lo := min (min p q) (min r s)
  let hi := max (max p q) (max r s)
  ⟨lo/step, -((-hi)/step)⟩⟩

def ipow (a : Interval) : Nat → Interval
  | 0 => 1
  | n+1 => a*ipow a n
instance : Pow Interval Nat := ⟨ipow⟩

def half (a : Interval) : Interval := ⟨a.lo/2, -((-a.hi)/2)⟩
def nonzero (a : Interval) : Bool := decide (a.hi < 0 ∨ 0 < a.lo)
def disjoint (a b : Interval) : Bool := decide (a.hi < b.lo ∨ b.hi < a.lo)
def distinct : List Interval → Bool
  | [] => true
  | a::as => as.all (disjoint a) && distinct as

def changesSign (f : Interval → Interval) (iv : Interval) : Bool :=
  let outL := f (point iv.lo)
  let outR := f (point iv.hi)
  decide (iv.lo < iv.hi ∧
    ((outL.hi<0 ∧ 0<outR.lo) ∨ (outR.hi<0 ∧ 0<outL.lo)))

def ieval (a : List Int) (x : Interval) : Interval :=
  a.foldr (fun v t => exact v+x*t) 0

def a4 : List Int := [1,-14,56,-84,42]
def a5 : List Int := [-1,20,-120,300,-330,132]
def aDoubling : List Int := [24,-384,2632,-9720,20973,-27090,20496,-8316,1386]
def aOneApart : List Int := [1,0,-104,0,1212,0,-3528,0,2772]
def r4 (x : Interval) : Interval := ieval a4 x
def r5 (x : Interval) : Interval := ieval a5 x

def oneBoxes : List (Interval × List Interval) :=
  [(i36 (464580794119247766319416004501535920) (464580794119247766319416004501535923), [i28 (935996548372533895316401231) (935996548372533895316401234), i28 (2895377408148397472501096144) (2895377408148397472501096147), i28 (9312506304991908493097403937) (9312506304991908493097403940)]),
   (i36 (903978085956574561398684019503244945) (903978085956574561398684019503244948), [i28 (2968189062022800943464459851) (2968189062022800943464459854), i28 (7829053541457852714975577446) (7829053541457852714975577449), i28 (9417023252590716443204327136) (9417023252590716443204327139)]),
   (i36 (1212896452538046007881735191552867656) (1212896452538046007881735191552867659), [i28 (1406816962137713486161926214) (1406816962137713486161926217), i28 (6705981152082508988815883422) (6705981152082508988815883425), i28 (8933151128423491088314842714) (8933151128423491088314842717)]),
   (i36 (1745538115205063357591348261044241577) (1745538115205063357591348261044241580), [i28 (3758428242815018270156526220) (3758428242815018270156526223), i28 (6585683257437836232094181658) (6585683257437836232094181661), i28 (8890379049062145388225204380) (8890379049062145388225204383)])]
def bothBoxes : List (Interval × List Interval) :=
  [(i36 (-873940454099940772167568509706941116) (-873940454099940772167568509706941113), [i28 (3739311249454877164018813921) (3739311249454877164018813924), i28 (6571130591536393001367623561) (6571130591536393001367623564), i28 (8884912478285366073138958559) (8884912478285366073138958562)]),
   (i36 (-621833884439697889819316273071076975) (-621833884439697889819316273071076972), [i28 (1287172262916621755521112849) (1287172262916621755521112852), i28 (6602883042916384606098340176) (6602883042916384606098340179), i28 (8896745423109435877171063326) (8896745423109435877171063329)]),
   (i36 (-333621719446586916323228667240166710) (-333621719446586916323228667240166707), [i28 (1350532369850396541969148146) (1350532369850396541969148149), i28 (3869550944559568086138571601) (3869550944559568086138571604), i28 (8918569672587427540572203540) (8918569672587427540572203543)]),
   (i36 (-104759361829868664145363697894815071) (-104759361829868664145363697894815068), [i28 (1503977580842325134725312552) (1503977580842325134725312555), i28 (4031065726213702958016408111) (4031065726213702958016408114), i28 (6763232858832254151913947674) (6763232858832254151913947677)]),
   (i36 (104759361829868664145363697894815068) (104759361829868664145363697894815071), [i28 (3236767141167745848086052323) (3236767141167745848086052326), i28 (5968934273786297041983591886) (5968934273786297041983591889), i28 (8496022419157674865274687445) (8496022419157674865274687448)]),
   (i36 (333621719446586916323228667240166707) (333621719446586916323228667240166710), [i28 (1081430327412572459427796457) (1081430327412572459427796460), i28 (6130449055440431913861428396) (6130449055440431913861428399), i28 (8649467630149603458030851851) (8649467630149603458030851854)]),
   (i36 (621833884439697889819316273071076972) (621833884439697889819316273071076975), [i28 (1103254576890564122828936671) (1103254576890564122828936674), i28 (3397116957083615393901659821) (3397116957083615393901659824), i28 (8712827737083378244478887148) (8712827737083378244478887151)]),
   (i36 (873940454099940772167568509706941113) (873940454099940772167568509706941116), [i28 (1115087521714633926861041438) (1115087521714633926861041441), i28 (3428869408463606998632376436) (3428869408463606998632376439), i28 (6260688750545122835981186076) (6260688750545122835981186079)])]
def mixedBoxes : List (Interval × List Interval) :=
  [(i36 (131222855298074669318598084020664722) (131222855298074669318598084020664725), [i28 (3818437421921367627515595063) (3818437421921367627515595066), i28 (6629112246509434309622133575) (6629112246509434309622133578), i28 (8906273025093393166548561252) (8906273025093393166548561255)]),
   (i36 (271827578998312478213130048723143121) (271827578998312478213130048723143124), [i28 (5083218168645717189704002183) (5083218168645717189704002186), i28 (7411835439193486603406446496) (7411835439193486603406446499), i28 (9178941300204519469953261033) (9178941300204519469953261036)]),
   (i36 (421666020241385924077166682666253717) (421666020241385924077166682666253720), [i28 (-5163612916770938656276185) (-5163612916770938656276182), i28 (1743982958272757337177770694) (1743982958272757337177770697), i28 (8986220551788852158434291697) (8986220551788852158434291700)]),
   (i36 (477277634142603604785705471690007249) (477277634142603604785705471690007252), [i28 (760717589890047685675698112) (760717589890047685675698115), i28 (2456811287549596994729838414) (2456811287549596994729838417), i28 (7183351258473658543838174306) (7183351258473658543838174309)]),
   (i36 (618072357390167913629313914347298579) (618072357390167913629313914347298582), [i28 (1093516768170248038920322969) (1093516768170248038920322972), i28 (3370302649820750952646329056) (3370302649820750952646329059), i28 (8687176554224176573780238851) (8687176554224176573780238854)]),
   (i36 (877118368539809825928179121729495859) (877118368539809825928179121729495862), [i28 (1132410294360976250130482434) (1132410294360976250130482437), i28 (3473618052090878302084467949) (3473618052090878302084467952), i28 (6316450114599208555252423996) (6316450114599208555252423999)])]

def aMixed : List Int :=
 [353,-8480,84184,-456720,1491162,-3010896,3677184,-2483712,709632]

def floorQ (n d : Int) : Int := if d<0 then (-n)/(-d) else n/d
def quotient (a b : Interval) : Option Interval :=
  if nonzero b then
    let p := floorQ (a.lo*step) b.lo
    let q := floorQ (a.lo*step) b.hi
    let r := floorQ (a.hi*step) b.lo
    let s := floorQ (a.hi*step) b.hi
    -- Each exact endpoint quotient is < (its floor + 1).
    some ⟨min (min p q) (min r s), max (max p q) (max r s)+1⟩
  else none

def getI (a : List Interval) (i : Nat) : Interval := a[i]?.getD 0
def isum (xs : List Interval) : Interval := xs.foldl (·+·) 0
def iprod (xs : List Interval) : Interval := xs.foldl (·*·) 1
def nodesDiff (xs : List Interval) (x : Interval) : Interval :=
  iprod (xs.map (fun y => x-y))

structure Chart where
  xs : List Interval         -- Five supported pair clocks, then the omitted triple.
  ai : Nat
  ni : Nat
  di : Nat
  ei : Nat
  lambda : Interval

def ref (t : Chart) : Chart :=
  ⟨t.xs.map (1-·),t.di,t.ei,t.ai,t.ni,-t.lambda⟩

def choose2 : List Nat → List (Nat × Nat)
  | [] => []
  | x::xs => (xs.map (x,·)) ++ choose2 xs

def lResponse (a x : Interval) (atPlateau : Bool) : Option Interval :=
  if atPlateau then some (half (-(a^2))) else quotient (x^2*(a-x)) a
def rResponse (d x : Interval) (atPlateau : Bool) : Option Interval :=
  if atPlateau then some (half (-((1-d)^2)))
  else quotient ((1-x)^2*(x-d)) (1-d)

def pModel (a x : Interval) : Option Interval :=
  quotient (x^3*(6*x^2-15*a*x+10*a^2)) 30

def basisAt (data : List Interval) (is : List Nat) (i : Nat) (x : Interval) :
    Option Interval :=
  let cs := (is.filter (· != i)).map (getI data)
  quotient (nodesDiff cs x) (nodesDiff cs (getI data i))

/-- The first-left seventh-row primitive test with its actual three interpolation nodes. -/
def rowTest (t : Chart) (lhs : List Interval) (h : Nat → Interval)
    (z x : Nat) : Option Bool := do
  let a := getI t.xs t.ai
  let vx := getI t.xs x
  let pa ← pModel a a
  let px ← pModel a vx
  let is := [t.ni,t.ai,z]
  let terms ← is.mapM (fun i => do
    let pi ← pModel a (getI t.xs i)
    let fit ← quotient (-(pi+h i*pa)) (getI lhs i)
    let w ← basisAt t.xs is i vx
    return w*fit)
  return nonzero (px + getI lhs x * isum terms + h x*pa)

def oneCrossArithmetic (t : Chart) (left : List Nat)
    (cross z x : Nat) : Option Bool := do
  let a := getI t.xs t.ai
  let d := getI t.xs t.di
  let p := getI t.xs 5
  let pair := t.xs.take 5
  let ids := List.range 5
  let hp := ids.map (fun i => nodesDiff (pair.eraseIdx i) (getI pair i))
  let d6p := nodesDiff pair p
  let d6 := ids.map (fun i => (getI pair i-p)*getI hp i)
  let w ← ids.mapM (fun i =>
    let y := getI pair i
    quotient (-1) (13860*y*(y-1)*getI hp i*r4 y))
  let w1 ← quotient (7*t.lambda+5) (210*(t.lambda+1))
  let LF ← (List.range 6).mapM (fun i =>
    lResponse a (getI t.xs i) (i==t.ai))
  let RG ← (List.range 6).mapM (fun i =>
    rResponse d (getI t.xs i) (i==t.di))
  let c0 := -(getI w cross * getI d6 cross * getI LF cross * getI RG cross)
  -- The pair sums are linear in the one unknown first normalization.
  let ab ← ids.mapM (fun i => do
    let wi := getI w i*getI d6 i
    if left.contains i then
      let u := getI LF i
      let s ← quotient (-1) (wi*u)
      return (u,s)
    else
      let g := getI RG i
      let c ← quotient (-c0) (wi*g)
      let s ← quotient g c0
      return (c,s))
  let residues ← ab.zipIdx.mapM (fun ((c,s),i) => do
    let u ← quotient c (getI hp i)
    let v ← quotient s (getI hp i)
    return (u,v))
  let k ← quotient (-(isum (residues.map Prod.fst))) (isum (residues.map Prod.snd))
  let u3terms ← ab.zipIdx.mapM (fun ((c,s),i) => do
    let l ← quotient (nodesDiff (pair.eraseIdx i) p) (getI hp i)
    return (c+s*k)*l)
  let u3 := isum u3terms
  let fl := getI LF 5
  let fr ← quotient (getI RG 5*k) c0
  let fx := u3-fl-fr
  let mu ← quotient k d6p
  let hPair ← ids.mapM (fun i => quotient 1
    ((getI pair i-1)*getI d6 i*getI w i))
  let h1 ← quotient 1 (w1*nodesDiff t.xs 1)
  let outsideNorm := isum (ids.map (fun i => getI w i * (getI hPair i)^2)) + w1*h1^2
  let gamma ← quotient 1 (k*(p-1))
  let sig2 := fl*fr+fl*fx+fr*fx
  let alpha ← quotient (gamma^2*sig2*mu-outsideNorm) (2*gamma*mu)
  let hBase := fun i =>
    if i==5 then alpha+gamma*((getI LF i)^2-u3*getI LF i) else getI hPair i
  let u ←
    if t.ai==5 then quotient (-1) (alpha-gamma*fl*fx)
    else quotient (-1) (getI hPair t.ai)
  let hh := fun i => u*hBase i
  let test1 ← rowTest t LF hh z x
  let test2 ← rowTest t LF hh x z
  if t.ai==5 then
    let hNull := fun i => if i==5 then (-1:Interval) else 0
    let test3 ← rowTest t LF hNull z x
    let test4 ← rowTest t LF hNull x z
    return test1 && test2 && test3 && test4
  else return test1 && test2

def validTopology (left right : List Nat) : Bool :=
  (List.range 6).all (fun i => decide (left.count i+right.count i ≤ 2+(if i==5 then 1 else 0)))

def checkChart (t : Chart) : Bool :=
  distinct (0::1::t.xs) &&
  (choose2 ((List.range 6).filter (fun i => i != t.ai && i != t.ni))).all (fun (z,x) =>
    (choose2 ((List.range 6).filter (fun i => i != t.di && i != t.ei))).all (fun (u,y) =>
      let L := [t.ai,t.ai,t.ni,z,x]
      let R := [t.di,t.di,t.ei,u,y]
      if validTopology L R then
        match (List.range 5).filter (fun i => L.contains i && R.contains i) with
        | [c] => (oneCrossArithmetic t L c z x).getD false
        | _ => true
      else true))

def rootCheck (known extra : List Interval) (f : Interval → Interval) : Bool :=
    (extra.length==3) && distinct (known++extra) && extra.all (changesSign f)

def checkOne (bd : Interval × List Interval) : Bool := ((do
  let (b,xs) := bd
  let d := 1-b
  let e := 1-half b
  let h := d::e::xs
  let l ← quotient (r5 b) (r4 b)
  let halfs := [2,3,4].map (fun i => Chart.mk (h++[half (getI h i)]) i 5 0 1 l)
  let plats := [1,2,3,4].map (fun i => Chart.mk (h++[2*getI h i]) 5 i 0 1 l)
  let ts := halfs++plats
  return (changesSign (ieval aDoubling) b &&
    rootCheck [d,e] xs (fun y => r4 b*r5 y + r5 b*r4 y) &&
    (ts++ts.map ref).all checkChart : Bool)) : Option Bool).getD false

def checkBoth (bd : Interval × List Interval) : Bool := ((do
  let (u,xs) := bd
  let a := 1+u
  let d := u
  let l ← quotient (-(r5 a)) (r4 a)
  let c := Chart.mk (a::d::xs++[half a]) 0 5 1 5 l
  return (changesSign (ieval aOneApart) u &&
    rootCheck [a,d] xs (fun y => r4 a*r5 y-r5 a*r4 y) && checkChart c : Bool)) : Option Bool).getD false

def checkMixed (bd : Interval × List Interval) : Bool := ((do
  let (x,xs) := bd
  let a := 2*x
  let d := 4*x-1
  let l ← quotient (-(r5 x)) (r4 x)
  let c := Chart.mk (x::d::xs++[a]) 5 0 1 5 l
  return (changesSign (ieval aMixed) x &&
    rootCheck [x,d] xs (fun y => r4 x*r5 y-r5 x*r4 y) &&
    checkChart c && checkChart (ref c) : Bool)) : Option Bool).getD false

def countTopology (t : Chart) : Nat :=
  ((choose2 ((List.range 6).filter (fun i => i != t.ai && i != t.ni))).foldl
    (fun n (z,x) => n +
      (choose2 ((List.range 6).filter (fun i => i != t.di && i != t.ei))).foldl
        (fun m (u,y) =>
          let L := [t.ai,t.ai,t.ni,z,x]
          let R := [t.di,t.di,t.ei,u,y]
          if validTopology L R &&
             ((List.range 5).filter (fun i => L.contains i && R.contains i)).length==1
          then m+1 else m) 0) 0)
def shapeOne : List Chart :=
  [2,3,4].map (fun i => ⟨[],i,5,0,1,0⟩) ++
  [1,2,3,4].map (fun i => ⟨[],5,i,0,1,0⟩)
def shapeBoth : Chart := ⟨[],0,5,1,5,0⟩
def shapeMix : Chart := ⟨[],5,0,1,5,0⟩
def shapeAll : List Chart :=
  (List.replicate 4 (shapeOne++shapeOne.map ref)).flatten ++
    List.replicate 8 shapeBoth ++ (List.replicate 6 [shapeMix,ref shapeMix]).flatten

theorem chronologyCounts :
    shapeAll.foldl (fun n t => n+countTopology t) 0 = 396 ∧
    shapeAll.foldl (fun n t => n+(if t.ai==5 then 4 else 2)*countTopology t) 0 = 1044 := by decide

theorem distinctParams :
    oneBoxes.length=4 ∧ bothBoxes.length=8 ∧ mixedBoxes.length=6 ∧
    distinct (oneBoxes.map Prod.fst)=true ∧ distinct (bothBoxes.map Prod.fst)=true ∧
    distinct (mixedBoxes.map Prod.fst)=true := by decide

def getBox (l : List (Interval × List Interval)) (i : Nat) : Interval × List Interval :=
  l[i]?.getD (0,[])

def xMean (a : List Int) : Int :=
  a.zipIdx.foldl (fun z (v,i) => z+v*((27720:Int)/Int.ofNat (i+2))) 0
def jacobiNorm : Int :=
  a4.zipIdx.foldl (fun z (u,i) => z+a4.zipIdx.foldl
    (fun w (v,j) => w+u*v*((27720:Int)/(Int.ofNat (i+j+2)*Int.ofNat (i+j+3)))) 0) 0

theorem scalarWeightConstants : xMean a4 = 924 ∧ xMean a5 = 660 ∧ jacobiNorm=84 := by decide

theorem one0 : checkOne (getBox oneBoxes 0)=true := by decide +kernel
theorem one1 : checkOne (getBox oneBoxes 1)=true := by decide +kernel
theorem one2 : checkOne (getBox oneBoxes 2)=true := by decide +kernel
theorem one3 : checkOne (getBox oneBoxes 3)=true := by decide +kernel
theorem both0 : checkBoth (getBox bothBoxes 0)=true := by decide +kernel
theorem both1 : checkBoth (getBox bothBoxes 1)=true := by decide +kernel
theorem both2 : checkBoth (getBox bothBoxes 2)=true := by decide +kernel
theorem both3 : checkBoth (getBox bothBoxes 3)=true := by decide +kernel
theorem both4 : checkBoth (getBox bothBoxes 4)=true := by decide +kernel
theorem both5 : checkBoth (getBox bothBoxes 5)=true := by decide +kernel
theorem both6 : checkBoth (getBox bothBoxes 6)=true := by decide +kernel
theorem both7 : checkBoth (getBox bothBoxes 7)=true := by decide +kernel
theorem mix0 : checkMixed (getBox mixedBoxes 0)=true := by decide +kernel
theorem mix1 : checkMixed (getBox mixedBoxes 1)=true := by decide +kernel
theorem mix2 : checkMixed (getBox mixedBoxes 2)=true := by decide +kernel
theorem mix3 : checkMixed (getBox mixedBoxes 3)=true := by decide +kernel
theorem mix4 : checkMixed (getBox mixedBoxes 4)=true := by decide +kernel
theorem mix5 : checkMixed (getBox mixedBoxes 5)=true := by decide +kernel

end RKResearch.ERK11SixTripleOneCrossGate
#print axioms RKResearch.ERK11SixTripleOneCrossGate.distinctParams
#print axioms RKResearch.ERK11SixTripleOneCrossGate.chronologyCounts
#print axioms RKResearch.ERK11SixTripleOneCrossGate.scalarWeightConstants
#print axioms RKResearch.ERK11SixTripleOneCrossGate.one0
#print axioms RKResearch.ERK11SixTripleOneCrossGate.one1
#print axioms RKResearch.ERK11SixTripleOneCrossGate.one2
#print axioms RKResearch.ERK11SixTripleOneCrossGate.one3
#print axioms RKResearch.ERK11SixTripleOneCrossGate.both0
#print axioms RKResearch.ERK11SixTripleOneCrossGate.both1
#print axioms RKResearch.ERK11SixTripleOneCrossGate.both2
#print axioms RKResearch.ERK11SixTripleOneCrossGate.both3
#print axioms RKResearch.ERK11SixTripleOneCrossGate.both4
#print axioms RKResearch.ERK11SixTripleOneCrossGate.both5
#print axioms RKResearch.ERK11SixTripleOneCrossGate.both6
#print axioms RKResearch.ERK11SixTripleOneCrossGate.both7
#print axioms RKResearch.ERK11SixTripleOneCrossGate.mix0
#print axioms RKResearch.ERK11SixTripleOneCrossGate.mix1
#print axioms RKResearch.ERK11SixTripleOneCrossGate.mix2
#print axioms RKResearch.ERK11SixTripleOneCrossGate.mix3
#print axioms RKResearch.ERK11SixTripleOneCrossGate.mix4
#print axioms RKResearch.ERK11SixTripleOneCrossGate.mix5
