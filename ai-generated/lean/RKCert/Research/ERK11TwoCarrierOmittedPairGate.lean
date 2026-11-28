import Lean

/-!
Exact interval certificates for all 48 Jacobi clock charts in the
two-carrier omitted half-plateau branch. Intervals are integer endpoints
on a fixed rational grid, and multiplication rounds outwards.
-/
namespace RKResearch.ERK11TwoCarrierOmittedPairGate
set_option maxRecDepth 30000
set_option maxHeartbeats 0

structure Interval where
  lo : Int
  hi : Int

def step : Int := 10^36
def i24 (a b : Int) : Interval := ⟨a*10^12,b*10^12⟩
def i16 (a b : Int) : Interval := ⟨a*10^20,b*10^20⟩
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
  [(i24 (464580794119247766319415) (464580794119247766319418), [i16 (935996548372532) (935996548372535), i16 (2895377408148396) (2895377408148399), i16 (9312506304991907) (9312506304991910)]),
   (i24 (903978085956574561398683) (903978085956574561398686), [i16 (2968189062022799) (2968189062022802), i16 (7829053541457851) (7829053541457854), i16 (9417023252590715) (9417023252590718)]),
   (i24 (1212896452538046007881734) (1212896452538046007881737), [i16 (1406816962137712) (1406816962137715), i16 (6705981152082507) (6705981152082510), i16 (8933151128423490) (8933151128423493)]),
   (i24 (1745538115205063357591347) (1745538115205063357591350), [i16 (3758428242815017) (3758428242815020), i16 (6585683257437835) (6585683257437838), i16 (8890379049062144) (8890379049062147)])]
def bothBoxes : List (Interval × List Interval) :=
  [(i24 (-873940454099940772167570) (-873940454099940772167567), [i16 (3739311249454876) (3739311249454879), i16 (6571130591536392) (6571130591536395), i16 (8884912478285365) (8884912478285368)]),
   (i24 (-621833884439697889819318) (-621833884439697889819315), [i16 (1287172262916620) (1287172262916623), i16 (6602883042916383) (6602883042916386), i16 (8896745423109434) (8896745423109437)]),
   (i24 (-333621719446586916323230) (-333621719446586916323227), [i16 (1350532369850395) (1350532369850398), i16 (3869550944559567) (3869550944559570), i16 (8918569672587426) (8918569672587429)]),
   (i24 (-104759361829868664145365) (-104759361829868664145362), [i16 (1503977580842324) (1503977580842327), i16 (4031065726213701) (4031065726213704), i16 (6763232858832253) (6763232858832256)]),
   (i24 (104759361829868664145362) (104759361829868664145365), [i16 (3236767141167744) (3236767141167747), i16 (5968934273786296) (5968934273786299), i16 (8496022419157673) (8496022419157676)]),
   (i24 (333621719446586916323227) (333621719446586916323230), [i16 (1081430327412571) (1081430327412574), i16 (6130449055440430) (6130449055440433), i16 (8649467630149602) (8649467630149605)]),
   (i24 (621833884439697889819315) (621833884439697889819318), [i16 (1103254576890563) (1103254576890566), i16 (3397116957083614) (3397116957083617), i16 (8712827737083377) (8712827737083380)]),
   (i24 (873940454099940772167567) (873940454099940772167570), [i16 (1115087521714632) (1115087521714635), i16 (3428869408463605) (3428869408463608), i16 (6260688750545121) (6260688750545124)])]

def checkParamRoots (coef : List Int) (xs : List (Interval × List Interval)) : Bool :=
  distinct (xs.map Prod.fst) && xs.all (fun (i,_) => changesSign (ieval coef) i)

theorem parameterEnclosures :
    oneBoxes.length=4 ∧ bothBoxes.length=8 ∧
    checkParamRoots aDoubling oneBoxes=true ∧ checkParamRoots aOneApart bothBoxes=true := by decide

def p0quad (a w : Interval) : Interval := 6*w^2-15*a*w+10*a^2

/-- Numerator for the physically dormant eighth-row gate.
The remaining denominators are all products of distinct sites. -/
def leftGate (a d p w1 w2 w : Interval) : Interval :=
  let den := (1-a)*(a-d)*(p-w1)*(p-w2)
  let coeff := -a*den + a*(1-p)*(p-d)*(a-w1)*(a-w2)
  (a-p)*a^5*r4 w*den + coeff*(w-p)*w^2*p0quad a w*r4 a

/-- Reflected physically dormant tenth-row gate. -/
def rightGate (a d p w1 w2 w : Interval) : Interval :=
  let den := d*(a-d)*(p-w1)*(p-w2)
  let coeff := -(d-1)*den + p*(a-p)*(d-1)*(d-w1)*(d-w2)
  (d-p)*(1-d)^5*r4 w*den -
      coeff*(w-p)*(1-w)^2*p0quad (1-d) (1-w)*r4 d

def exclude (a d t w1 w2 : Interval) : Bool :=
  let p := half a
  distinct [0,1,a,d,t,p,w1,w2] &&
  [w1,w2].all (fun w =>
    nonzero (leftGate a d p w1 w2 w) && nonzero (rightGate a d p w1 w2 w))

def checkOne (b : Interval) (extra : List Interval) : Bool :=
  let d := 1-b
  let e := 1-half b
  let f := fun x => r4 b*r5 x+r5 b*r4 x
  (extra.length==3) && nonzero (r4 b) && distinct (d::e::extra) &&
  extra.all (changesSign f) &&
  extra.zipIdx.all (fun (x,i) =>
    match extra.eraseIdx i with
    | [w1,w2] => exclude x d e w1 w2 && exclude e d x w1 w2
    | _ => false)

def checkBoth (u : Interval) (extra : List Interval) : Bool :=
  let a := 1+u
  let d := u
  let f := fun x => r4 a*r5 x-r5 a*r4 x
  (extra.length==3) && nonzero (r4 a) && distinct (d::a::extra) &&
  extra.all (changesSign f) &&
  extra.zipIdx.all (fun (t,i) =>
    match extra.eraseIdx i with
    | [w1,w2] => exclude a d t w1 w2
    | _ => false)

theorem oneOmitted : oneBoxes.all (fun (b,xs) => checkOne b xs) = true := by decide
theorem bothOmitted : bothBoxes.all (fun (u,xs) => checkBoth u xs) = true := by decide

/-! A short exact signed remainder count gives the four real roots of the
doubling polynomial. The one-apart degree-eight polynomial already has
a checked sign change in eight disjoint boxes. -/
def term (a : List Int) (i : Nat) : Int := a[i]?.getD 0
def trim (a : List Int) : List Int := (a.reverse.dropWhile (· == 0)).reverse
def top (a : List Int) : Int := a.getLast?.getD 0
def content (a : List Int) : Nat := a.foldl (fun c i => Nat.gcd c i.natAbs) 0
def prim (a : List Int) : List Int :=
  let a := trim a
  let d := content a
  if d ≤ 1 then a else a.map (fun i => i / Int.ofNat d)
def addPoly (a b : List Int) : List Int :=
  (List.range (max a.length b.length)).map (fun i => term a i+term b i)
def scalePoly (r : Int) (a : List Int) : List Int := a.map (r * ·)
def premLoop (b : List Int) : Nat → List Int → List Int
  | 0, a => a
  | n+1, a =>
    if a.isEmpty || a.length < b.length then a
    else
      let q := top b
      let s := Int.sign q
      let sub := List.replicate (a.length-b.length) 0 ++ scalePoly (-(s*top a)) b
      premLoop b n (prim (addPoly (scalePoly (Int.ofNat q.natAbs) a) sub))
def prem (a b : List Int) : List Int :=
  if b.isEmpty then a else premLoop b a.length a

def derivative (a : List Int) : List Int :=
  a.tail.zipIdx.map (fun (v,i) => v*Int.ofNat (i+1))
def sturm : Nat → List Int → List Int → List (Nat × Int)
  | 0, _, _ => []
  | n+1, a, b =>
    if a.isEmpty then []
    else ((a.length-1), Int.sign (top a)) :: sturm n b (scalePoly (-1) (prem a b))

def doublingSigns : List (Nat × Int) :=
  [(8,1),(7,1),(6,1),(5,1),(4,1),(3,-1),(2,-1),(1,-1),(0,1)]

theorem doublingSturm :
    sturm 9 aDoubling (derivative aDoubling) = doublingSigns := by decide

def variations : List Int → Nat
  | [] => 0
  | a::as => ((as.zip (a::as)).filter (fun (x,y) => x != y)).length

theorem doublingCount :
    variations (doublingSigns.map (fun (d,s) => if d%2==1 then -s else s))=6 ∧
    variations (doublingSigns.map Prod.snd)=2 := by decide

end RKResearch.ERK11TwoCarrierOmittedPairGate
#print axioms RKResearch.ERK11TwoCarrierOmittedPairGate.parameterEnclosures
#print axioms RKResearch.ERK11TwoCarrierOmittedPairGate.doublingSturm
#print axioms RKResearch.ERK11TwoCarrierOmittedPairGate.doublingCount
#print axioms RKResearch.ERK11TwoCarrierOmittedPairGate.oneOmitted
#print axioms RKResearch.ERK11TwoCarrierOmittedPairGate.bothOmitted
